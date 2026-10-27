defmodule Astraea.Session.Ltb do
  @moduledoc """
  CASC Large Theory Batch (LTB) Specification Parser & Session Runner.

  Implements the standard CASC LTB competition protocol:
  - Ingests batch configuration, shared `BatchIncludes`, and `BatchProblems` lists.
  - Spawns an `Astraea.Session` with the shared theory.
  - Sequentially runs problems with warm theory reuse and sound lemma accumulation.
  - Emits TSTP / SZS status outputs to designated result paths.
  """

  alias Astraea.Session

  @type batch_config :: %{
          category: String.t() | nil,
          order: :ordered | :unordered,
          timeout_problem: non_neg_integer(),
          timeout_overall: non_neg_integer(),
          includes: [String.t()],
          problems: [{String.t(), String.t()}]
        }

  @doc """
  Parses a CASC LTB batch specification file into a `%{} `config struct.
  """
  @spec parse_spec(Path.t()) :: {:ok, batch_config()} | {:error, term()}
  def parse_spec(spec_path) do
    case File.read(spec_path) do
      {:ok, content} ->
        lines = String.split(content, ~r/\r?\n/)
        config = do_parse(lines, :global, default_config())
        {:ok, config}

      {:error, reason} ->
        {:error, reason}
    end
  end

  @doc """
  Runs an entire LTB batch using a warm `Astraea.Session`.
  """
  @spec run_batch(Path.t(), keyword()) :: {:ok, map()} | {:error, term()}
  def run_batch(spec_path, opts \\ []) do
    with {:ok, config} <- parse_spec(spec_path) do
      base_dir = Path.dirname(spec_path)
      timeout_ms = Keyword.get(opts, :timeout_ms, config.timeout_problem * 1000)

      # 1. Start Session
      {:ok, session} = Session.start_link(opts)

      # 2. Build theory includes from BatchIncludes
      includes_content = Enum.join(config.includes, "\n")
      {:ok, init_info} = Session.init_theory(session, {:string, includes_content}, opts)

      # 3. Process Problems
      t0 = System.monotonic_time(:millisecond)

      results =
        for {prob_rel, out_rel} <- config.problems do
          prob_path = resolve_path(base_dir, prob_rel)
          out_path = if out_rel != "", do: resolve_path(base_dir, out_rel), else: nil

          case Session.prove(session, {:file, prob_path}, timeout_ms: timeout_ms) do
            {:ok, res} ->
              if out_path do
                write_result(out_path, prob_rel, res)
              end
              {prob_rel, res}

            {:error, reason} ->
              {prob_rel, %{szs: :error, reason: reason}}
          end
        end

      dur_ms = System.monotonic_time(:millisecond) - t0
      stats = Session.stats(session)
      Session.stop(session)

      report = %{
        category: config.category,
        total_problems: length(config.problems),
        solved: stats.queries_proved,
        solve_rate_pct: stats.solve_rate_pct,
        elapsed_ms: dur_ms,
        harvested_lemmas: stats.harvested_lemmas_count,
        demod_rules: stats.demod_rules_count,
        background_clauses: init_info.background_clauses,
        results: results
      }

      {:ok, report}
    end
  end

  # ---------------------------------------------------------------------------
  # Parser Helpers
  # ---------------------------------------------------------------------------

  defp default_config do
    %{
      category: nil,
      order: :ordered,
      timeout_problem: 10,
      timeout_overall: 3600,
      includes: [],
      problems: []
    }
  end

  defp do_parse([], _section, acc), do: acc

  defp do_parse([line | rest], section, acc) do
    trimmed = String.trim(line)

    cond do
      trimmed == "" or String.starts_with?(trimmed, "#") ->
        do_parse(rest, section, acc)

      trimmed == "% SZS start BatchConfiguration" ->
        do_parse(rest, :config, acc)

      trimmed == "% SZS end BatchConfiguration" ->
        do_parse(rest, :global, acc)

      trimmed == "% SZS start BatchIncludes" ->
        do_parse(rest, :includes, acc)

      trimmed == "% SZS end BatchIncludes" ->
        do_parse(rest, :global, acc)

      trimmed == "% SZS start BatchProblems" ->
        do_parse(rest, :problems, acc)

      trimmed == "% SZS end BatchProblems" ->
        do_parse(rest, :global, acc)

      section == :config ->
        new_acc =
          cond do
            String.starts_with?(trimmed, "execution.order") ->
              order = if String.contains?(trimmed, "unordered"), do: :unordered, else: :ordered
              %{acc | order: order}

            String.starts_with?(trimmed, "limit.time.problem.wc") ->
              [_, secs] = String.split(trimmed, ~r/\s+/)
              %{acc | timeout_problem: String.to_integer(secs)}

            String.starts_with?(trimmed, "limit.time.overall.wc") ->
              [_, secs] = String.split(trimmed, ~r/\s+/)
              %{acc | timeout_overall: String.to_integer(secs)}

            true ->
              acc
          end

        do_parse(rest, :config, new_acc)

      section == :includes ->
        do_parse(rest, :includes, %{acc | includes: acc.includes ++ [trimmed]})

      section == :problems ->
        parts = String.split(trimmed, ~r/\s+/)
        prob = Enum.at(parts, 0)
        out = Enum.at(parts, 1, "")
        do_parse(rest, :problems, %{acc | problems: acc.problems ++ [{prob, out}]})

      section == :global ->
        new_acc =
          if String.starts_with?(trimmed, "division.category ") do
            [_, cat] = String.split(trimmed, ~r/\s+/, parts: 2)
            %{acc | category: cat}
          else
            acc
          end

        do_parse(rest, :global, new_acc)
    end
  end

  defp resolve_path(base_dir, path) do
    if Path.type(path) == :absolute do
      path
    else
      Path.expand(path, base_dir)
    end
  end

  defp write_result(out_path, prob, res) do
    File.mkdir_p!(Path.dirname(out_path))

    szs_str =
      case Map.get(res, :szs, :unknown) do
        :theorem -> "Theorem"
        :unsatisfiable -> "Unsatisfiable"
        :counter_satisfiable -> "CounterSatisfiable"
        :timeout -> "Timeout"
        other -> Atom.to_string(other)
      end

    content = "% SZS status #{szs_str} for #{prob}\n"
    File.write(out_path, content)
  end
end
