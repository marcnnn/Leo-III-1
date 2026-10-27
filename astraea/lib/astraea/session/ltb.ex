defmodule Astraea.Session.Ltb do
  @moduledoc """
  CASC Large Theory Batch (LTB) Specification Parser & Session Runner.

  Implements the standard CASC LTB competition protocol:
  - Ingests batch configuration, shared `BatchIncludes`, and `BatchProblems` lists.
  - Spawns an `Astraea.Session` with the shared theory.
  - Sequentially runs problems with warm theory reuse and sound lemma accumulation.
  - Emits TSTP / SZS status outputs to designated result paths.
  - Supports resilient checkpointing to disk and live telemetry reporting.
  """

  alias Astraea.{Session, TptpCorpus}

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

  Options:
  - `:timeout_ms`: Per-problem timeout in milliseconds (defaults to spec's `limit.time.problem.wc` * 1000).
  - `:overall_timeout_ms`: Overall batch timeout in milliseconds (defaults to spec's `limit.time.overall.wc` * 1000).
  - `:checkpoint_file`: Path to JSON checkpoint file for persisting state and resuming.
  - `:resume`: Whether to resume from existing checkpoint (default `true`).
  - `:on_result`: Callback invoked after each problem: `fn info -> ... end`.
  - `:competitive`: Whether to race external provers alongside internal strategies (default `false`).
  """
  @spec run_batch(Path.t(), keyword()) :: {:ok, map()} | {:error, term()}
  def run_batch(spec_path, opts \\ []) do
    with {:ok, config} <- parse_spec(spec_path) do
      base_dir = Path.dirname(spec_path)
      timeout_ms = Keyword.get(opts, :timeout_ms, config.timeout_problem * 1000)
      overall_timeout_ms = Keyword.get(opts, :overall_timeout_ms, config.timeout_overall * 1000)
      checkpoint_path = Keyword.get(opts, :checkpoint_file)
      resume? = Keyword.get(opts, :resume, true)
      on_result = Keyword.get(opts, :on_result, fn _ -> :ok end)
      competitive? = Keyword.get(opts, :competitive, false)

      # 1. Load existing checkpoint if available
      {completed_map, _prior_stats} =
        if resume? and is_binary(checkpoint_path) and File.exists?(checkpoint_path) do
          load_checkpoint(checkpoint_path)
        else
          {%{}, nil}
        end

      # 2. Start Session
      tptp_roots = List.wrap(Keyword.get(opts, :tptp_root, TptpCorpus.default_tptp_root()))

      session_opts =
        opts
        |> Keyword.put(:competitive, competitive?)
        |> Keyword.put(:timeout_ms, timeout_ms)
        |> Keyword.put(:tptp_root, [base_dir | tptp_roots])

      {:ok, session} = Session.start_link(session_opts)

      # 3. Build theory includes from BatchIncludes
      includes_content = Enum.join(config.includes, "\n")
      {:ok, init_info} = Session.init_theory(session, {:string, includes_content}, session_opts)

      # 4. Process Problems
      t0 = System.monotonic_time(:millisecond)
      total_problems = length(config.problems)

      {results_map, _interrupted?} =
        Enum.reduce_while(
          Enum.with_index(config.problems, 1),
          {completed_map, false},
          fn {{prob_rel, out_rel}, idx}, {acc_results, _} ->
            cur_ms = System.monotonic_time(:millisecond) - t0

            cond do
              overall_timeout_ms > 0 and cur_ms >= overall_timeout_ms ->
                {:halt, {acc_results, true}}

              Map.has_key?(acc_results, prob_rel) ->
                # Already proved in previous run
                cached_res = Map.get(acc_results, prob_rel)
                cur_stats = Session.stats(session)

                on_result.(%{
                  problem: prob_rel,
                  result: cached_res,
                  index: idx,
                  total: total_problems,
                  elapsed_ms: cur_ms,
                  stats: cur_stats,
                  cached: true
                })

                {:cont, {acc_results, false}}

              true ->
                prob_path = resolve_path(base_dir, prob_rel)
                out_path = if out_rel != "", do: resolve_path(base_dir, out_rel), else: nil

                prove_opts = [timeout_ms: timeout_ms, competitive: competitive?]

                res =
                  case Session.prove(session, {:file, prob_path}, prove_opts) do
                    {:ok, proof_res} ->
                      if out_path do
                        write_result(out_path, prob_rel, proof_res)
                      end

                      proof_res

                    {:error, reason} ->
                      err_res = %{szs: :error, reason: inspect(reason), duration_ms: 0}

                      if out_path do
                        write_result(out_path, prob_rel, err_res)
                      end

                      err_res
                  end

                updated_results = Map.put(acc_results, prob_rel, res)
                cur_stats = Session.stats(session)

                if checkpoint_path do
                  save_checkpoint(checkpoint_path, updated_results, config, cur_stats)
                end

                on_result.(%{
                  problem: prob_rel,
                  result: res,
                  index: idx,
                  total: total_problems,
                  elapsed_ms: cur_ms,
                  stats: cur_stats,
                  cached: false
                })

                {:cont, {updated_results, false}}
            end
          end
        )

      dur_ms = System.monotonic_time(:millisecond) - t0
      final_stats = Session.stats(session)
      Session.stop(session)

      ordered_results =
        Enum.map(config.problems, fn {prob_rel, _} ->
          {prob_rel, Map.get(results_map, prob_rel, %{szs: :not_attempted})}
        end)

      solved_count =
        Enum.count(ordered_results, fn {_, r} ->
          Map.get(r, :szs) in [:theorem, :unsatisfiable]
        end)

      report = %{
        category: config.category,
        total_problems: total_problems,
        attempted: map_size(results_map),
        solved: solved_count,
        solve_rate_pct:
          if total_problems > 0 do
            Float.round(solved_count * 100.0 / total_problems, 2)
          else
            0.0
          end,
        elapsed_ms: dur_ms,
        harvested_lemmas: final_stats.harvested_lemmas_count,
        demod_rules: final_stats.demod_rules_count,
        background_clauses: init_info.background_clauses,
        results: ordered_results
      }

      {:ok, report}
    end
  end

  @doc """
  Generates a standard CASC-J11 LTB specification file targeting the Isabelle
  Van Emde Boas Trees (VBT) problems available in the local TPTP distribution.
  """
  @spec generate_vbt_spec(Path.t(), keyword()) :: {:ok, Path.t()} | {:error, term()}
  def generate_vbt_spec(target_spec_path, opts \\ []) do
    tptp_root = Keyword.get(opts, :tptp_root, TptpCorpus.default_tptp_root())
    format = Keyword.get(opts, :format, :thf)
    limit = Keyword.get(opts, :limit, nil)
    timeout_problem = Keyword.get(opts, :timeout_problem, 15)
    timeout_overall = Keyword.get(opts, :timeout_overall, 28_800)

    itp_dir = Path.join([tptp_root, "Problems", "ITP"])

    case File.ls(itp_dir) do
      {:ok, files} ->
        pattern_match =
          case format do
            :thf -> fn f -> String.starts_with?(f, "ITP2") and String.contains?(f, "^") end
            :tff -> fn f -> String.starts_with?(f, "ITP2") and String.contains?(f, "_") end
            :all -> fn f -> String.starts_with?(f, "ITP2") and (String.contains?(f, "^") or String.contains?(f, "_")) end
          end

        vbt_files =
          files
          |> Enum.filter(pattern_match)
          |> Enum.sort()

        selected = if limit, do: Enum.take(vbt_files, limit), else: vbt_files

        spec_dir = Path.dirname(target_spec_path)
        File.mkdir_p!(spec_dir)

        header = """
        division.category LTB.VBT
        % SZS start BatchConfiguration
        execution.order ordered
        output.required Proof
        limit.time.problem.wc #{timeout_problem}
        limit.time.overall.wc #{timeout_overall}
        % SZS end BatchConfiguration

        % SZS start BatchIncludes
        % SZS end BatchIncludes

        % SZS start BatchProblems
        """

        problems_content =
          selected
          |> Enum.map(fn f ->
            prob_rel = Path.join([tptp_root, "Problems", "ITP", f])
            out_rel = Path.join(["results", Path.rootname(f) <> ".out"])
            "#{prob_rel} #{out_rel}"
          end)
          |> Enum.join("\n")

        footer = "\n% SZS end BatchProblems\n"
        full_spec = header <> problems_content <> footer

        File.write!(target_spec_path, full_spec)
        {:ok, target_spec_path}

      {:error, reason} ->
        {:error, reason}
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

  defp load_checkpoint(path) do
    case File.read(path) do
      {:ok, json} ->
        case Jason.decode(json) do
          {:ok, %{"completed" => completed} = full} ->
            stats = Map.get(full, "stats")
            converted =
              Map.new(completed, fn {k, v} ->
                szs_atom = String.to_existing_atom(Map.get(v, "szs", "unknown"))
                {k, %{
                  szs: szs_atom,
                  duration_ms: Map.get(v, "duration_ms", 0),
                  proof_length: Map.get(v, "proof_length", 0),
                  winning_strategy: Map.get(v, "winning_strategy", "unknown"),
                  verified: Map.get(v, "verified", false)
                }}
              end)
            {converted, stats}

          _ ->
            {%{}, nil}
        end

      _ ->
        {%{}, nil}
    end
  end

  defp save_checkpoint(path, results_map, config, stats) do
    File.mkdir_p!(Path.dirname(path))

    serializable =
      Map.new(results_map, fn {k, v} ->
        {k, %{
          "szs" => Atom.to_string(Map.get(v, :szs, :unknown)),
          "duration_ms" => Map.get(v, :duration_ms, 0),
          "proof_length" => Map.get(v, :proof_length, 0),
          "winning_strategy" => inspect(Map.get(v, :winning_strategy, :unknown)),
          "verified" => Map.get(v, :verified, false)
        }}
      end)

    payload = %{
      "category" => config.category,
      "total_problems" => length(config.problems),
      "completed_count" => map_size(results_map),
      "stats" => %{
        "queries_attempted" => stats.queries_attempted,
        "queries_proved" => stats.queries_proved,
        "demod_rules" => stats.demod_rules_count,
        "harvested_lemmas" => stats.harvested_lemmas_count
      },
      "completed" => serializable
    }

    tmp_path = path <> ".tmp"
    File.write!(tmp_path, Jason.encode!(payload, pretty: true))
    File.rename(tmp_path, path)
  end
end
