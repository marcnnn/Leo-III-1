defmodule Astraea.Session do
  @moduledoc """
  Persistent Theory Session & Incremental Lemma Coordinator (OTP GenServer).

  Maintains a pre-warmed background theory in memory for sequential verification
  pipelines (e.g. Isabelle Sledgehammer, Lean 4 hammers, Dafny VCs, and CASC LTB batches):
  - Ingests and clausifies background axioms and definitions once.
  - Eliminates cold-start parsing, elaboration, and indexing overhead across queries.
  - Automatically harvests sound, conjecture-free sub-proof lemmas from refutation DAGs.
  - Indexes equational lemmas directly into `Astraea.Session.DemodCache` to accelerate
    subsequent queries via directed rewriting while avoiding given-clause swamping.
  """

  use GenServer

  alias Astraea.{
    Arena,
    Clausifier,
    Portfolio,
    Session.DemodCache,
    Session.Lineage,
    TptpLower
  }

  defstruct theory_files: [],
            theory_source: "",
            theory_lowered: nil,
            theory_arena: nil,
            theory_clauses: [],
            demod_cache: DemodCache.new(),
            harvested_lemmas: [],
            queries_attempted: 0,
            queries_proved: 0,
            verified_proved: 0,
            opts: []

  # ---------------------------------------------------------------------------
  # Client API
  # ---------------------------------------------------------------------------

  @doc """
  Starts a new `Astraea.Session` coordinator.
  """
  def start_link(opts \\ []) do
    GenServer.start_link(__MODULE__, opts)
  end

  @doc """
  Initializes the background theory from a list of axiom file paths or a THF string.
  """
  def init_theory(session, theory_spec, opts \\ []) do
    GenServer.call(session, {:init_theory, theory_spec, opts}, :infinity)
  end

  @doc """
  Dispatches a proof obligation (goal) against the warm background theory.
  `goal_spec` can be `{:file, path}` or `{:string, thf_string}`.
  """
  def prove(session, goal_spec, opts \\ []) do
    timeout_ms = Keyword.get(opts, :timeout_ms, 2500)
    # Give GenServer call slightly more headroom than the prover timeout
    call_timeout = timeout_ms + 10_000
    GenServer.call(session, {:prove, goal_spec, opts}, call_timeout)
  end

  @doc """
  Returns telemetry and cache statistics for the current session.
  """
  def stats(session) do
    GenServer.call(session, :stats)
  end

  @doc """
  Stops the session coordinator.
  """
  def stop(session) do
    GenServer.stop(session)
  end

  # ---------------------------------------------------------------------------
  # GenServer Callbacks
  # ---------------------------------------------------------------------------

  @impl true
  def init(opts) do
    {:ok, %__MODULE__{opts: opts}}
  end

  @impl true
  def handle_call({:init_theory, theory_spec, opts}, _from, %__MODULE__{} = state) do
    merged_opts = Keyword.merge(state.opts, opts)

    case build_theory_source(theory_spec) do
      {:ok, source, files} ->
        case TptpLower.from_string(source, merged_opts) do
          {:ok, lowered} ->
            {arena, clauses} = Clausifier.clausify(%{lowered | conjectures: []}, sine_limit: nil)

            # Seed demodulator cache with initial equational axioms
            init_lemmas =
              clauses
              |> Enum.filter(&(MapSet.size(&1) == 1))
              |> Enum.map(fn c ->
                [{pol, atom_id}] = MapSet.to_list(c)
                {is_eq, l, r} =
                  if pol == :pos do
                    case Arena.get_node(arena, atom_id) do
                      {6, _, _, lhs, rhs} -> {true, lhs, rhs}
                      _ -> {false, nil, nil}
                    end
                  else
                    {false, nil, nil}
                  end

                %{
                  id: 0,
                  rule: :axiom,
                  clause: c,
                  thf: "",
                  is_unit: true,
                  is_equality: is_eq,
                  lhs: l,
                  rhs: r
                }
              end)

            {demod, _inserted} = DemodCache.insert_lemmas(DemodCache.new(), arena, init_lemmas)

            new_state = %__MODULE__{
              state
              | theory_files: files,
                theory_source: source,
                theory_lowered: lowered,
                theory_arena: arena,
                theory_clauses: clauses,
                demod_cache: demod,
                opts: merged_opts
            }

            {:reply, {:ok, %{background_clauses: length(clauses), demod_rules: demod.count}}, new_state}

          {:error, reason} ->
            {:reply, {:error, {:lower_failed, reason}}, state}
        end

      {:error, reason} ->
        {:reply, {:error, {:source_failed, reason}}, state}
    end
  end

  @impl true
  def handle_call({:prove, goal_spec, opts}, _from, %__MODULE__{} = state) do
    state =
      if is_nil(state.theory_lowered) do
        {:ok, empty_lowered} = TptpLower.from_string("", state.opts)
        %{state | theory_lowered: empty_lowered}
      else
        state
      end

    timeout_ms = Keyword.get(opts, :timeout_ms, 2500)
    state = %{state | queries_attempted: state.queries_attempted + 1}

    case prepare_goal_input(state, goal_spec) do
      {:ok, augmented_src} ->
        t0 = System.monotonic_time(:millisecond)

        call_opts =
          state.opts
          |> Keyword.merge(opts)
          |> Keyword.put(:timeout_ms, timeout_ms)

        case TptpLower.from_string(augmented_src, call_opts) do
          {:ok, lowered} ->
            res = Portfolio.prove_lowered(lowered, call_opts)
            dur_ms = System.monotonic_time(:millisecond) - t0

            case res do
              {:proved, steps, stats} ->
                # Harvest sound pure-theory lemmas
                {new_state, new_count} =
                  case Lineage.harvest_theory_lemmas(stats.arena, steps, lowered) do
                    {:ok, pure_lemmas, _lineage_meta} ->
                      {updated_demod, inserted} =
                        DemodCache.insert_lemmas(state.demod_cache, stats.arena, pure_lemmas)

                      s = %{
                        state
                        | demod_cache: updated_demod,
                          harvested_lemmas: state.harvested_lemmas ++ pure_lemmas,
                          queries_proved: state.queries_proved + 1,
                          verified_proved: state.verified_proved + 1
                      }

                      {s, inserted}

                    _ ->
                      {%{state | queries_proved: state.queries_proved + 1, verified_proved: state.verified_proved + 1}, 0}
                  end

                reply = {
                  :ok,
                  %{
                    szs: :theorem,
                    duration_ms: dur_ms,
                    proof_length: length(steps),
                    iterations: Map.get(stats, :iterations, 0),
                    winning_strategy: Map.get(stats, :winning_strategy, :unknown),
                    harvested_rules: new_count,
                    verified: true
                  }
                }

                {:reply, reply, new_state}

              {:proved_external, stats} ->
                reply = {
                  :ok,
                  %{
                    szs: :theorem,
                    duration_ms: dur_ms,
                    proof_length: 0,
                    iterations: 0,
                    winning_strategy: {:external, Map.get(stats, :prover, :external)},
                    harvested_rules: 0,
                    verified: false
                  }
                }

                {:reply, reply, %{state | queries_proved: state.queries_proved + 1}}

              other ->
                szs = Portfolio.szs_status(other)
                new_state =
                  if szs in [:theorem, :unsatisfiable] do
                    %{state | queries_proved: state.queries_proved + 1}
                  else
                    state
                  end

                reply = {
                  :ok,
                  %{
                    szs: szs,
                    duration_ms: dur_ms,
                    status: elem(other, 0),
                    winning_strategy: :none,
                    harvested_rules: 0,
                    verified: false
                  }
                }

                {:reply, reply, new_state}
            end

          {:error, reason} ->
            {:reply, {:error, {:parse_goal_failed, reason}}, state}
        end

      {:error, reason} ->
        {:reply, {:error, {:goal_input_failed, reason}}, state}
    end
  end

  @impl true
  def handle_call(:stats, _from, %__MODULE__{} = state) do
    info = %{
      theory_files_count: length(state.theory_files),
      background_clauses: length(state.theory_clauses),
      demod_rules_count: state.demod_cache.count,
      harvested_lemmas_count: length(state.harvested_lemmas),
      queries_attempted: state.queries_attempted,
      queries_proved: state.queries_proved,
      verified_proved: state.verified_proved,
      solve_rate_pct:
        if state.queries_attempted > 0 do
          Float.round(state.queries_proved * 100.0 / state.queries_attempted, 2)
        else
          0.0
        end
    }

    {:reply, info, state}
  end

  @impl true
  def handle_info({ref, _pid, _strategy, _result}, state) when is_reference(ref) do
    {:noreply, state}
  end

  def handle_info({:DOWN, _ref, :process, _pid, _reason}, state) do
    {:noreply, state}
  end

  def handle_info(_msg, state) do
    {:noreply, state}
  end

  # ---------------------------------------------------------------------------
  # Helpers
  # ---------------------------------------------------------------------------

  defp build_theory_source({:files, paths}) when is_list(paths) do
    includes =
      paths
      |> Enum.map(fn p -> "include('#{p}')." end)
      |> Enum.join("\n")

    {:ok, includes, paths}
  end

  defp build_theory_source({:string, str}) when is_binary(str) do
    {:ok, str, []}
  end

  defp build_theory_source(:none) do
    {:ok, "", []}
  end

  defp build_theory_source(other) do
    {:error, {:invalid_theory_spec, other}}
  end

  defp prepare_goal_input(state, {:file, path}) do
    case File.read(path) do
      {:ok, content} ->
        prepare_goal_content(state, content)

      {:error, reason} ->
        {:error, reason}
    end
  end

  defp prepare_goal_input(state, {:string, content}) do
    prepare_goal_content(state, content)
  end

  defp prepare_goal_input(state, {:formula, conjecture_thf}) do
    content = "thf(goal_conjecture, conjecture, #{conjecture_thf})."
    prepare_goal_content(state, content)
  end

  defp prepare_goal_input(_state, other) do
    {:error, {:invalid_goal_spec, other}}
  end

  defp prepare_goal_content(state, goal_content) do
    cached_axioms =
      state.demod_cache.thf_rules
      |> Enum.take(300)
      |> Enum.with_index()
      |> Enum.map(fn {thf, idx} -> "thf(session_lem_#{idx}, axiom, #{thf})." end)
      |> Enum.join("\n")

    augmented =
      cond do
        state.theory_source == "" and cached_axioms == "" ->
          goal_content

        state.theory_source == "" ->
          "% --- ACCUMULATED SOUND THEORY RULES ---\n" <> cached_axioms <> "\n" <> goal_content

        cached_axioms == "" ->
          state.theory_source <> "\n" <> goal_content

        true ->
          state.theory_source <> "\n% --- ACCUMULATED SOUND THEORY RULES ---\n" <> cached_axioms <> "\n" <> goal_content
      end

    {:ok, augmented}
  end
end
