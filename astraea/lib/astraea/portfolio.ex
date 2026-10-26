defmodule Astraea.Portfolio do
  @moduledoc """
  WP3: Multi-Core OTP Strategy Portfolio Runner for `Astraea.Prover`.

  Coordinates concurrent strategy workers over a shared problem input, varying:
  1. `:goal_standard` — Balanced SInE (`sine_limit: 55`), bridge-predicate preservation,
     and goal-directed variable-penalized clause ordering.
  2. `:sine_tight_unit` — Tight SInE premise selection (`sine_limit: 16`) for large
     axiomatizations (`ITP`, `SEU`, `CSR`) with unit-focused clause selection.
  3. `:full_inline_weight` — Full constant & bridge-predicate expansion into conjectures
     (`inline_bridges: true`, `sine_limit: 40`) with weight-first KBO ordering.
  4. `:broad_breadth` — Wide SInE window (`sine_limit: 90`) and breadth-first depth
     ordering with higher literal/weight ceilings (`max_clause_lits: 8`).

  Workers race concurrently under an OTP monitor loop; as soon as the first worker
  constructs an LCF-verified refutation (`Astraea.ProofChecker.verify_refutation/2`),
  sibling workers are terminated immediately (`Process.exit(pid, :kill)`).

  External provers (`:external` option, see `Astraea.External`) race alongside the
  internal strategies as MuonTrap-supervised OS processes. Killing their worker
  closes the port and MuonTrap kills the prover process tree. An external
  refutation is reconstructed from its unsat core by `Astraea.Prover`
  (`Astraea.External.Reconstruct`) and then reported as an ordinary LCF-verified
  `{:proved, ...}` with `:external_assist` stats. Answers that cannot be
  reconstructed stay unverified oracle results, reported as
  `{:proved_external, stats}` or `{:counter_satisfiable, stats}`.
  """

  alias Astraea.{Clausifier, Compressor, External, ProofChecker, Prover, TptpCorpus, TptpLower}
  alias Astraea.External.Reconstruct

  @type strategy_spec :: {atom(), keyword()}

  @doc """
  Returns the default 4-strategy portfolio schedule.
  """
  @spec default_strategies() :: [strategy_spec()]
  def default_strategies do
    [
      {:goal_standard,
       [
         sine_limit: 55,
         inline_bridges: false,
         scoring_mode: :goal_directed,
         max_clause_lits: 6,
         max_clause_weight: 45
       ]},
      {:sine_tight_unit,
       [
         sine_limit: 16,
         inline_bridges: false,
         scoring_mode: :unit_focused,
         max_clause_lits: 6,
         max_clause_weight: 50
       ]},
      {:full_inline_weight,
       [
         sine_limit: 40,
         inline_bridges: true,
         scoring_mode: :weight_first,
         max_clause_lits: 7,
         max_clause_weight: 55
       ]},
      {:broad_breadth,
       [
         sine_limit: 90,
         inline_bridges: false,
         scoring_mode: :breadth_first,
         max_clause_lits: 8,
         max_clause_weight: 60
       ]}
    ]
  end

  @doc """
  Parses, lowers, and runs the multi-strategy portfolio on a TPTP problem file.
  """
  @spec prove_file(Path.t(), keyword()) :: Prover.result()
  def prove_file(path, opts \\ []) do
    case TptpLower.from_file(path, opts) do
      {:ok, lowered} ->
        prove_lowered(lowered, Keyword.put_new(opts, :problem_path, path))

      {:error, _} = err ->
        err
    end
  end

  @doc """
  Runs all portfolio strategies concurrently on a `%Astraea.TptpLower{}` problem,
  returning the first LCF-verified refutation and immediately killing sibling workers.
  If `:compress => true` (default `true`), compresses the winning LCF proof DAG via
  `Astraea.Compressor.compress_dag/2`.

  External provers are enabled with `:external`, a list of prover names or
  `{name, opts}` tuples. The opts are those of `Astraea.External.run/3` plus
  `:input` (`:problem` passes the original file from `:problem_path`, `:clauses`
  passes Astraea's clause set; defaults to `:problem` when a path is known),
  `:spec` for custom provers, and `:reconstruct` (default `true`).

  `:cooperate` is passed to every internal strategy (see `Astraea.Prover.prove_clauses/3`).

  `:external_policy` decides how external answers are used:
    * `:race` (default) - the first definitive answer, internal or external, wins
    * `:fallback` - an external answer is only returned when no internal strategy
      finds an LCF-verified proof
  """
  @spec prove_lowered(TptpLower.t(), keyword()) ::
          Prover.result() | {:proved_external, map()} | {:counter_satisfiable, map()}
  def prove_lowered(%TptpLower{} = lowered, opts \\ []) do
    timeout_ms = Keyword.get(opts, :timeout_ms, 2_500)
    strategies = Keyword.get(opts, :strategies, default_strategies())
    externals = opts |> Keyword.get(:external, []) |> Enum.map(&normalize_external/1)
    policy = Keyword.get(opts, :external_policy, :race)
    compress? = Keyword.get(opts, :compress, true)
    deadline_ms = System.monotonic_time(:millisecond) + timeout_ms

    parent = self()
    race_ref = make_ref()

    # Killed external workers cannot remove their own problem files.
    tmp_dir =
      if externals != [] do
        dir =
          Path.join(System.tmp_dir!(), "astraea_portfolio_#{System.unique_integer([:positive])}")

        File.mkdir_p!(dir)
        dir
      end

    internal_workers =
      Map.new(strategies, fn {strat_name, strat_opts} ->
        merged_opts =
          opts
          |> Keyword.merge(strat_opts)
          |> Keyword.put(:timeout_ms, timeout_ms)

        {pid, mon_ref} =
          spawn_monitor(fn ->
            res = Prover.prove_lowered(lowered, merged_opts)
            send(parent, {race_ref, self(), strat_name, res})
          end)

        {pid, {mon_ref, strat_name}}
      end)

    external_workers =
      Map.new(externals, fn {ext_name, ext_opts} ->
        ext_opts =
          ext_opts
          |> Keyword.put_new(:timeout_ms, timeout_ms)
          |> Keyword.put(:tmp_dir, tmp_dir)

        strat_name = {:external, ext_name}

        {pid, mon_ref} =
          spawn_monitor(fn ->
            res = run_external(ext_name, ext_opts, lowered, opts, deadline_ms)
            send(parent, {race_ref, self(), strat_name, res})
          end)

        {pid, {mon_ref, strat_name}}
      end)

    workers = Map.merge(internal_workers, external_workers)

    race_result =
      try do
        await_race(race_ref, workers, deadline_ms, nil, policy)
      after
        if tmp_dir, do: File.rm_rf(tmp_dir)
      end

    case race_result do
      {:proved, steps, stats} ->
        if compress? and is_map_key(stats, :arena) do
          {:ok, comp_arena, comp_steps, comp_meta} =
            Compressor.compress_dag(stats.arena, steps)

          {:proved, comp_steps,
           stats
           |> Map.put(:arena, comp_arena)
           |> Map.put(:raw_proof_length, length(steps))
           |> Map.put(:proof_length, length(comp_steps))
           |> Map.put(:compression, comp_meta)}
        else
          {:proved, steps, stats}
        end

      other ->
        other
    end
  end

  defp normalize_external(name) when is_atom(name), do: {name, []}

  defp normalize_external({name, ext_opts}) when is_atom(name) and is_list(ext_opts),
    do: {name, ext_opts}

  defp run_external(ext_name, ext_opts, lowered, opts, deadline_ms) do
    prover = Keyword.get(ext_opts, :spec, ext_name)
    problem_path = Keyword.get(opts, :problem_path)
    input = Keyword.get(ext_opts, :input, if(problem_path, do: :problem, else: :clauses))

    {run, reconstruct} =
      case input do
        :problem ->
          tptp_root = Keyword.get(opts, :tptp_root, TptpCorpus.default_tptp_root())
          ext_opts = Keyword.put_new(ext_opts, :tptp_root, tptp_root)

          {External.prove_problem(prover, problem_path, ext_opts),
           &Reconstruct.problem(lowered, &1, &2)}

        :clauses ->
          {arena, clauses} =
            Clausifier.clausify(lowered,
              sine_limit: Keyword.get(ext_opts, :sine_limit, 55),
              inline_bridges: Keyword.get(ext_opts, :inline_bridges, false)
            )

          {External.prove_clauses(prover, arena, clauses, ext_opts),
           &Reconstruct.clauses(arena, clauses, &1, &2)}
      end

    case run do
      {:ok, %External.Result{} = res} ->
        stats = %{
          iterations: 0,
          prover: res.prover,
          input: input,
          szs_status: res.status,
          dataform: res.dataform,
          proof: res.proof,
          external_elapsed_ms: res.elapsed_ms
        }

        case {External.SZS.classify(res.status), input} do
          {:unsat, _} ->
            if Keyword.get(ext_opts, :reconstruct, true),
              do: reconstruct_external(res, stats, reconstruct, opts, deadline_ms),
              else: {:proved_external, stats}

          # A model of the SInE-filtered clause set is not a model of the problem.
          {:sat, :problem} ->
            {:counter_satisfiable, stats}

          _ ->
            {:resource_out, stats}
        end

      {:error, reason} ->
        {:error, {:external, ext_name, reason}}
    end
  end

  # Re-proves the unsat core of an external refutation with `Astraea.Prover`, which
  # turns the oracle answer into an LCF-verified `{:proved, ...}` result.
  defp reconstruct_external(res, stats, reconstruct, opts, deadline_ms) do
    core = Reconstruct.core_names(res.proof)
    remaining = max(deadline_ms - System.monotonic_time(:millisecond), 0)

    recon_opts =
      opts
      |> Keyword.drop([:external, :external_policy, :strategies, :cooperate])
      |> Keyword.put(:timeout_ms, remaining)

    case reconstruct.(core, recon_opts) do
      {:proved, steps, recon_stats} ->
        {:proved, steps,
         Map.put(recon_stats, :external_assist, %{
           prover: res.prover,
           input: stats.input,
           szs_status: res.status,
           core_size: MapSet.size(core),
           external_elapsed_ms: res.elapsed_ms
         })}

      other ->
        {:proved_external,
         Map.merge(stats, %{core_size: MapSet.size(core), reconstruction: elem(other, 0)})}
    end
  end

  defp await_race(_race_ref, workers, _deadline_ms, last_non_proof, _policy)
       when map_size(workers) == 0 do
    last_non_proof || {:resource_out, %{iterations: 0}}
  end

  defp await_race(race_ref, workers, deadline_ms, last_non_proof, policy) do
    rem_ms = max(0, deadline_ms - System.monotonic_time(:millisecond))

    receive do
      {^race_ref, _pid, strat_name, {:proved, steps, stats}} ->
        shutdown_workers(workers)

        {:proved, steps,
         stats
         |> Map.put(:winning_strategy, strat_name)}

      {^race_ref, _pid, _strat_name, {:error, {:lcf_verification_failed, _, _}} = lcf_err} ->
        shutdown_workers(workers)
        lcf_err

      {^race_ref, _pid, strat_name, {tag, stats}}
      when tag in [:proved_external, :counter_satisfiable] and policy == :race ->
        shutdown_workers(workers)
        {tag, Map.put(stats, :winning_strategy, strat_name)}

      {^race_ref, pid, strat_name, non_proof} ->
        case Map.pop(workers, pid) do
          {{mon_ref, _}, rest} ->
            Process.demonitor(mon_ref, [:flush])
            tagged = tag_non_proof(non_proof, strat_name)

            continue_race(
              race_ref,
              rest,
              deadline_ms,
              pick_better_non_proof(last_non_proof, tagged),
              policy
            )

          {nil, rest} ->
            continue_race(race_ref, rest, deadline_ms, last_non_proof, policy)
        end

      {:DOWN, _mon_ref, :process, pid, _reason} ->
        rest = Map.delete(workers, pid)
        continue_race(race_ref, rest, deadline_ms, last_non_proof, policy)
    after
      rem_ms + 250 ->
        shutdown_workers(workers)
        finish_external(last_non_proof) || {:resource_out, %{iterations: 0}}
    end
  end

  # Under `:fallback`, a held external answer is returned as soon as no internal
  # strategy is left that could still produce an LCF-verified proof.
  defp continue_race(race_ref, workers, deadline_ms, best, policy) do
    internal_left? =
      Enum.any?(workers, fn {_pid, {_mon_ref, name}} -> not match?({:external, _}, name) end)

    if external_answer?(best) and not internal_left? do
      shutdown_workers(workers)
      finish_external(best)
    else
      await_race(race_ref, workers, deadline_ms, best, policy)
    end
  end

  defp external_answer?({tag, _stats}), do: tag in [:proved_external, :counter_satisfiable]
  defp external_answer?(_other), do: false

  defp finish_external({tag, stats} = answer) do
    if external_answer?(answer),
      do: {tag, Map.put(stats, :winning_strategy, stats.strategy)},
      else: answer
  end

  defp finish_external(other), do: other

  defp shutdown_workers(workers) do
    Enum.each(workers, fn {pid, {mon_ref, _strat_name}} ->
      Process.demonitor(mon_ref, [:flush])
      Process.exit(pid, :kill)
    end)
  end

  defp tag_non_proof({tag, stats}, strat_name) when is_map(stats) do
    {tag, Map.put(stats, :strategy, strat_name)}
  end

  defp tag_non_proof(other, _strat_name), do: other

  defp pick_better_non_proof(nil, candidate), do: candidate

  defp pick_better_non_proof({tag, _} = ext, _candidate)
       when tag in [:proved_external, :counter_satisfiable],
       do: ext

  defp pick_better_non_proof(_prev, {tag, _} = ext)
       when tag in [:proved_external, :counter_satisfiable],
       do: ext

  defp pick_better_non_proof({:saturated, _} = sat, _candidate), do: sat
  defp pick_better_non_proof(_prev, {:saturated, _} = sat), do: sat
  defp pick_better_non_proof(prev, _candidate), do: prev

  @doc """
  Evaluates a TPTP split (`:smoke`, `:dev`, or `:holdout`) using the multi-strategy
  portfolio, enforcing Gate 3 (0 `CSA` false proofs, 100% LCF proof verification)
  and aggregating strategy win counts and proof compression telemetry.
  """
  @spec evaluate_split(:smoke | :dev | :holdout, keyword()) :: map()
  def evaluate_split(split, opts \\ []) when split in [:smoke, :dev, :holdout] do
    tptp_root = Keyword.get(opts, :tptp_root, TptpCorpus.default_tptp_root())
    timeout_ms = Keyword.get(opts, :timeout_ms, 2_500)
    default_conc = max(1, div(System.schedulers_online(), 2))
    max_concurrency = Keyword.get(opts, :max_concurrency, default_conc)

    entries = TptpCorpus.load_split_entries(split)

    results =
      entries
      |> Task.async_stream(
        fn entry ->
          abs_path = Path.join(tptp_root, entry.rel_path)
          t0 = System.monotonic_time(:microsecond)
          res = prove_file(abs_path, Keyword.put(opts, :tptp_root, tptp_root))
          elapsed_ms = Float.round((System.monotonic_time(:microsecond) - t0) / 1000.0, 2)
          {entry, res, elapsed_ms}
        end,
        max_concurrency: max_concurrency,
        timeout: timeout_ms + 8_000,
        on_timeout: :kill_task
      )
      |> Enum.map(fn
        {:ok, item} -> item
        {:exit, :timeout} -> {:timeout, :resource_out, timeout_ms * 1.0}
      end)

    thm_solved =
      for {entry, {:proved, steps, st}, ms} <- results,
          is_map(entry) and entry.status == "Theorem" do
        %{
          problem: entry.problem,
          domain: entry.domain,
          proof_length: length(steps),
          raw_proof_length: Map.get(st, :raw_proof_length, length(steps)),
          iterations: st.iterations,
          elapsed_ms: ms,
          winning_strategy: Map.get(st, :winning_strategy, :goal_standard),
          compression: Map.get(st, :compression, %{}),
          external_assist: Map.get(st, :external_assist)
        }
      end

    csa_false_proofs =
      for {entry, {:proved, _steps, _st}, _ms} <- results,
          is_map(entry) and entry.status in ["CounterSatisfiable", "Satisfiable"] do
        entry.problem
      end

    lcf_failures =
      for {entry, {:error, {:lcf_verification_failed, reason, _}}, _ms} <- results,
          is_map(entry) do
        {entry.problem, reason}
      end

    strategy_wins =
      Enum.frequencies_by(thm_solved, & &1.winning_strategy)

    # LCF-verified proofs found with external help (portfolio racer or mid-search cooperation).
    externally_assisted = Enum.count(thm_solved, & &1.external_assist)

    domain_breakdown =
      thm_solved
      |> Enum.group_by(& &1.domain)
      |> Map.new(fn {dom, list} -> {dom, length(list)} end)

    # External oracle answers are tallied apart from LCF-verified proofs.
    external_thm_solved =
      for {entry, {:proved_external, st}, ms} <- results,
          is_map(entry) and entry.status == "Theorem" do
        %{
          problem: entry.problem,
          domain: entry.domain,
          elapsed_ms: ms,
          winning_strategy: st.winning_strategy
        }
      end

    external_unsound =
      for {entry, {tag, st}, _ms} <- results,
          is_map(entry),
          {tag, entry.status} in [
            {:proved_external, "CounterSatisfiable"},
            {:proved_external, "Satisfiable"},
            {:counter_satisfiable, "Theorem"},
            {:counter_satisfiable, "Unsatisfiable"}
          ] do
        {entry.problem, st.winning_strategy, st.szs_status}
      end

    %{
      split: split,
      total: length(entries),
      thm_total: Enum.count(entries, &(&1.status == "Theorem")),
      csa_total: Enum.count(entries, &(&1.status in ["CounterSatisfiable", "Satisfiable"])),
      thm_solved_count: length(thm_solved),
      thm_solved: thm_solved,
      externally_assisted_count: externally_assisted,
      strategy_wins: strategy_wins,
      domain_breakdown: domain_breakdown,
      csa_false_proofs: csa_false_proofs,
      lcf_failures: lcf_failures,
      external_thm_solved_count: length(external_thm_solved),
      external_thm_solved: external_thm_solved,
      external_strategy_wins: Enum.frequencies_by(external_thm_solved, & &1.winning_strategy),
      external_unsound: external_unsound,
      raw_results: results
    }
  end

  @spec verify_proof(Astraea.Arena.t(), [ProofChecker.step()]) ::
          :ok | {:error, term()}
  def verify_proof(arena, steps) do
    ProofChecker.verify_refutation(arena, steps)
  end
end
