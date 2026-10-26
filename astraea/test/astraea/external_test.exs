defmodule Astraea.ExternalTest do
  use ExUnit.Case, async: true

  alias Astraea.{Arena, Clausifier, External, Portfolio, ProofChecker, Prover, TptpLower}
  alias Astraea.External.{Provers, Reconstruct, SZS, TffPrinter, ThfPrinter}

  @moduletag :external

  @thm_src """
  thf(q_type, type, q: ($i > $i) > $o).
  thf(p_type, type, p: $i > $o).
  thf(g_type, type, g: $i > $i).
  thf(a_type, type, a: $i).
  thf(ax_pa, axiom, p @ a).
  thf(ax_cond_id, axiom, ! [X: $i]: ((p @ a) => ((g @ X) = X))).
  thf(ax_q_id, axiom, q @ (^ [X: $i]: X)).
  thf(conj_qg, conjecture, q @ g).
  """

  @csa_src """
  thf(p_type, type, p: $i > $o).
  thf(a_type, type, a: $i).
  thf(ax_pa, axiom, p @ a).
  thf(conj_invalid, conjecture, ! [X: $i]: (p @ X)).
  """

  setup do
    dir =
      Path.join(System.tmp_dir!(), "astraea_external_test_#{System.unique_integer([:positive])}")

    File.mkdir_p!(dir)
    on_exit(fn -> File.rm_rf(dir) end)
    {:ok, dir: dir}
  end

  # A stand-in prover: a shell script whose body receives the problem file as `$1`.
  defp fake_prover(dir, name, body, formats \\ [:thf]) do
    path = Path.join(dir, Atom.to_string(name))
    File.write!(path, "#!/bin/sh\n" <> body <> "\n")
    File.chmod!(path, 0o755)
    %{name: name, executables: [path], formats: formats, args: fn _limits, file -> [file] end}
  end

  # An oracle that claims unsatisfiability and cites every clause `c<i>` of its
  # input as the unsat core, like E's `file(_, Name)` source annotations.
  @cite_all_clauses """
  echo "% SZS status Unsatisfiable"
  echo "% SZS output start CNFRefutation"
  grep -o '^t[hf]f(c[0-9]*' "$1" | sed 's/^t.f(//' | while read n; do
    echo "cnf($n, axiom, \\$false, file('input.p', $n))."
  done
  echo "% SZS output end CNFRefutation"
  """

  defp tptp_errors(source) do
    {:ok, _unit, diagnostics} =
      Tptp.Unit.from_string(source,
        resolver: {Tptp.Resolver.Fs, root: System.tmp_dir!()},
        max_concurrency: 1
      )

    Enum.filter(diagnostics, &(&1.severity == :error))
  end

  defp os_pid_alive?(pid) do
    {_, code} = System.cmd("kill", ["-0", pid], stderr_to_stdout: true)
    code == 0
  end

  describe "SZS parsing" do
    test "reads status and output block from E-style output" do
      output = """
      # Proof found!
      # SZS status Theorem
      # SZS output start CNFRefutation
      cnf(c_0_1, negated_conjecture, ~p(a)).
      cnf(c_0_2, plain, $false, inference(sr, [], [c_0_1])).
      # SZS output end CNFRefutation
      """

      parsed = SZS.parse(output)
      assert parsed.status == :theorem
      assert parsed.dataform == "CNFRefutation"
      assert length(parsed.proof) == 2
      assert SZS.classify(parsed.status) == :unsat
    end

    test "ignores status mentions outside TPTP comment lines" do
      assert %{status: :unknown} =
               SZS.parse("grep: % SZS status Theorem: No such file or directory")

      assert %{status: :unknown} = SZS.parse("thf(c, axiom, 'SZS status Theorem').")
    end

    test "maps unknown status strings without creating atoms" do
      assert %{status: :unknown, status_raw: "Wibble"} = SZS.parse("% SZS status Wibble for foo")
      assert %{status: :unknown, status_raw: nil} = SZS.parse("no answer")
      assert SZS.classify(:counter_satisfiable) == :sat
      assert SZS.classify(:gave_up) == :unknown
    end
  end

  describe "ThfPrinter" do
    test "printed clause sets re-lower and keep their refutability" do
      {:ok, lowered} = TptpLower.from_string(@thm_src)
      {arena, clauses} = Clausifier.clausify(lowered)
      printed = ThfPrinter.problem(arena, clauses)

      refute printed =~ "conjecture"
      assert {:ok, relowered} = TptpLower.from_string(printed)
      assert length(relowered.axioms) == length(clauses)
      assert {:proved, _steps, _stats} = Prover.prove_lowered(relowered)
    end

    test "declares content-addressed Skolem symbols" do
      {:ok, lowered} = TptpLower.from_string(@csa_src)
      {arena, clauses} = Clausifier.clausify(lowered)
      printed = ThfPrinter.problem(arena, clauses)

      assert [_, sk] = Regex.run(~r/type, (sk_[0-9a-f]{8}): \$i\)/, printed)
      assert printed =~ "(p @ #{sk})"
      assert {:ok, _} = TptpLower.from_string(printed)
    end
  end

  describe "MuonTrap runner" do
    test "parses the SZS answer of a prover process", %{dir: dir} do
      spec = fake_prover(dir, :fake_e, ~S|echo "# SZS status Theorem for $1"|)
      problem = Path.join(dir, "p.p")
      File.write!(problem, @thm_src)

      assert {:ok, %External.Result{} = res} = External.run(spec, problem, timeout_ms: 2_000)
      assert res.prover == :fake_e
      assert res.status == :theorem
      assert res.exit_status == 0
    end

    test "kills a prover and its child processes when it overruns its time limit", %{dir: dir} do
      # Like a portfolio prover, the script forks a worker instead of exec-ing it.
      pid_file = Path.join(dir, "worker_pid")
      spec = fake_prover(dir, :sleeper, "sleep 30 &\necho $! > #{pid_file}\nwait")
      problem = Path.join(dir, "p.p")
      File.write!(problem, @thm_src)

      assert {:ok, res} = External.run(spec, problem, timeout_ms: 300, grace_ms: 100)
      assert res.status == :timeout
      assert res.exit_status == :timeout
      assert res.elapsed_ms < 5_000

      worker_pid = wait_for_file(pid_file)
      assert eventually(fn -> not os_pid_alive?(worker_pid) end)
    end

    test "killing the calling process kills the OS prover process", %{dir: dir} do
      pid_file = Path.join(dir, "pid")
      spec = fake_prover(dir, :victim, "echo $$ > #{pid_file}\nexec sleep 30")

      caller = spawn(fn -> External.run(spec, "unused.p", timeout_ms: 60_000) end)
      os_pid = wait_for_file(pid_file)
      assert os_pid_alive?(os_pid)

      Process.exit(caller, :kill)
      assert eventually(fn -> not os_pid_alive?(os_pid) end)
    end

    test "prints clause sets into a temporary file and removes it", %{dir: dir} do
      spec =
        fake_prover(dir, :cat_e, ~S|grep -q "thf(" "$1" && echo "% SZS status Unsatisfiable"|)

      {:ok, lowered} = TptpLower.from_string(@thm_src)

      assert {:ok, %{status: :unsatisfiable}} =
               External.prove_lowered(spec, lowered, tmp_dir: dir)

      assert Path.wildcard(Path.join(dir, "astraea_cat_e_*.p")) == []
    end

    test "reports missing executables and unknown provers" do
      assert {:error, {:unknown_prover, :nope}} = External.run(:nope, "p.p")

      assert {:error, {:executable_not_found, :eprover, ["/nonexistent/eprover"]}} =
               External.run(:eprover, "p.p", path: "/nonexistent/eprover")

      assert Enum.all?(Provers.available(), &(&1 in Provers.names()))
    end
  end

  describe "TffPrinter" do
    test "encodes higher-order clauses as well-formed first-order TFF" do
      src = @thm_src <> "thf(ax_lam, axiom, ! [Y: $i]: (q @ (^ [X: $i]: (g @ Y))))."
      {:ok, lowered} = TptpLower.from_string(src)
      {arena, clauses} = Clausifier.clausify(lowered)
      printed = TffPrinter.problem(arena, clauses)

      assert tptp_errors(printed) == []
      refute printed =~ "thf("
      refute printed =~ "^"
      # The lambda over the free variable `Y` is lifted into a function of `Y`.
      assert printed =~ ~r/astraea_lift_\d+: \$i > astraea_fun_\d+\)/

      assert printed =~
               ~r/astraea_app_\d+\(astraea_lift_\d+\(V\d+\), B0\) = astraea_app_\d+\(g, V\d+\)/

      assert length(Regex.scan(~r/^tff\(c\d+, axiom/m, printed)) == length(clauses)
    end

    test "Boolean terms in argument positions become defined symbols" do
      src = """
      thf(r_type, type, r: $o > $o).
      thf(p_type, type, p: $i > $o).
      thf(ax, axiom, ! [X: $i]: (r @ (~ (p @ X)))).
      """

      {:ok, lowered} = TptpLower.from_string(src)
      {arena, clauses} = Clausifier.clausify(lowered)
      printed = TffPrinter.problem(arena, clauses)

      assert tptp_errors(printed) == []
      assert printed =~ ~r/astraea_holds\(astraea_lift_\d+\(V\d+\)\) <=> \(~ astraea_holds/
    end

    test "clause sets are sent in the prover's preferred format", %{dir: dir} do
      spec =
        fake_prover(
          dir,
          :fo_only,
          ~S|grep -q "^tff(" "$1" && echo "% SZS status Unsatisfiable"|,
          [:tff]
        )

      {:ok, lowered} = TptpLower.from_string(@thm_src)

      assert {:ok, %{status: :unsatisfiable}} =
               External.prove_lowered(spec, lowered, tmp_dir: dir)

      assert {:ok, %{status: :error}} =
               External.prove_lowered(spec, lowered, tmp_dir: dir, format: :thf)
    end
  end

  describe "Reconstruct" do
    test "reads unsat cores from E and Vampire style source annotations" do
      proof = [
        "thf(c_0_3, axiom, (p @ a), file('/tmp/x.p', ax_pa)).",
        "fof(f12,axiom,(",
        "  q(a)),",
        "  file('/home/u/TPTP/Axioms/SET001^0.ax','set_def')).",
        "cnf(c_0_9, plain, ($false), inference(sr, [status(thm)], [c_0_3])).",
        "cnf(c3, axiom, $false, file('in.p', c3))."
      ]

      assert Reconstruct.core_names(proof) == MapSet.new(["ax_pa", "set_def", "c3"])
      assert Reconstruct.clause_indices(MapSet.new(["c3", "c11", "d0", "ax_pa"])) == [3, 11]
    end

    test "re-proves a cited core with an LCF-verified proof" do
      {:ok, lowered} = TptpLower.from_string(@thm_src)
      {arena, clauses} = Clausifier.clausify(lowered)
      core = MapSet.new(0..(length(clauses) - 1), &"c#{&1}")

      assert {:proved, steps, stats} = Reconstruct.clauses(arena, clauses, core)
      assert :ok == ProofChecker.verify_refutation(stats.arena, steps)
      assert {:error, :empty_core} = Reconstruct.clauses(arena, clauses, MapSet.new(["d0"]))
      assert {:saturated, _} = Reconstruct.problem(lowered, MapSet.new(["ax_pa"]))
    end

    test "a seeded search splices its refutation onto existing derivations" do
      arena = Arena.new()
      {arena, io} = Arena.intern_type(arena, {:arrow, :i, :o})
      {arena, p} = Arena.mk_const(arena, "p", io)
      {arena, a} = Arena.mk_const(arena, "a", :i)
      {arena, x} = Arena.mk_fvar(arena, 1, :i)
      {arena, px} = Arena.mk_app(arena, p, x)
      {arena, pa} = Arena.mk_app(arena, p, a)

      # Step 2 derives `p(a)` from the axiom `p(X)`; step 3 is the axiom `~p(a)`.
      steps = %{
        1 => {:axiom, 1, MapSet.new([{:pos, px}])},
        2 => {:subst, 2, 1, %{1 => a}},
        3 => {:axiom, 3, MapSet.new([{:neg, pa}])}
      }

      seed = %{steps: steps, ids: [2, 3], next_step_id: 4, next_fvar_id: 2}
      input = [MapSet.new([{:pos, pa}]), MapSet.new([{:neg, pa}])]

      assert {:proved, proof, stats} = Prover.prove_clauses(arena, input, seed: seed)
      assert {:axiom, 1, _} = Enum.at(proof, 0)
      assert {:subst, 2, 1, _} = Enum.at(proof, 1)
      refute Enum.any?(proof, &match?({:axiom, id, _} when id > 3, &1))
      assert :ok == ProofChecker.verify_refutation(stats.arena, proof)
    end
  end

  describe "Mid-search cooperation" do
    # Unprovable for `Astraea.Prover`, which runs out of iterations rather than saturating.
    @open_src """
    thf(f_type, type, f: $i > $i).
    thf(p_type, type, p: $i > $o).
    thf(a_type, type, a: $i).
    thf(b_type, type, b: $i).
    thf(ax_pa, axiom, p @ a).
    thf(ax_step, axiom, ! [X: $i]: ((p @ X) => (p @ (f @ X)))).
    thf(conj, conjecture, p @ b).
    """

    test "an unsound oracle answer is logged but never turned into a proof", %{dir: dir} do
      spec = fake_prover(dir, :liar, @cite_all_clauses)
      {:ok, lowered} = TptpLower.from_string(@open_src)

      assert {:resource_out, stats} =
               Prover.prove_lowered(lowered,
                 cooperate: [{:liar, spec: spec, tmp_dir: dir}],
                 cooperate_interval: 0,
                 max_iterations: 100_000,
                 timeout_ms: 1_500
               )

      assert [call | _] = stats.external_calls
      assert call.prover == :liar
      assert call.szs_status == :unsatisfiable
      assert call.reconstructed == false
      assert call.core_size > 0
      assert Path.wildcard(Path.join(dir, "astraea_liar_*.p")) == []
    end

    test ":trust_external accepts an answer that cannot be reconstructed", %{dir: dir} do
      spec = fake_prover(dir, :oracle, @cite_all_clauses)
      {:ok, lowered} = TptpLower.from_string(@open_src)

      assert {:proved_external, stats} =
               Prover.prove_lowered(lowered,
                 cooperate: [{:oracle, spec: spec, tmp_dir: dir}],
                 cooperate_interval: 0,
                 trust_external: true,
                 max_iterations: 100_000,
                 timeout_ms: 1_500
               )

      assert stats.prover == :oracle
      assert stats.szs_status == :unsatisfiable
    end

    test "external calls still running at the end of the search are killed", %{dir: dir} do
      pid_file = Path.join(dir, "pid")
      spec = fake_prover(dir, :slow, "echo $$ > #{pid_file}\nexec sleep 30")
      {:ok, lowered} = TptpLower.from_string(@open_src)

      assert {:resource_out, stats} =
               Prover.prove_lowered(lowered,
                 cooperate: [{:slow, spec: spec, tmp_dir: dir}],
                 cooperate_interval: 0,
                 max_iterations: 100_000,
                 timeout_ms: 800
               )

      assert stats.external_calls == []
      os_pid = wait_for_file(pid_file)
      assert eventually(fn -> not os_pid_alive?(os_pid) end)
      assert Path.wildcard(Path.join(dir, "astraea_slow_*.p")) == []
    end
  end

  describe "Portfolio integration" do
    test "an external refutation of the clause set is reconstructed into an LCF proof", %{
      dir: dir
    } do
      spec = fake_prover(dir, :cited, @cite_all_clauses)
      {:ok, lowered} = TptpLower.from_string(@thm_src)

      assert {:proved, steps, stats} =
               Portfolio.prove_lowered(lowered,
                 strategies: [],
                 external: [{:cited, spec: spec}],
                 timeout_ms: 2_500
               )

      assert stats.winning_strategy == {:external, :cited}
      assert stats.external_assist.prover == :cited
      assert stats.external_assist.input == :clauses
      assert :ok == ProofChecker.verify_refutation(stats.arena, steps)
    end

    test "an external refutation of the original problem is reconstructed from its axiom names",
         %{dir: dir} do
      problem = Path.join(dir, "thm.p")
      File.write!(problem, @thm_src)

      cite = ~S"""
      echo "% SZS status Theorem"
      echo "% SZS output start CNFRefutation"
      for n in ax_pa ax_cond_id ax_q_id conj_qg; do echo "thf($n, axiom, \$true, file('thm.p', $n))."; done
      echo "% SZS output end CNFRefutation"
      """

      spec = fake_prover(dir, :cited_problem, cite)

      assert {:proved, steps, stats} =
               Portfolio.prove_file(problem,
                 strategies: [],
                 external: [{:cited_problem, spec: spec}],
                 tptp_root: dir,
                 timeout_ms: 2_500
               )

      assert stats.external_assist.input == :problem
      assert stats.external_assist.core_size == 4
      assert :ok == ProofChecker.verify_refutation(stats.arena, steps)
    end

    test "an external Theorem answer is reported as an unverified oracle result", %{dir: dir} do
      spec = fake_prover(dir, :oracle, ~S|echo "% SZS status Theorem"|)
      {:ok, lowered} = TptpLower.from_string(@csa_src)

      assert {:proved_external, stats} =
               Portfolio.prove_lowered(lowered,
                 strategies: [],
                 external: [{:oracle, spec: spec}],
                 timeout_ms: 2_000
               )

      assert stats.winning_strategy == {:external, :oracle}
      assert stats.szs_status == :theorem
      assert stats.input == :clauses
    end

    test "a model of the clause set is not reported as CounterSatisfiable", %{dir: dir} do
      spec = fake_prover(dir, :modeler, ~S|echo "% SZS status Satisfiable"|)
      {:ok, lowered} = TptpLower.from_string(@csa_src)

      assert {:resource_out, %{szs_status: :satisfiable}} =
               Portfolio.prove_lowered(lowered,
                 strategies: [],
                 external: [{:modeler, spec: spec}],
                 timeout_ms: 2_000
               )
    end

    test "the :fallback policy prefers an internal LCF-verified proof", %{dir: dir} do
      spec = fake_prover(dir, :fast_oracle, ~S|echo "% SZS status Theorem"|)
      {:ok, lowered} = TptpLower.from_string(@thm_src)

      assert {:proved, _steps, stats} =
               Portfolio.prove_lowered(lowered,
                 external: [{:fast_oracle, spec: spec}],
                 external_policy: :fallback,
                 timeout_ms: 2_500
               )

      refute match?({:external, _}, stats.winning_strategy)
    end

    test "the :fallback policy returns the external answer when internal search fails", %{
      dir: dir
    } do
      spec = fake_prover(dir, :late_oracle, ~S|echo "% SZS status Theorem"|)
      {:ok, lowered} = TptpLower.from_string(@csa_src)

      assert {:proved_external, %{winning_strategy: {:external, :late_oracle}}} =
               Portfolio.prove_lowered(lowered,
                 external: [{:late_oracle, spec: spec}],
                 external_policy: :fallback,
                 timeout_ms: 1_000
               )
    end

    test "a winning internal strategy kills running external provers", %{dir: dir} do
      pid_file = Path.join(dir, "pid")
      spec = fake_prover(dir, :slow, "echo $$ > #{pid_file}\nexec sleep 30")
      {:ok, lowered} = TptpLower.from_string(@thm_src)

      assert {:proved, _steps, _stats} =
               Portfolio.prove_lowered(lowered,
                 external: [{:slow, spec: spec}],
                 timeout_ms: 2_500
               )

      # The prover may be killed before its shell even writes the pid file.
      Process.sleep(200)

      with {:ok, os_pid} <- File.read(pid_file) do
        assert eventually(fn -> not os_pid_alive?(String.trim(os_pid)) end)
      end
    end
  end

  defp wait_for_file(path, attempts \\ 100) do
    case File.read(path) do
      {:ok, content} when content != "" ->
        String.trim(content)

      _ when attempts > 0 ->
        Process.sleep(20)
        wait_for_file(path, attempts - 1)

      _ ->
        flunk("#{path} was never written")
    end
  end

  defp eventually(fun, attempts \\ 100) do
    cond do
      fun.() ->
        true

      attempts == 0 ->
        false

      true ->
        Process.sleep(20)
        eventually(fun, attempts - 1)
    end
  end
end
