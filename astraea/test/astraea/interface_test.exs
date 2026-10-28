defmodule Astraea.InterfaceTest do
  use ExUnit.Case, async: true

  import ExUnit.CaptureIO

  alias Astraea.{CLI, Portfolio, Schedule, TptpLower, Tstp}

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

  @inst_src """
  thf(p_type, type, p: $i > $o).
  thf(a_type, type, a: $i).
  thf(ax_all, axiom, ! [X: $i]: (p @ X)).
  thf(conj_pa, conjecture, p @ a).
  """

  @unsat_src """
  thf(p_type, type, p: $i > $o).
  thf(a_type, type, a: $i).
  thf(ax_all, axiom, ! [X: $i]: (p @ X)).
  thf(ax_not_pa, axiom, ~ (p @ a)).
  """

  @cax_src """
  thf(p_type, type, p: $o).
  thf(q_type, type, q: $o).
  thf(ax_p, axiom, p).
  thf(ax_not_p, axiom, ~ p).
  thf(conj_q, conjecture, q).
  """

  @csa_src """
  thf(p_type, type, p: $i > $o).
  thf(a_type, type, a: $i).
  thf(ax_pa, axiom, p @ a).
  thf(conj_invalid, conjecture, ! [X: $i]: (p @ X)).
  """

  # A higher-order non-theorem: Astraea can neither prove it nor claim a model.
  @ho_open_src """
  thf(q_type, type, q: ($i > $o) > $o).
  thf(conj_open, conjecture, q @ (^ [X: $i]: $true)).
  """

  @def_src """
  thf(leibeq_decl, type, leibeq: $i > $i > $o).
  thf(leibeq, definition, leibeq = (^ [X: $i, Y: $i]: ! [P: $i > $o]: ((P @ X) => (P @ Y)))).
  thf(f_decl, type, f: $i > $i).
  thf(p_decl, type, p: ($i > $i) > $o).
  thf(conj, conjecture, ((! [X: $i]: (leibeq @ (f @ X) @ X)) & (p @ (^ [X: $i]: X))) => (p @ f)).
  """

  setup do
    dir =
      Path.join(System.tmp_dir!(), "astraea_interface_test_#{System.unique_integer([:positive])}")

    File.mkdir_p!(dir)
    on_exit(fn -> File.rm_rf(dir) end)
    {:ok, dir: dir}
  end

  defp write_problem(dir, name, source) do
    path = Path.join(dir, name)
    File.write!(path, source)
    path
  end

  defp prove!(source) do
    {:ok, lowered} = TptpLower.from_string(source)
    {lowered, Portfolio.prove_lowered(lowered, timeout_ms: 2_000)}
  end

  defp fake_prover(dir, name, body) do
    path = Path.join(dir, Atom.to_string(name))
    File.write!(path, "#!/bin/sh\n" <> body <> "\n")
    File.chmod!(path, 0o755)
    %{name: name, executables: [path], formats: [:thf], args: fn _limits, file -> [file] end}
  end

  describe "TSTP derivations" do
    test "a refutation is a well-formed derivation from the problem's formulas", %{dir: dir} do
      path = write_problem(dir, "thm.p", @thm_src)
      {lowered, {:proved, steps, stats}} = prove!(@thm_src)

      tstp =
        Tstp.derivation(lowered, steps, stats,
          problem: "thm.p",
          problem_path: path,
          tptp_root: dir
        )

      assert {:ok, derivation, []} = Tptp.Derivation.from_string(tstp)
      assert Tptp.Derivation.acyclic?(derivation)

      # The only non-declaration root is the empty clause.
      roots = Enum.reject(derivation.roots, &String.starts_with?(&1, "decl_"))
      assert [root] = roots
      assert tstp =~ ~r/thf\(#{root}, plain, \$false,/

      # Leaves are the problem's formulas, verbatim, with file sources.
      leaves = Enum.reject(derivation.leaves, &String.starts_with?(&1, "decl_"))
      assert Enum.sort(leaves) == ["ax_cond_id", "ax_pa", "ax_q_id", "conj_qg"]
      assert tstp =~ "thf(ax_cond_id, axiom, ![X: $i]: ((p @ a) => ((g @ X) = X)),"
      assert tstp =~ "file('thm.p', ax_pa)"

      # The conjecture is negated and its clause cites the negation.
      assert tstp =~ "inference(negate_conjecture, [status(cth)], [conj_qg])"

      assert tstp =~
               ~r/negated_conjecture, \(\(~ \(q @ g\)\)\),\s+inference\(cnf, \[status\(esa\)\], \[neg_conj_qg\]\)/

      assert tstp =~ "inference(func_ext, [status(thm)]"

      # The printed formulas and clauses re-parse as a TPTP problem.
      assert {:ok, _unit, diagnostics} =
               Tptp.Unit.from_string(tstp,
                 resolver: {Tptp.Resolver.Fs, root: dir},
                 max_concurrency: 1
               )

      refute Enum.any?(diagnostics, &(&1.severity == :error))
    end

    test "instantiations carry bind/2 parent details" do
      {lowered, {:proved, steps, stats}} = prove!(@inst_src)
      tstp = Tstp.derivation(lowered, steps, stats, problem: "inst.p")

      assert tstp =~
               ~r/inference\(instantiate, \[status\(thm\)\], \[c_\d+:\[bind\(V\d+, \$thf\(a\)\)\]\]\)/

      assert {:ok, _derivation, []} = Tptp.Derivation.from_string(tstp)
    end

    test "clausification steps cite the definitions they inline", %{dir: dir} do
      path = write_problem(dir, "def.p", @def_src)
      {lowered, {:proved, steps, stats}} = prove!(@def_src)
      tstp = Tstp.derivation(lowered, steps, stats, problem: "def.p", problem_path: path)

      assert tstp =~ "inference(cnf, [status(esa)], [neg_conj, leibeq])"
      assert tstp =~ "type, leibeq: ($i > ($i > $o)))."
      assert tstp =~ "file('def.p', leibeq)"
      assert {:ok, derivation, []} = Tptp.Derivation.from_string(tstp)
      assert "leibeq" in derivation.leaves
    end

    test "without the problem file input formulas are printed from their lowered form" do
      {lowered, {:proved, steps, stats}} = prove!(@thm_src)
      tstp = Tstp.derivation(lowered, steps, stats, problem: "thm.p")

      assert tstp =~ "thf(ax_cond_id, axiom, (! [B0: $i]: ((~ (p @ a)) | ((g @ B0) = B0))),"
      assert {:ok, _derivation, []} = Tptp.Derivation.from_string(tstp)
    end

    test "search-time clausification and choice instances are rendered" do
      alias Astraea.{Arena, Prover}

      arena = Arena.new()
      {arena, io} = Arena.intern_type(arena, {:arrow, :i, :o})
      {arena, p} = Arena.mk_const(arena, "p", io)
      {arena, q} = Arena.mk_const(arena, "q", io)
      {arena, a} = Arena.mk_const(arena, "a", :i)
      {arena, choice} = Arena.mk_const(arena, "$choice", {:arrow, io, :i})
      {arena, pa} = Arena.mk_app(arena, p, a)
      {arena, qa} = Arena.mk_app(arena, q, a)
      {arena, eps_p} = Arena.mk_app(arena, choice, p)
      {arena, p_eps} = Arena.mk_app(arena, p, eps_p)
      {arena, bool_eq} = Arena.mk_eq(arena, pa, qa)
      lowered = %TptpLower{arena: arena}

      for {clauses, kind, rendered} <- [
            {[[{:pos, pa}], [{:neg, p_eps}]], :choice, "introduced(axiom_of_choice, [], [])"},
            {[[{:neg, bool_eq}], [{:pos, pa}], [{:pos, qa}]], :cnf, "status(thm)"}
          ] do
        clauses = Enum.map(clauses, &MapSet.new/1)
        assert {:proved, steps, stats} = Prover.prove_clauses(arena, clauses, timeout_ms: 2_000)
        assert Enum.any?(steps, &(elem(&1, 0) == kind))

        {_arena, derived} = Tstp.replay(stats.arena, steps)
        assert derived[elem(List.last(steps), 1)] == MapSet.new()

        tstp = Tstp.derivation(lowered, steps, stats, problem: "p.p")
        assert tstp =~ rendered
        assert {:ok, derivation, []} = Tptp.Derivation.from_string(tstp)
        assert Tptp.Derivation.acyclic?(derivation)
      end
    end

    test "replay recomputes the clause of every kernel step" do
      {_lowered, {:proved, steps, stats}} = prove!(@thm_src)
      {_arena, clauses} = Tstp.replay(stats.arena, steps)

      assert map_size(clauses) == length(steps)
      assert clauses[elem(List.last(steps), 1)] == MapSet.new()
    end

    test "clause keys identify clauses up to variable renaming" do
      {:ok, lowered} = TptpLower.from_string(@inst_src)
      arena = lowered.arena
      {arena, ty} = Astraea.Arena.intern_type(arena, {:arrow, :i, :o})
      {arena, p} = Astraea.Arena.mk_const(arena, "p", ty)
      {arena, x1} = Astraea.Arena.mk_fvar(arena, 1, :i)
      {arena, x7} = Astraea.Arena.mk_fvar(arena, 7, :i)
      {arena, px1} = Astraea.Arena.mk_app(arena, p, x1)
      {arena, px7} = Astraea.Arena.mk_app(arena, p, x7)

      assert Tstp.clause_key(arena, MapSet.new([{:pos, px1}])) ==
               Tstp.clause_key(arena, MapSet.new([{:pos, px7}]))

      refute Tstp.clause_key(arena, MapSet.new([{:pos, px1}])) ==
               Tstp.clause_key(arena, MapSet.new([{:neg, px7}]))
    end

    test "status lines and output blocks follow Leo-III's format" do
      assert Tstp.status_line(:counter_satisfiable, "p.p") ==
               "% SZS status CounterSatisfiable for p.p"

      assert Tstp.status_line(:theorem, "p.p", "12 ms") == "% SZS status Theorem for p.p : 12 ms"

      assert IO.iodata_to_binary(Tstp.output_block("CNFRefutation", "p.p", "body\n")) ==
               "% SZS output start CNFRefutation for p.p\nbody\n% SZS output end CNFRefutation for p.p\n"
    end
  end

  describe "SZS answers" do
    test "refutations are Theorem, Unsatisfiable or ContradictoryAxioms" do
      {_lowered, thm} = prove!(@thm_src)
      assert Portfolio.szs_status(thm) == :theorem

      {_lowered, unsat} = prove!(@unsat_src)
      assert Portfolio.szs_status(unsat) == :unsatisfiable

      {_lowered, cax} = prove!(@cax_src)
      assert {:proved, _steps, _stats} = cax
      assert Portfolio.szs_status(cax) == :contradictory_axioms
    end

    test "an incomplete saturation is never reported as a model" do
      {_lowered, result} = prove!(@csa_src)

      refute match?({tag, _} when tag in [:counter_satisfiable, :satisfiable], result)
      assert Portfolio.szs_status(result) in [:gave_up, :timeout]
    end

    test "external models of the original problem are CounterSatisfiable or Satisfiable", %{
      dir: dir
    } do
      spec = fake_prover(dir, :modeler, ~S|echo "% SZS status Satisfiable"|)

      for {src, expected} <- [{@csa_src, :counter_satisfiable}, {@unsat_src, :satisfiable}] do
        path = write_problem(dir, "#{expected}.p", src)

        result =
          Portfolio.prove_file(path,
            strategies: [],
            external: [{:modeler, spec: spec}],
            tptp_root: dir,
            timeout_ms: 2_000
          )

        assert {^expected, _stats} = result
        assert Portfolio.szs_status(result) == expected
      end
    end

    test "unverified external refutations keep the problem's status" do
      result = {:proved_external, %{szs: :theorem}}
      assert Portfolio.szs_status(result) == :theorem
      assert Portfolio.szs_status({:error, :parse}) == :error
      assert Portfolio.szs_status({:saturated, %{}}) == :gave_up
    end
  end

  describe "strategy schedule" do
    test "Leo-III's strategies are data and map onto Astraea options" do
      strategies = Schedule.leo3_strategies()
      assert length(strategies) == 17
      s3b = Enum.find(strategies, &(&1.name == :s3b))
      assert s3b.share == 0.5

      opts = Schedule.leo3_opts(s3b.params)
      assert opts[:sos] == true
      assert opts[:prim_subst] == 3
      assert opts[:unifier_count] == 3
      assert opts[:unify_depth] == 8
      assert opts[:ordered] == true
      assert opts[:flex_resolution] == :ground

      funcspec = Enum.find(strategies, &(&1.name == :funcspec))
      assert Schedule.leo3_opts(funcspec.params)[:ordered] == false
      assert Schedule.leo3_opts(funcspec.params)[:flex_resolution] == :all
    end

    test "the default strategy order starts with the portfolio strategies" do
      names = Enum.map(Schedule.strategies(), & &1.name)
      defaults = Enum.map(Portfolio.default_strategies(), &elem(&1, 0))

      assert Enum.take(names, 4) == defaults
      assert length(names) == length(Enum.uniq(names))
      assert :fluid in names and :induction in names
    end

    test "the wide portfolio extends the defaults up to 16 distinct strategies" do
      wide = Portfolio.wide_strategies()
      names = Enum.map(wide, &elem(&1, 0))

      assert length(wide) == 16
      assert names == Enum.uniq(names)
      assert Enum.take(wide, 4) == Portfolio.default_strategies()
      assert Portfolio.wide_strategies(6) == Enum.take(wide, 6)
      assert Keyword.get(Map.new(wide)[:fluid], :fluid_sup)
      assert Keyword.get(Map.new(wide)[:induction], :induction)
    end

    test "slices fit the timeout and run at most `cores` strategies" do
      for timeout <- [500, 2_500, 60_000, 300_000], cores <- [1, 4, 14] do
        slices = Schedule.build(timeout, cores)

        assert slices != []
        assert Enum.sum(Enum.map(slices, & &1.timeout_ms)) <= timeout
        assert Enum.all?(slices, &(length(&1.strategies) in 1..cores))
      end

      # Too little time for a full slice: the first slice gets everything.
      assert [%{timeout_ms: 2_500, strategies: first}] = Schedule.build(2_500, 4)

      assert Enum.map(first, &elem(&1, 0)) ==
               Enum.map(Portfolio.default_strategies(), &elem(&1, 0))

      # Remaining time is spread over the slices that fit.
      assert [%{timeout_ms: a}, %{timeout_ms: b}] =
               Schedule.build(25_000, 2, Enum.take(Schedule.strategies(), 4))

      assert a + b == 25_000
    end

    test "the schedule moves on to the next slice until one answers" do
      {:ok, lowered} = TptpLower.from_string(@thm_src)

      hopeless = %{name: :hopeless, share: 1, opts: [max_iterations: 0]}
      [good | _] = Schedule.strategies()

      result =
        Schedule.prove_lowered(lowered,
          timeout_ms: 3_000,
          cores: 1,
          schedule_strategies: [hopeless, good]
        )

      assert {:proved, _steps, stats} = result
      assert stats.winning_strategy == good.name
    end

    test "strategy overrides reach every strategy" do
      {:ok, lowered} = TptpLower.from_string(@thm_src)

      assert {:resource_out, _stats} =
               Schedule.prove_lowered(lowered,
                 timeout_ms: 2_000,
                 cores: 4,
                 schedule_strategies: Enum.take(Schedule.strategies(), 4),
                 strategy_overrides: [max_iterations: 0]
               )
    end
  end

  describe "command line" do
    test "parses Leo-III style options" do
      params = CLI.parse(~w(p.p -t 30 -p --atp e=/bin/e --atp vampire=/bin/v --sos --unidepth 4))

      assert params.problem == "p.p"
      assert params["t"] == ["30"]
      assert params["p"] == []
      assert params["atp"] == ["e=/bin/e", "vampire=/bin/v"]
      assert params["sos"] == []
      assert params["unidepth"] == ["4"]

      # Switches do not swallow the problem; combined short switches are split.
      assert %{"p" => [], "s" => [], problem: "p.p"} = CLI.parse(~w(-ps p.p))
    end

    test "prints the SZS status and the proof", %{dir: dir} do
      path = write_problem(dir, "thm.p", @thm_src)

      out = capture_io(fn -> assert CLI.run([path, "-t", "5", "-p"]) == 0 end)

      assert out =~ "% SZS status Theorem for #{path}"
      assert out =~ "% SZS output start CNFRefutation for #{path}"
      assert out =~ "% SZS output end CNFRefutation for #{path}"
      assert out =~ "file('#{path}', conj_qg)"

      out = capture_io(fn -> CLI.run([path, "-t", "5"]) end)
      assert out =~ "% SZS status Theorem"
      refute out =~ "SZS output"
    end

    test "never claims a theorem it cannot prove", %{dir: dir} do
      # First-order and saturated without limits, so the model answer is justified.
      path = write_problem(dir, "csa.p", @csa_src)
      out = capture_io(fn -> CLI.run([path, "-t", "2", "-n", "2"]) end)

      assert out =~ "% SZS status CounterSatisfiable for"
      refute out =~ "Theorem"

      # Higher-order saturation is never complete, so no model answer either.
      path = write_problem(dir, "ho_open.p", @ho_open_src)
      out = capture_io(fn -> CLI.run([path, "-t", "2", "-n", "2"]) end)

      assert out =~ ~r/% SZS status (GaveUp|Timeout) for/
    end

    test "--consistency-only ignores the conjecture", %{dir: dir} do
      path = write_problem(dir, "cax.p", @cax_src)
      out = capture_io(fn -> CLI.run([path, "-t", "5", "--consistency-only"]) end)
      assert out =~ "% SZS status Unsatisfiable for"

      path = write_problem(dir, "thm.p", @thm_src)
      out = capture_io(fn -> CLI.run([path, "-t", "2", "--consistency-only"]) end)
      refute out =~ "Theorem"
    end

    test "reports usage and input errors as SZS statuses with exit code 0", %{dir: dir} do
      out = capture_io(fn -> assert CLI.run([]) == 0 end)
      assert out =~ "% SZS status UsageError for <unknown>"
      assert out =~ "Usage: astraea problem"

      out = capture_io(fn -> assert CLI.run([Path.join(dir, "missing.p")]) == 0 end)
      assert out =~ "% SZS status InputError for"

      path = write_problem(dir, "thm.p", @thm_src)
      out = capture_io(fn -> CLI.run([path, "-t", "x"]) end)
      assert out =~ "% SZS status UsageError for"

      out = capture_io(fn -> CLI.run([path, "-t", "2", "--strategies", "nope"]) end)
      assert out =~ "Unknown strategies: nope"
    end

    test "warns about unknown and unsupported options", %{dir: dir} do
      path = write_problem(dir, "thm.p", @thm_src)

      out =
        capture_io(fn ->
          CLI.run([path, "-t", "2", "--relevancefiltering", "--frobnicate", "--atp", "nope=/x"])
        end)

      assert out =~ "% Warning: Option 'relevancefiltering' is not supported"
      assert out =~ "% Warning: Unknown option 'frobnicate' ignored"
      assert out =~ "% Warning: Unknown external prover 'nope' ignored"
      assert out =~ "% SZS status Theorem"
    end

    test "unverified external answers need --trust-external", %{dir: dir} do
      path = write_problem(dir, "ho_open.p", @ho_open_src)
      oracle = Path.join(dir, "oracle")
      File.write!(oracle, "#!/bin/sh\necho '% SZS status Theorem'\n")
      File.chmod!(oracle, 0o755)
      args = [path, "-t", "3", "-n", "2", "--atp", "e=#{oracle}", "--atp-race"]

      out = capture_io(fn -> CLI.run(args) end)
      assert out =~ ~r/% SZS status (GaveUp|Timeout) for/

      out = capture_io(fn -> CLI.run(args ++ ["--trust-external"]) end)
      assert out =~ "% SZS status Theorem for"
    end
  end
end
