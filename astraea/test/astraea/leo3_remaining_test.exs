defmodule Astraea.Leo3RemainingTest do
  @moduledoc """
  The kernel's type check on substitutions, Leo-III's subsumption methods and
  `--print-clauses`, the axiom counts for Leo-III's SInE table, and the command
  line flags `--sine`, `--standard-sine`, `--subsumption`, `--embedding-param`,
  `--print-clauses` and `--guided`.
  """
  use ExUnit.Case, async: true

  import ExUnit.CaptureIO

  alias Astraea.{Arena, CLI, ProofChecker, Prover, TptpLower}
  alias Astraea.Engine.Subsumption

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

  setup do
    dir =
      Path.join(
        System.tmp_dir!(),
        "astraea_leo3_remaining_test_#{System.unique_integer([:positive])}"
      )

    File.mkdir_p!(dir)
    on_exit(fn -> File.rm_rf!(dir) end)
    %{dir: dir}
  end

  defp write_problem(dir, source) do
    path = Path.join(dir, "thm.p")
    File.write!(path, source)
    path
  end

  defp p_of_x do
    arena = Arena.new()
    {arena, i} = Arena.intern_type(arena, :i)
    {arena, pt} = Arena.intern_type(arena, {:arrow, i, Arena.ty_o()})
    {arena, p} = Arena.mk_const(arena, "p", pt)
    {arena, x} = Arena.mk_fvar(arena, 1, i)
    {arena, px} = Arena.mk_app(arena, p, x)
    %{arena: arena, i: i, p: p, x: x, px: px}
  end

  describe "kernel substitution" do
    test "accepts a well-typed instance and rejects an ill-typed one" do
      %{arena: arena, i: i, p: p, px: px} = p_of_x()
      {arena, a} = Arena.mk_const(arena, "a", i)
      {arena, b} = Arena.mk_const(arena, "b", Arena.ty_o())
      axiom = {:axiom, 1, MapSet.new([{:pos, px}])}

      assert {:ok, ar, derived} =
               ProofChecker.derive_steps(arena, [axiom, {:subst, 2, 1, %{1 => a}}])

      {_ar, pa} = Arena.mk_app(ar, p, a)
      assert derived[2] == MapSet.new([{:pos, pa}])

      assert {:error, {:invalid_subst, 2, 1}} =
               ProofChecker.derive_steps(arena, [axiom, {:subst, 2, 1, %{1 => b}}])
    end

    test "checks variables that only occur inside other replacements" do
      %{arena: arena, i: i, p: p, px: px} = p_of_x()
      {arena, f} = Arena.mk_const(arena, "f", {:arrow, i, i})
      {arena, y} = Arena.mk_fvar(arena, 2, i)
      {arena, fy} = Arena.mk_app(arena, f, y)
      {arena, b} = Arena.mk_const(arena, "b", Arena.ty_o())
      _ = p

      axiom = {:axiom, 1, MapSet.new([{:pos, px}])}

      assert {:error, _} =
               ProofChecker.derive_steps(arena, [axiom, {:subst, 2, 1, %{1 => fy, 2 => b}}])
    end
  end

  describe "subsumption methods" do
    test "trivial subsumption only accepts literal inclusion" do
      %{arena: arena, i: i, p: p, px: px} = p_of_x()
      {arena, a} = Arena.mk_const(arena, "a", i)
      {arena, pa} = Arena.mk_app(arena, p, a)
      general = %{lits: MapSet.new([{:pos, px}])}
      instance = %{lits: MapSet.new([{:pos, pa}])}

      assert Subsumption.subsumes?(arena, general, instance)
      refute Subsumption.subsumes?(arena, general, instance, :trivial)
      assert Subsumption.subsumes?(arena, instance, instance, :trivial)
    end

    test "the prover finds verified proofs with either method" do
      for method <- [:matching, :trivial] do
        assert {:proved, steps, stats} = Prover.prove_string(@thm_src, subsumption: method)
        assert :ok = ProofChecker.verify_refutation(stats.arena, steps)
      end
    end
  end

  test "keep_clauses reports the active clauses at termination" do
    src = "thf(p_type, type, p: $o).\nthf(ax, axiom, p).\nthf(c, conjecture, ~ p)."
    assert {:saturated, stats} = Prover.prove_string(src, keep_clauses: true)
    assert %Arena{} = stats.arena
    assert [_ | _] = stats.final_clauses
  end

  test "lowering records the axioms of the problem file and of its includes", %{dir: dir} do
    ax = Path.join(dir, "ax.ax")
    File.write!(ax, "thf(p_type, type, p: $o).\nthf(ax1, axiom, p).\nthf(ax2, axiom, ~ ~ p).\n")
    path = write_problem(dir, "include('ax.ax').\nthf(ax3, axiom, p).\nthf(c, conjecture, p).\n")

    assert {:ok, lowered} = TptpLower.from_file(path, tptp_root: dir)
    assert lowered.axiom_counts == {1, 2}
  end

  describe "command line" do
    test "SInE, subsumption, embedding parameters and --print-clauses", %{dir: dir} do
      path = write_problem(dir, @thm_src)

      out =
        capture_io(fn ->
          CLI.run([
            path,
            "-t",
            "5",
            "--sine",
            "1.5;100;3",
            "--standard-sine",
            "--subsumption",
            "trivial",
            "--embedding-param",
            "MODALITIES_SYNTACTICAL",
            "--print-clauses"
          ])
        end)

      refute out =~ "Warning"
      assert out =~ "% SZS status Theorem"
      assert out =~ "% Processed clauses at termination:"
    end

    test "unknown embedding parameters are usage errors", %{dir: dir} do
      path = write_problem(dir, @thm_src)
      out = capture_io(fn -> CLI.run([path, "--embedding-param", "FOO"]) end)
      assert out =~ "% SZS status UsageError"
      assert out =~ "FOO"
    end

    test "--guided reads commands from stdin and kill reports User", %{dir: dir} do
      path = write_problem(dir, @thm_src)

      out = capture_io("processed\nkill\n", fn -> CLI.run([path, "--guided"]) end)
      assert out =~ "% SZS status User"

      out = capture_io("exit\n", fn -> CLI.run([path, "--guided"]) end)
      assert out =~ "% SZS status Theorem"
    end
  end

  describe "ordering checks after unification" do
    test "ordered proofs stay verified with and without Leo-III's checks" do
      for skip <- [[], [1, 2, 3]], ord <- [:kbo, :cpo] do
        assert {:proved, steps, stats} =
                 Prover.prove_string(@thm_src,
                   ordered: true,
                   term_ordering: ord,
                   no_ord_check: skip
                 )

        assert :ok = ProofChecker.verify_refutation(stats.arena, steps)
      end
    end
  end

  describe "more command line flags" do
    test "--no-default-types rejects undeclared symbols in THF", %{dir: dir} do
      path = write_problem(dir, "thf(ax, axiom, p).\nthf(c, conjecture, p).\n")
      assert capture_io(fn -> CLI.run([path, "-t", "2"]) end) =~ "% SZS status Theorem"

      out = capture_io(fn -> CLI.run([path, "-t", "2", "--no-default-types"]) end)
      assert out =~ "% SZS status InputError"
      assert out =~ "unknown type"
    end

    test "--DEBUG prints the proof as internal clauses", %{dir: dir} do
      path = write_problem(dir, @thm_src)

      out =
        capture_io(fn ->
          CLI.run([path, "-t", "5", "-p", "--DEBUG", "--noOrdCheck1", "--noOrdCheck3"])
        end)

      refute out =~ "Warning"
      refute out =~ "SZS output start CNFRefutation"
      assert out =~ ~r/% \d+: .* <- axiom\(\)/
      assert out =~ ~r/% \d+: \$false <- resolve\(\d+, \d+\)/
    end

    test "atpdebug prints the external prover call", %{dir: dir} do
      prover = Path.join(dir, "fake_prover")
      File.write!(prover, "#!/bin/sh\necho \"% SZS status GaveUp for $1\"\n")
      File.chmod!(prover, 0o755)
      spec = %{name: :fake, executables: [prover], formats: [:thf], args: fn _l, f -> [f] end}
      problem = write_problem(dir, @thm_src)

      out =
        capture_io(fn ->
          assert {:ok, %{status: :gave_up}} =
                   Astraea.External.run(spec, problem, debug: true, process_group: false)
        end)

      assert out =~ "% [atpdebug] #{prover} #{problem}"
      assert out =~ "% [atpdebug] | % SZS status GaveUp"
      assert out =~ "% [atpdebug] fake: exit 0"
    end
  end
end
