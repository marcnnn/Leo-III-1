defmodule Astraea.Leo3WiringTest do
  @moduledoc """
  Leo-III features reached through the prover options and the command line:
  clausifier options forwarded by `Astraea.Prover.prove_lowered/2`, the CPO term
  ordering in demodulation, set instantiation, and the Leo-III modes and flags of
  `Astraea.CLI`.
  """
  use ExUnit.Case, async: true

  import ExUnit.CaptureIO

  alias Astraea.{Arena, CLI, Clausifier, ProofChecker, Prover, TptpLower}
  alias Astraea.Engine.Demodulator

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

  # Needs the instance `S := s` of an axiom over sets of properties.
  @sets_src """
  thf(s_type, type, s: ($i > $o) > $o).
  thf(p_type, type, p: $i > $o).
  thf(t_type, type, t: (($i > $o) > $o) > $o).
  thf(ax_all, axiom, ! [S: ($i > $o) > $o]: ((S @ p) => (t @ S))).
  thf(ax_s, axiom, s @ p).
  thf(conj, conjecture, t @ s).
  """

  setup do
    dir =
      Path.join(
        System.tmp_dir!(),
        "astraea_leo3_wiring_test_#{System.unique_integer([:positive])}"
      )

    File.mkdir_p!(dir)
    on_exit(fn -> File.rm_rf!(dir) end)
    %{dir: dir}
  end

  defp write_problem(dir, name, source) do
    path = Path.join(dir, name)
    File.write!(path, source)
    path
  end

  defp assert_verified({:proved, steps, stats}) do
    assert :ok = ProofChecker.verify_refutation(stats.arena, steps)
  end

  describe "prover options forwarded to the clausifier" do
    test "renaming, equality rewrites and the relevance filter keep proofs verified" do
      for opts <- [
            [renaming: true, renaming_threshold: 0],
            [leibniz_eq: false, andrews_eq: false],
            [instantiate_sets: true],
            [relevance_filter: %{passmark: 0.1, aging: 2.35}]
          ] do
        assert {:proved, _, _} = result = Prover.prove_string(@thm_src, opts)
        assert_verified(result)
      end
    end

    test "axioms dropped by the relevance filter make a saturation incomplete" do
      assert {:saturated, stats} =
               Prover.prove_string(@thm_src, relevance_filter: %{passmark: 0.99, aging: 2.35})

      assert :sine in stats.incomplete_reasons
    end
  end

  describe "set instantiation" do
    test "adds the instances of an axiom over sets of properties next to it" do
      {:ok, lowered} = TptpLower.from_string(@sets_src)
      {_arena, plain} = Clausifier.clausify(lowered, sine_limit: nil)
      {arena, inst} = Clausifier.clausify(lowered, sine_limit: nil, instantiate_sets: true)

      assert length(inst) == length(plain) + 1

      # The instance `~ (s @ p) | t @ s`, with no variables left.
      assert Enum.any?(inst, fn clause ->
               MapSet.size(clause) == 2 and
                 Enum.all?(clause, fn {_pol, atom} -> Enum.empty?(Arena.free_vars(arena, atom)) end)
             end)

      assert {:proved, _, _} = result = Prover.prove_string(@sets_src, instantiate_sets: true)
      assert_verified(result)
    end
  end

  describe "CPO term ordering" do
    test "demodulation rules keep the ordering they were oriented with" do
      arena = Arena.new()
      {arena, i} = Arena.intern_type(arena, :i)
      {arena, fi} = Arena.intern_type(arena, {:arrow, i, i})
      {arena, f} = Arena.mk_const(arena, "f", fi)
      {arena, a} = Arena.mk_const(arena, "a", i)
      {arena, fa} = Arena.mk_app(arena, f, a)
      {arena, eq} = Arena.mk_eq(arena, fa, a)
      item = %{id: 1, lits: MapSet.new([{:pos, eq}])}

      for ord <- [:kbo, :cpo] do
        assert [%{lhs: ^fa, rhs: ^a, ordering: ^ord}] =
                 Demodulator.rules(arena, item, term_ordering: ord)
      end
    end

    test "Leo-III's CPO strategies prove an equational theorem with verified proofs" do
      assert {:proved, _, _} =
               result = Prover.prove_string(@thm_src, ordered: true, term_ordering: :cpo)

      assert_verified(result)
    end
  end

  describe "command line" do
    test "Leo-III calculus flags are accepted and the proof is printed", %{dir: dir} do
      path = write_problem(dir, "thm.p", @thm_src)

      out =
        capture_io(fn ->
          CLI.run([
            path,
            "-t",
            "5",
            "-p",
            "--seq",
            "--renaming",
            "0",
            "--ordering",
            "CPO",
            "--naeq",
            "--nleq",
            "--acsimp",
            "--instantiate",
            "59",
            "--instantiate-maxdepth",
            "3",
            "--instantiate-sets",
            "--relevancefiltering",
            "--passmark",
            "0.5",
            "--lambda-elim",
            "ski",
            "--atp-max-jobs",
            "2",
            "--print-signature"
          ])
        end)

      refute out =~ "Warning"
      assert out =~ "% SZS status Theorem"
      assert out =~ "% SZS output start CNFRefutation"
      assert out =~ "% Signature:"
      assert out =~ "%   g: ($i > $i)"
    end

    test "bad flag values are usage errors", %{dir: dir} do
      path = write_problem(dir, "thm.p", @thm_src)

      for flag <- [["--ordering", "LPO"], ["--passmark", "x"], ["--lambda-elim", "foo"]] do
        out = capture_io(fn -> CLI.run([path | flag]) end)
        assert out =~ "% SZS status UsageError"
      end
    end

    test "--processOnly prints the normalized problem", %{dir: dir} do
      path = write_problem(dir, "thm.p", @thm_src)
      out = capture_io(fn -> CLI.run([path, "--processOnly", "--cnf", "--xType", "0"]) end)

      refute out =~ "SZS status"
      assert {:proved, _, _} = Prover.prove_string(out)
    end

    test "--toTHF, --syntaxcheck and --typecheck report Success", %{dir: dir} do
      path = write_problem(dir, "thm.p", @thm_src)

      out = capture_io(fn -> CLI.run([path, "--toTHF"]) end)
      assert out =~ "% SZS status Success"
      assert out =~ "% SZS output start ListOfTHF"

      for mode <- ["--syntaxcheck", "--typecheck"] do
        assert capture_io(fn -> CLI.run([path, mode]) end) =~ "% SZS status Success"
      end

      bad = write_problem(dir, "bad.p", "thf(x, axiom, (.")
      refute capture_io(fn -> CLI.run([bad, "--syntaxcheck"]) end) =~ "Success"
    end
  end
end
