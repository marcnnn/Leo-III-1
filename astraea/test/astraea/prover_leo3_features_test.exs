defmodule Astraea.ProverLeo3FeaturesTest do
  use ExUnit.Case, async: true

  alias Astraea.{Arena, ProofChecker, Prover, Schedule, TptpLower}
  alias Astraea.Calculus.{DomainConstraint, Injectivity}

  defp prove(src, opts) do
    Prover.prove_string(src, Keyword.merge([timeout_ms: 1_500], opts))
  end

  defp fvars(arena, n) do
    Enum.map_reduce(1..n, arena, fn i, ar ->
      {ar, v} = Arena.mk_fvar(ar, i, :i)
      {v, ar}
    end)
  end

  defp assert_kernel_proof(result) do
    assert {:proved, steps, stats} = result
    assert :ok == ProofChecker.verify_refutation(stats.arena, steps)
    steps
  end

  describe "set of support (Leo-III sos)" do
    @sos_thm """
    thf(p_t, type, p: $o). thf(q_t, type, q: $o). thf(r_t, type, r: $o).
    thf(a1, axiom, p). thf(a2, axiom, p => q). thf(a3, axiom, q => r).
    thf(c, conjecture, r).
    """

    @sos_csa """
    thf(p_t, type, p: $i > $o). thf(a_t, type, a: $i).
    thf(ax, axiom, p @ a). thf(c, conjecture, ! [X: $i]: (p @ X)).
    """

    test "proves through the conjecture and passes the kernel" do
      assert_kernel_proof(prove(@sos_thm, sos: true))
    end

    test "marks the run incomplete, so a saturation is no model answer" do
      assert {:saturated, stats} = prove(@sos_csa, sos: true)
      assert :sos in stats.incomplete_reasons
      assert {:saturated, %{complete: true}} = prove(@sos_csa, [])
    end

    test "only conjecture clauses are in the set of support" do
      {:ok, lowered} = TptpLower.from_string(@sos_thm)
      # Without the conjecture the axioms alone do not refute, and nothing is marked.
      no_conj = %{lowered | conjectures: []}
      assert {:saturated, stats} = Prover.prove_lowered(no_conj, sos: true)
      refute :sos in stats.incomplete_reasons
    end
  end

  describe "domain constraints (Leo-III domConstr)" do
    @dom_thm """
    thf(a_t, type, a: $i). thf(b_t, type, b: $i). thf(p_t, type, p: $i > $o).
    thf(d, axiom, ! [X: $i]: ((X = a) | (X = b))).
    thf(pa, axiom, p @ a). thf(pb, axiom, p @ b).
    thf(c, conjecture, ! [X: $i]: (p @ X)).
    """

    @dom_csa """
    thf(a_t, type, a: $i). thf(b_t, type, b: $i). thf(p_t, type, p: $i > $o).
    thf(d, axiom, ! [X: $i]: ((X = a) | (X = b))).
    thf(pa, axiom, p @ a).
    thf(c, conjecture, ! [X: $i]: (p @ X)).
    """

    test "instantiates constrained variables by kernel-checked substitutions" do
      result = prove(@dom_thm, dom_constr: -1)
      assert_kernel_proof(result)
      assert elem(result, 2).domain_instances > 0
    end

    test "does not refute a satisfiable problem" do
      refute match?({:proved, _, _}, prove(@dom_csa, dom_constr: -1, max_iterations: 300))
    end

    test "detection needs positive literals with one variable and closed terms" do
      arena = Arena.new()
      {arena, a} = Arena.mk_const(arena, "a", :i)
      {arena, b} = Arena.mk_const(arena, "b", :i)
      {arena, x} = Arena.mk_fvar(arena, 1, :i)
      {arena, xa} = Arena.mk_eq(arena, x, a)
      {arena, bx} = Arena.mk_eq(arena, b, x)
      ty = Arena.type_of(arena, x)

      assert {:ok, ^ty, terms} =
               DomainConstraint.detect(arena, MapSet.new([{:pos, xa}, {:pos, bx}]))

      assert Enum.sort(terms) == Enum.sort([a, b])
      assert :none == DomainConstraint.detect(arena, MapSet.new([{:neg, xa}, {:neg, bx}]))
    end

    test "a positive bound stops before exceeding the number of instances" do
      fvars = MapSet.new([{1, 7}, {2, 7}])
      domains = %{7 => [10, 11]}
      assert length(DomainConstraint.substitutions(fvars, domains, -1)) == 4
      assert length(DomainConstraint.substitutions(fvars, domains, 3)) == 2
      assert DomainConstraint.substitutions(fvars, domains, 0) == []
    end
  end

  describe "injectivity (Leo-III detectInjectivity / InverseFunction)" do
    @inj_unary """
    thf(f_t, type, f: $i > $i).
    thf(inj, axiom, ! [X: $i, Y: $i]: (((f @ X) = (f @ Y)) => (X = Y))).
    thf(c, conjecture, ? [G: $i > $i]: ! [X: $i]: ((G @ (f @ X)) = X)).
    """

    @inj_binary """
    thf(f_t, type, f: $i > $i > $i).
    thf(inj, axiom,
      ! [X1: $i, X2: $i, Y1: $i, Y2: $i]: (((f @ X1 @ X2) = (f @ Y1 @ Y2)) => (X2 = Y2))).
    thf(c, conjecture, ? [G: $i > $i > $i]: ! [X: $i, Y: $i]: ((G @ X @ (f @ X @ Y)) = Y)).
    """

    @inj_csa """
    thf(f_t, type, f: $i > $i). thf(a_t, type, a: $i).
    thf(inj, axiom, ! [X: $i, Y: $i]: (((f @ X) = (f @ Y)) => (X = Y))).
    thf(c, conjecture, ? [X: $i]: ((f @ X) = a)).
    """

    test "the inverse of a unary injective function is derived through choice" do
      steps = assert_kernel_proof(prove(@inj_unary, injectivity: true))
      assert Enum.any?(steps, &match?({:choice, _, _, _}, &1))
      refute match?({:proved, _, _}, prove(@inj_unary, max_iterations: 200))
    end

    test "injectivity in one argument of a binary function" do
      assert_kernel_proof(prove(@inj_binary, injectivity: true))
    end

    test "injectivity does not make a function surjective" do
      refute match?(
               {:proved, _, _},
               prove(@inj_csa, injectivity: true, max_iterations: 200, timeout_ms: 1_500)
             )
    end

    test "detection reads the injective argument position" do
      arena = Arena.new()
      {arena, ty} = Arena.intern_type(arena, {:arrow, :i, {:arrow, :i, :i}})
      {arena, f} = Arena.mk_const(arena, "f", ty)
      {[x1, x2, y1, y2], arena} = fvars(arena, 4)
      {arena, fx} = Astraea.Calculus.Terms.mk_apps(arena, f, [x1, x2])
      {arena, fy} = Astraea.Calculus.Terms.mk_apps(arena, f, [y1, y2])
      {arena, neg} = Arena.mk_eq(arena, fx, fy)
      {arena, pos} = Arena.mk_eq(arena, y2, x2)

      assert {:ok, %{head: ^f, index: 1}} =
               Injectivity.detect(arena, MapSet.new([{:neg, neg}, {:pos, pos}]))

      {arena, pos1} = Arena.mk_eq(arena, x1, y2)
      assert :none == Injectivity.detect(arena, MapSet.new([{:neg, neg}, {:pos, pos1}]))
    end
  end

  test "the Leo-III schedule passes sos, domConstr and injectivity to the prover" do
    s3 = Enum.find(Schedule.leo3_strategies(), &(&1.name == :s3))
    s5a = Enum.find(Schedule.leo3_strategies(), &(&1.name == :s5a))
    assert Schedule.leo3_opts(s3.params)[:sos] == true
    assert Schedule.leo3_opts(s5a.params)[:dom_constr] == -1
    assert Schedule.leo3_opts(s3.params)[:injectivity] == true
  end
end
