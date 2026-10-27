defmodule Astraea.CalculusTest do
  use ExUnit.Case, async: true
  use ExUnitProperties

  alias Astraea.{Arena, ProofChecker, Prover}
  alias Astraea.Calculus.{Choice, Cnf, FingerprintIndex, Ordering, PrimSubst, Terms, Unify}

  # ---------------------------------------------------------------------------
  # Random terms over a small higher-order signature:
  #   a, b : $i      f : $i > $i      g : $i > $i > $i
  #   X, Y : $i      F, G : $i > $i   (free variables, F and G give flex heads)
  # ---------------------------------------------------------------------------

  defp signature do
    arena = Arena.new()
    {arena, ii} = Arena.intern_type(arena, {:arrow, :i, :i})
    {arena, iii} = Arena.intern_type(arena, {:arrow, :i, ii})
    {arena, a} = Arena.mk_const(arena, "a", :i)
    {arena, b} = Arena.mk_const(arena, "b", :i)
    {arena, f} = Arena.mk_const(arena, "f", ii)
    {arena, g} = Arena.mk_const(arena, "g", iii)
    {arena, x} = Arena.mk_fvar(arena, 1, :i)
    {arena, y} = Arena.mk_fvar(arena, 2, :i)
    {arena, ff} = Arena.mk_fvar(arena, 3, ii)
    {arena, gg} = Arena.mk_fvar(arena, 4, ii)
    {arena, %{a: a, b: b, f: f, g: g, x: x, y: y, F: ff, G: gg}}
  end

  defp term_spec do
    leaf = member_of([:a, :b, :x, :y])

    tree(leaf, fn child ->
      one_of([
        tuple({constant(:f), child}),
        tuple({constant(:g), child, child}),
        tuple({constant(:F), child}),
        tuple({constant(:G), child})
      ])
    end)
  end

  defp build(arena, sig, leaf) when is_atom(leaf), do: {arena, Map.fetch!(sig, leaf)}

  defp build(arena, sig, {head, arg}) do
    {arena, t} = build(arena, sig, arg)
    Arena.mk_app(arena, Map.fetch!(sig, head), t)
  end

  defp build(arena, sig, {:g, l, r}) do
    {arena, tl} = build(arena, sig, l)
    {arena, tr} = build(arena, sig, r)
    {arena, gl} = Arena.mk_app(arena, sig.g, tl)
    Arena.mk_app(arena, gl, tr)
  end

  defp instantiate(arena, term, subst) do
    Arena.subst_fvar(arena, term, subst)
  end

  # ---------------------------------------------------------------------------
  # Pre-unification
  # ---------------------------------------------------------------------------

  property "every returned pre-unifier unifies the pair" do
    check all(s_spec <- term_spec(), t_spec <- term_spec(), max_runs: 300) do
      {arena, sig} = signature()
      {arena, s} = build(arena, sig, s_spec)
      {arena, t} = build(arena, sig, t_spec)

      {arena, _nf, unifiers, _cut} =
        Unify.unifiers(arena, [{s, t}], 100, max_depth: 3, max_unifiers: 4)

      for subst <- unifiers do
        {arena, s1} = instantiate(arena, s, subst)
        {_arena, t1} = instantiate(arena, t, subst)
        assert s1 == t1
      end
    end
  end

  property "the fingerprint filter accepts every pair the unifier solves" do
    check all(s_spec <- term_spec(), t_spec <- term_spec(), max_runs: 300) do
      {arena, sig} = signature()
      {arena, s} = build(arena, sig, s_spec)
      {arena, t} = build(arena, sig, t_spec)
      {arena, _nf, unifiers, _cut} = Unify.unifiers(arena, [{s, t}], 100, max_depth: 3)

      if unifiers != [] do
        fs = FingerprintIndex.fingerprint(arena, s)
        ft = FingerprintIndex.fingerprint(arena, t)
        assert FingerprintIndex.compatible?(:unify, fs, ft)
        assert FingerprintIndex.compatible?(:unify, ft, fs)

        {index, _slot} = FingerprintIndex.insert(FingerprintIndex.new(), arena, t, :target)
        assert [[:target]] == FingerprintIndex.query(index, [fs], :unify, backend: :elixir)
      end
    end
  end

  property "the matching filter accepts every instance of a pattern" do
    check all(s_spec <- term_spec(), t_spec <- term_spec(), max_runs: 200) do
      {arena, sig} = signature()
      {arena, s} = build(arena, sig, s_spec)
      {arena, t} = build(arena, sig, t_spec)
      {arena, inst} = instantiate(arena, s, %{1 => t, 3 => sig.f})

      assert FingerprintIndex.compatible?(
               :match,
               FingerprintIndex.fingerprint(arena, s),
               FingerprintIndex.fingerprint(arena, inst)
             )
    end
  end

  # Pattern fragment reference: `^ [xs]: F @ xs = ^ [xs]: t` has the unique most general
  # unifier `F := ^ [xs]: t` whenever `F` does not occur in `t`.
  property "pattern problems get exactly their most general unifier" do
    check all(spec <- pattern_body_spec(), n <- integer(1..2), max_runs: 200) do
      arena = Arena.new()
      {arena, ii} = Arena.intern_type(arena, {:arrow, :i, :i})
      {arena, f} = Arena.mk_const(arena, "f", ii)
      {arena, c} = Arena.mk_const(arena, "c", :i)
      {arena, h} = Arena.mk_fvar(arena, 7, :i)
      taus = List.duplicate(Arena.ty_i(), n)
      {arena, fty} = Terms.mk_arrows(arena, taus, Arena.ty_i())
      {arena, ff} = Arena.mk_fvar(arena, 9, fty)
      {arena, xs} = Terms.bound_args(arena, taus)
      {arena, body} = build_pattern_body(arena, %{f: f, c: c, h: h}, xs, spec)
      {arena, lhs_body} = Terms.mk_apps(arena, ff, xs)
      {arena, lhs} = Terms.mk_lams(arena, taus, lhs_body)
      {arena, rhs} = Terms.mk_lams(arena, taus, body)
      {arena, lhs} = Arena.beta_eta_norm(arena, lhs)
      {arena, rhs} = Arena.beta_eta_norm(arena, rhs)

      {arena, _nf, unifiers, cutoffs} = Unify.unifiers(arena, [{lhs, rhs}], 100)
      assert cutoffs == 0
      assert [subst] = unifiers
      assert Map.keys(subst) == [9]
      {arena, bound} = Arena.beta_eta_norm(arena, subst[9])
      assert bound == rhs
      {_arena, applied} = instantiate(arena, lhs, subst)
      assert applied == rhs
    end
  end

  defp pattern_body_spec do
    tree(member_of([:c, :h, {:x, 0}, {:x, 1}]), fn child -> tuple({constant(:f), child}) end)
  end

  defp build_pattern_body(arena, sig, _xs, :c), do: {arena, sig.c}
  defp build_pattern_body(arena, sig, _xs, :h), do: {arena, sig.h}

  defp build_pattern_body(arena, _sig, xs, {:x, j}),
    do: {arena, Enum.at(xs, min(j, length(xs) - 1))}

  defp build_pattern_body(arena, sig, xs, {:f, child}) do
    {arena, t} = build_pattern_body(arena, sig, xs, child)
    Arena.mk_app(arena, sig.f, t)
  end

  test "imitation and projection enumerate several unifiers; occurs check fails" do
    {arena, sig} = signature()
    {arena, fa} = Arena.mk_app(arena, sig[:F], sig.a)
    {arena, ffa} = Arena.mk_app(arena, sig.f, sig.a)

    {arena, _nf, unifiers, _cut} =
      Unify.unifiers(arena, [{fa, ffa}], 100, max_depth: 3, max_unifiers: 8)

    # F := ^[x]: f a,  F := ^[x]: f x  (plus nothing else)
    assert length(unifiers) == 2

    {arena, fx} = Arena.mk_app(arena, sig.f, sig.x)
    assert {_, _, [], 0} = Unify.unifiers(arena, [{sig.x, fx}], 100)
  end

  test "partial bindings and primitive substitution templates are well typed" do
    {arena, sig} = signature()
    {arena, io} = Arena.intern_type(arena, {:arrow, :i, :o})
    {arena, p} = Arena.mk_fvar(arena, 20, io)
    {arena, pa} = Arena.mk_app(arena, p, sig.a)
    lits = MapSet.new([{:pos, pa}])

    assert [{20, ^io}] = PrimSubst.head_vars(arena, lits)

    for level <- 1..3 do
      {arena, _nf, substs} = PrimSubst.substitutions(arena, lits, 100, level)
      assert length(substs) >= 4

      for subst <- substs do
        {arena, inst} = Arena.subst_fvar(arena, pa, subst)
        assert Arena.type_of(arena, inst) == Arena.ty_o()
      end
    end
  end

  test "literal eligibility respects KBO maximality and negative selection" do
    {arena, sig} = signature()
    {arena, io} = Arena.intern_type(arena, {:arrow, :i, :o})
    {arena, p} = Arena.mk_const(arena, "p", io)
    {arena, fa} = Arena.mk_app(arena, sig.f, sig.a)
    {arena, pa} = Arena.mk_app(arena, p, sig.a)
    {arena, pfa} = Arena.mk_app(arena, p, fa)
    lits = MapSet.new([{:pos, pa}, {:pos, pfa}, {:neg, pa}])

    assert Ordering.eligible(arena, lits, %{ordered: true, select: :none}) ==
             MapSet.new([{:pos, pfa}])

    assert Ordering.eligible(arena, lits, %{ordered: false, select: :neg_max}) ==
             MapSet.new([{:neg, pa}])
  end

  # ---------------------------------------------------------------------------
  # Kernel: `:cnf` and `:choice` rules accept sound steps and reject forgeries
  # ---------------------------------------------------------------------------

  defp prop_sig do
    arena = Arena.new()
    {arena, io} = Arena.intern_type(arena, {:arrow, :i, :o})
    {arena, p} = Arena.mk_const(arena, "p", io)
    {arena, q} = Arena.mk_const(arena, "q", io)
    {arena, a} = Arena.mk_const(arena, "a", :i)
    {arena, pa} = Arena.mk_app(arena, p, a)
    {arena, qa} = Arena.mk_app(arena, q, a)
    {arena, %{p: p, q: q, a: a, pa: pa, qa: qa, io: io}}
  end

  test "kernel :cnf expands connectives, quantifiers and truth constants" do
    {arena, s} = prop_sig()
    {arena, or_pq} = Arena.mk_or(arena, s.pa, s.qa)
    {arena, x0} = Arena.mk_bvar(arena, 0, :i)
    {arena, px} = Arena.mk_app(arena, s.p, x0)
    {arena, all_p} = Arena.mk_forall(arena, :i, px)

    # p(a) | q(a),  ~p(a),  ~q(a)  refuted through `:or`
    proof = [
      {:axiom, 1, MapSet.new([{:pos, or_pq}])},
      {:axiom, 2, MapSet.new([{:neg, s.pa}])},
      {:axiom, 3, MapSet.new([{:neg, s.qa}])},
      {:cnf, 4, 1, {:pos, or_pq}, :or},
      {:resolve, 5, 4, 2, {:pos, s.pa}},
      {:resolve, 6, 5, 3, {:pos, s.qa}}
    ]

    assert :ok == ProofChecker.verify_refutation(arena, proof)

    # ! [X]: p(X)  and  ~p(a)  refuted through `{:forall, X}` + `:subst`
    {arena, x} = Arena.mk_fvar(arena, 5, :i)
    {arena, px_free} = Arena.mk_app(arena, s.p, x)

    proof = [
      {:axiom, 1, MapSet.new([{:pos, all_p}])},
      {:axiom, 2, MapSet.new([{:neg, s.pa}])},
      {:cnf, 3, 1, {:pos, all_p}, {:forall, 5}},
      {:subst, 4, 3, %{5 => s.a}},
      {:resolve, 5, 4, 2, {:pos, s.pa}}
    ]

    assert :ok == ProofChecker.verify_refutation(arena, proof)

    assert {:ok, _, [{:pos, ^px_free}]} =
             ProofChecker.expand_literal(arena, {:pos, all_p}, {:forall, 5})

    # ~$true is dropped, $false is dropped
    {arena, truth} = Arena.mk_const(arena, "$true", :o)
    {arena, falsum} = Arena.mk_const(arena, "$false", :o)

    proof = [
      {:axiom, 1, MapSet.new([{:neg, truth}, {:pos, falsum}])},
      {:cnf, 2, 1, {:neg, truth}, :truth},
      {:cnf, 3, 2, {:pos, falsum}, :truth}
    ]

    assert :ok == ProofChecker.verify_refutation(arena, proof)
  end

  test "kernel rejects forged :cnf, :choice and Skolem steps" do
    {arena, s} = prop_sig()
    {arena, or_pq} = Arena.mk_or(arena, s.pa, s.qa)
    {arena, truth} = Arena.mk_const(arena, "$true", :o)
    {arena, eq_ia} = Arena.mk_eq(arena, s.a, s.a)

    forged = [
      # picking one disjunct of a *positive* disjunction is unsound
      {:cnf, 2, 1, {:pos, or_pq}, {:or, :left}},
      # `$true` is not removable from a positive literal
      {:cnf, 2, 1, {:pos, truth}, :truth},
      # Boolean extensionality only applies to equations at `$o`
      {:cnf, 2, 1, {:pos, eq_ia}, {:bool_eq, :left}},
      # functional extensionality needs an arrow type
      {:cnf, 2, 1, {:pos, eq_ia}, :ext},
      # positive literals are not Skolemized
      {:cnf, 2, 1, {:pos, or_pq}, :skolem},
      # the literal must belong to the parent clause
      {:cnf, 2, 1, {:pos, s.qa}, :not}
    ]

    parent = MapSet.new([{:pos, or_pq}, {:pos, truth}, {:pos, eq_ia}])

    for step <- forged do
      assert {:error, {:invalid_cnf, 2, 1, _}} =
               ProofChecker.verify_refutation(arena, [{:axiom, 1, parent}, step])
    end

    # choice instances need a closed predicate `T > $o`
    assert {:error, {:invalid_choice, 1, _}} =
             ProofChecker.verify_refutation(arena, [{:choice, 1, s.a, 3}])

    # a hand-made Skolem constant is not the kernel's witness for `~ ! [X]: p(X)`
    {arena, x0} = Arena.mk_bvar(arena, 0, :i)
    {arena, px} = Arena.mk_app(arena, s.p, x0)
    {arena, all_p} = Arena.mk_forall(arena, :i, px)

    {:ok, arena2, [{:neg, witness_lit}]} =
      ProofChecker.expand_literal(arena, {:neg, all_p}, :skolem)

    assert witness_lit != s.pa

    proof = [
      {:axiom, 1, MapSet.new([{:neg, all_p}])},
      {:axiom, 2, MapSet.new([{:pos, s.pa}])},
      {:cnf, 3, 1, {:neg, all_p}, :skolem},
      {:resolve, 4, 2, 3, {:pos, s.pa}}
    ]

    assert {:error, {:invalid_resolve, 4, 2, 3, _}} =
             ProofChecker.verify_refutation(arena2, proof)
  end

  test "Cnf expansion trees replay as kernel steps" do
    {arena, s} = prop_sig()
    {arena, neg_q} = Arena.mk_not(arena, s.qa)
    {arena, or_pq} = Arena.mk_or(arena, s.pa, neg_q)
    {arena, not_or} = Arena.mk_not(arena, or_pq)
    lits = MapSet.new([{:pos, not_or}])

    {_arena, _nf, tree, 0} = Cnf.expand(arena, lits, 50)
    assert Cnf.leaves(tree, lits) == [MapSet.new([{:neg, s.pa}]), MapSet.new([{:pos, s.qa}])]
  end

  # ---------------------------------------------------------------------------
  # End-to-end refutations through the prover (LCF verified)
  # ---------------------------------------------------------------------------

  defp kinds(steps), do: steps |> Enum.map(&elem(&1, 0)) |> MapSet.new()

  test "Huet imitation solves an existential function goal" do
    src = """
    thf(a_type, type, a: $i).
    thf(b_type, type, b: $i).
    thf(conj, conjecture, ? [F: $i > $i]: ((F @ a) = b)).
    """

    assert {:proved, _steps, stats} = Prover.prove_string(src, timeout_ms: 2_000)
    assert is_integer(stats.unification_cutoffs)
  end

  test "primitive substitution plus search-time clausification" do
    src = """
    thf(a_type, type, a: $i).
    thf(conj, conjecture, ? [P: $i > $o]: ! [X: $i]: (P @ X)).
    """

    assert {:proved, steps, _} = Prover.prove_string(src, timeout_ms: 2_000)
    assert :cnf in kinds(steps)
  end

  test "search-time functional and Boolean extensionality" do
    arena = Arena.new()
    {arena, ii} = Arena.intern_type(arena, {:arrow, :i, :i})
    {arena, f} = Arena.mk_const(arena, "f", ii)
    {arena, g} = Arena.mk_const(arena, "g", ii)
    {arena, x} = Arena.mk_fvar(arena, 1, :i)
    {arena, fx} = Arena.mk_app(arena, f, x)
    {arena, gx} = Arena.mk_app(arena, g, x)
    {arena, eq_x} = Arena.mk_eq(arena, fx, gx)
    {arena, eq_fg} = Arena.mk_eq(arena, f, g)

    clauses = [MapSet.new([{:pos, eq_x}]), MapSet.new([{:neg, eq_fg}])]
    assert {:proved, steps, _} = Prover.prove_clauses(arena, clauses, timeout_ms: 2_000)
    assert :cnf in kinds(steps)

    {arena, s} = prop_sig()
    {arena, bool_eq} = Arena.mk_eq(arena, s.pa, s.qa)

    clauses = [
      MapSet.new([{:neg, bool_eq}]),
      MapSet.new([{:pos, s.pa}]),
      MapSet.new([{:pos, s.qa}])
    ]

    assert {:proved, steps, _} = Prover.prove_clauses(arena, clauses, timeout_ms: 2_000)
    assert :cnf in kinds(steps)
  end

  test "Hilbert choice instances" do
    {arena, s} = prop_sig()
    {arena, choice} = Arena.mk_const(arena, "$choice", {:arrow, s.io, :i})
    {arena, eps_p} = Arena.mk_app(arena, choice, s.p)
    {arena, p_eps} = Arena.mk_app(arena, s.p, eps_p)

    # p(a), ~p($choice @ p)
    clauses = [MapSet.new([{:pos, s.pa}]), MapSet.new([{:neg, p_eps}])]
    assert {:proved, steps, _} = Prover.prove_clauses(arena, clauses, timeout_ms: 2_000)
    assert :choice in kinds(steps)

    assert {:saturated, _} =
             Prover.prove_clauses(arena, clauses, timeout_ms: 1_000, choice: false)
  end

  test "user-defined choice axiom detection and instantiation" do
    {arena, s} = prop_sig()
    # Define a choice operator constant: eps: (i > $o) > i
    {arena, eps} = Arena.mk_const(arena, "eps", {:arrow, s.io, :i})

    # Choice axiom: ~ (P @ X) | P @ (eps @ P)
    # P: i > $o (fvar 10), X: i (fvar 11)
    {arena, p_var} = Arena.mk_fvar(arena, 10, s.io)
    {arena, x_var} = Arena.mk_fvar(arena, 11, :i)
    {arena, px} = Arena.mk_app(arena, p_var, x_var)
    {arena, eps_p} = Arena.mk_app(arena, eps, p_var)
    {arena, p_eps} = Arena.mk_app(arena, p_var, eps_p)

    choice_ax = MapSet.new([{:neg, px}, {:pos, p_eps}])

    assert {:ok, info} = Choice.detect_axiom(arena, choice_ax)
    assert info.choice_head == eps
    assert info.pred_fvar_id == 10
    assert info.witness_fvar_id == 11

    # Goal: p(a), ~ p(eps @ p), plus choice axiom
    {arena, eps_sp} = Arena.mk_app(arena, eps, s.p)
    {arena, sp_eps} = Arena.mk_app(arena, s.p, eps_sp)

    clauses = [choice_ax, MapSet.new([{:pos, s.pa}]), MapSet.new([{:neg, sp_eps}])]

    assert {:proved, steps, _} = Prover.prove_clauses(arena, clauses, timeout_ms: 2_000)
    assert :subst in kinds(steps)
  end

  test "soundness trap: an invalid higher-order goal is not proved" do
    src = """
    thf(a_type, type, a: $i).
    thf(b_type, type, b: $i).
    thf(p_type, type, p: $i > $o).
    thf(conj, conjecture, ! [F: $i > $i]: ((F @ a) = b)).
    """

    refute match?({:proved, _, _}, Prover.prove_string(src, timeout_ms: 1_000))
  end

  test "trivial Boolean equivalences clausify instead of looping" do
    # `A <=> A` used to be rewritten into `$true <=> $true` and then into itself forever.
    assert {:proved, _, _} =
             Prover.prove_string("thf(p_t, type, p: $o).\nthf(c, conjecture, p <=> p).",
               timeout_ms: 1_000
             )

    assert {:proved, _, _} =
             Prover.prove_string(
               """
               thf(p_t, type, p: $i > $o).
               thf(q_t, type, q: $o).
               thf(c, conjecture, ! [X: $i]: (((p @ X) & q) <=> (q & (p @ X)))).
               """,
               timeout_ms: 1_000
             )

    refute match?(
             {:proved, _, _},
             Prover.prove_string(
               "thf(p_t, type, p: $o).\nthf(ax, axiom, p <=> p).\nthf(c, conjecture, p).",
               timeout_ms: 1_000
             )
           )
  end
end
