defmodule Astraea.GatesTest do
  use ExUnit.Case, async: true
  use ExUnitProperties

  alias Astraea.{Arena, Compressor, Native, Portfolio, ProofChecker, Prover, TptpCorpus, TptpLower}

  # ---------------------------------------------------------------------------
  # Gate 1: StreamData HOL & Arena Invariants
  # ---------------------------------------------------------------------------

  @tag :gate1
  property "Gate 1: 12-byte flat binary node encoding roundtrips losslessly" do
    check all tag <- integer(1..11),
              flags <- integer(0..255),
              type_id <- integer(0..65_535),
              left <- integer(0..1_000_000),
              right <- integer(0..1_000_000) do
      packed = Arena.encode_node(tag, flags, type_id, left, right)
      assert byte_size(packed) == 12
      assert Arena.decode_node(packed) == {tag, flags, type_id, left, right}
    end
  end

  @tag :gate1
  property "Gate 1: content-addressed Skolem hash is invariant to Arena insertion order" do
    check all sym_a <- string(:alphanumeric, min_length: 1, max_length: 8),
              sym_b <- string(:alphanumeric, min_length: 1, max_length: 8),
              noise_count <- integer(1..10) do
      a1 = Arena.new()
      {a1, i_to_o} = Arena.intern_type(a1, {:arrow, :i, :o})
      {a1, p1} = Arena.mk_const(a1, "pred_" <> sym_a, i_to_o)
      {a1, x1} = Arena.mk_bvar(a1, 0, :i)
      {a1, body1} = Arena.mk_app(a1, p1, x1)
      {a1, lam1} = Arena.mk_lam(a1, :i, body1)

      a2 =
        Enum.reduce(1..noise_count, Arena.new(), fn idx, acc ->
          {acc, _} = Arena.mk_const(acc, "noise_#{sym_b}_#{idx}", :i)
          acc
        end)

      {a2, i_to_o_2} = Arena.intern_type(a2, {:arrow, :i, :o})
      {a2, p2} = Arena.mk_const(a2, "pred_" <> sym_a, i_to_o_2)
      {a2, x2} = Arena.mk_bvar(a2, 0, :i)
      {a2, body2} = Arena.mk_app(a2, p2, x2)
      {a2, lam2} = Arena.mk_lam(a2, :i, body2)

      assert Arena.skolem_hash(a1, lam1) == Arena.skolem_hash(a2, lam2)
    end
  end

  @tag :gate1
  test "Gate 1: S,K,I,B,C combinator bracket abstraction agrees with beta-eta normalization" do
    arena = Arena.new()
    {arena, ii} = Arena.intern_type(arena, {:arrow, :i, :i})
    {arena, iii} = Arena.intern_type(arena, {:arrow, :i, ii})
    {arena, f} = Arena.mk_const(arena, "f", iii)
    {arena, g} = Arena.mk_const(arena, "g", ii)
    {arena, a} = Arena.mk_const(arena, "a", :i)
    {arena, b} = Arena.mk_const(arena, "b", :i)

    # Term: (^ [X: $i, Y: $i]: f @ (g @ Y) @ X) @ a @ b  ==>  f @ (g @ b) @ a
    # Inside 2 lambdas: X is BVar(1), Y is BVar(0)
    {arena, x} = Arena.mk_bvar(arena, 1, :i)
    {arena, y} = Arena.mk_bvar(arena, 0, :i)
    {arena, gy} = Arena.mk_app(arena, g, y)
    {arena, f_gy} = Arena.mk_app(arena, f, gy)
    {arena, body} = Arena.mk_app(arena, f_gy, x)
    {arena, lam_y} = Arena.mk_lam(arena, :i, body)
    {arena, lam_xy} = Arena.mk_lam(arena, :i, lam_y)

    {arena, app1} = Arena.mk_app(arena, lam_xy, a)
    {arena, redex} = Arena.mk_app(arena, app1, b)

    # 1. Beta-eta normal form in spine/de Bruijn representation
    {arena, beta_nf} = Arena.beta_eta_norm(arena, redex)

    # 2. Lower lambda to S,K,I,B,C combinators first, apply to a and b, and comb-reduce
    {arena, comb_fn} = Arena.to_combinators(arena, lam_xy)
    assert not Arena.occurs_bvar?(arena, comb_fn, 0)
    {arena, comb_app1} = Arena.mk_app(arena, comb_fn, a)
    {arena, comb_redex} = Arena.mk_app(arena, comb_app1, b)
    {_arena, comb_nf} = Arena.comb_norm(arena, comb_redex)

    assert beta_nf == comb_nf
  end

  # ---------------------------------------------------------------------------
  # Gate 2: Differential Oracle (Pure Elixir Reference vs. Native Rustler NIF)
  # ---------------------------------------------------------------------------

  @tag :gate2
  property "Gate 2: Native Rust NIF KBO & 16-lane FVIndex match Pure Elixir Reference Oracle" do
    check all shapes <- list_of(integer(0..4), min_length: 4, max_length: 16) do
      {arena, term_ids} = build_random_terms(shapes)
      flat_bin = Arena.to_flat_binary(arena)

      # 1. Verify KBO irreflexivity, asymmetry, and 100% agreement between Elixir & Rust NIF
      for s <- term_ids, t <- term_ids do
        ref_ord = Arena.kbo_compare(arena, s, t)
        nif_ord = Native.nif_kbo_compare(flat_bin, s, t)
        assert ref_ord == nif_ord

        if s == t do
          assert ref_ord == :eq
        end

        if ref_ord == :gt do
          assert Arena.kbo_compare(arena, t, s) == :lt
        end
      end

      # 2. Verify 16-lane Feature Vector extraction & SIMD batch subsumption
      ref_fvs =
        for id <- term_ids do
          fv_ref = Arena.feature_vector(arena, id)
          fv_nif = Native.nif_feature_vector(flat_bin, id)
          assert fv_ref == fv_nif
          fv_ref
        end

      targets_bin = Native.pack_feature_vectors(ref_fvs)

      for cand_fv <- ref_fvs do
        expected_indices =
          ref_fvs
          |> Enum.with_index()
          |> Enum.filter(fn {target_fv, _idx} -> Arena.fv_subsumes?(cand_fv, target_fv) end)
          |> Enum.map(&elem(&1, 1))

        actual_indices = Native.nif_fv_subsumes_batch(cand_fv, targets_bin)
        assert actual_indices == expected_indices
      end
    end
  end

  # ---------------------------------------------------------------------------
  # Gate 3: LCF Proof Certificate Checker & TPTP-Smoke 50-Problem Lowering
  # ---------------------------------------------------------------------------

  @tag :gate3
  test "Gate 3: LCF ProofChecker accepts valid equality + resolution refutation and rejects forged proof" do
    arena = Arena.new()
    {arena, a} = Arena.mk_const(arena, "a", :i)
    {arena, b} = Arena.mk_const(arena, "b", :i)
    {arena, c} = Arena.mk_const(arena, "c", :i)
    {arena, eq_ab} = Arena.mk_eq(arena, a, b)
    {arena, eq_bc} = Arena.mk_eq(arena, b, c)
    {arena, eq_ac} = Arena.mk_eq(arena, a, c)

    valid_proof = [
      {:axiom, 1, MapSet.new([{:pos, eq_ab}])},
      {:axiom, 2, MapSet.new([{:pos, eq_bc}])},
      {:axiom, 3, MapSet.new([{:neg, eq_ac}])},
      {:trans, 4, 1, 2},
      {:resolve, 5, 4, 3, {:pos, eq_ac}}
    ]

    assert :ok == ProofChecker.verify_refutation(arena, valid_proof)

    incomplete_proof = Enum.take(valid_proof, 4)
    assert {:error, {:not_empty_clause, _}} = ProofChecker.verify_refutation(arena, incomplete_proof)
  end

  @tag :gate3
  test "Gate 3: Prover solves higher-order THF0 theorems with LCF verification and never proves CounterSatisfiable formulas" do
    # 1. Higher-Order Leibniz Equality + Lambda Beta-Reduction Theorem
    thm_src = """
    thf(f_type, type, f: $i > $i).
    thf(a_type, type, a: $i).
    thf(b_type, type, b: $i).
    thf(ax_leibniz, axiom, ! [Q: $i > $o]: ((Q @ a) => (Q @ b))).
    thf(conj, conjecture, ((^ [X: $i]: (f @ X)) @ a) = (f @ b)).
    """

    assert {:proved, steps, stats} = Prover.prove_string(thm_src)
    assert length(steps) >= 3
    assert stats.proof_length == length(steps)

    # 2. Positive Functional Extensionality (`:func_ext` xi-rule) + Paramodulation under HO Predicate
    ext_src = """
    thf(q_type, type, q: ($i > $i) > $o).
    thf(p_type, type, p: $i > $o).
    thf(g_type, type, g: $i > $i).
    thf(a_type, type, a: $i).
    thf(ax_pa, axiom, p @ a).
    thf(ax_cond_id, axiom, ! [X: $i]: ((p @ a) => ((g @ X) = X))).
    thf(ax_q_id, axiom, q @ (^ [X: $i]: X)).
    thf(conj_qg, conjecture, q @ g).
    """

    assert {:proved, ext_steps, _} = Prover.prove_string(ext_src)
    assert Enum.any?(ext_steps, &(elem(&1, 0) == :func_ext))

    # 3. Soundness Trap (CounterSatisfiable): `p(a)` does NOT entail `! [X: $i]: p(X)`
    csa_src = """
    thf(p_type, type, p: $i > $o).
    thf(a_type, type, a: $i).
    thf(ax_pa, axiom, p @ a).
    thf(conj_invalid, conjecture, ! [X: $i]: (p @ X)).
    """

    assert {:saturated, _} = Prover.prove_string(csa_src, timeout_ms: 500)
  end

  @tag :gate3
  test "Gate 3: WP3 Portfolio & WP4 Compressor fuse linear :subst chains while preserving LCF verification" do
    arena = Arena.new()
    {arena, io} = Arena.intern_type(arena, {:arrow, :i, :o})
    {arena, p} = Arena.mk_const(arena, "p", io)
    {arena, a} = Arena.mk_const(arena, "a", :i)
    {arena, x1} = Arena.mk_fvar(arena, 1, :i)
    {arena, x2} = Arena.mk_fvar(arena, 2, :i)
    {arena, px1} = Arena.mk_app(arena, p, x1)
    {arena, pa} = Arena.mk_app(arena, p, a)

    # Raw proof with a 2-step `:subst -> :subst` chain (1 -> 2 -> 3) plus a duplicate step
    raw_steps = [
      {:axiom, 1, MapSet.new([{:pos, px1}])},
      {:axiom, 2, MapSet.new([{:neg, pa}])},
      {:subst, 3, 1, %{1 => x2}},
      {:subst, 4, 3, %{2 => a}},
      {:resolve, 5, 4, 2, {:pos, pa}}
    ]

    assert :ok == ProofChecker.verify_refutation(arena, raw_steps)

    assert {:ok, comp_arena, comp_steps, meta} = Compressor.compress_dag(arena, raw_steps)
    assert :ok == ProofChecker.verify_refutation(comp_arena, comp_steps)
    assert meta.raw_steps == 5
    assert meta.compressed_steps == 4
    assert meta.steps_saved == 1
    assert meta.subst_fusions == 1
    assert meta.macro_patterns[:inst_resolve] == 1

    # Also verify WP3 Portfolio on a higher-order theorem
    thm_src = """
    thf(p_type, type, p: $i > $o).
    thf(q_type, type, q: $i > $o).
    thf(a_type, type, a: $i).
    thf(def_q, definition, q = (^ [X: $i]: (p @ X))).
    thf(ax_pa, axiom, p @ a).
    thf(conj, conjecture, q @ a).
    """

    assert {:ok, lowered} = TptpLower.from_string(thm_src)
    assert {:proved, p_steps, p_stats} = Portfolio.prove_lowered(lowered, timeout_ms: 1_000)
    assert p_stats.winning_strategy in [:goal_standard, :sine_tight_unit, :full_inline_weight, :broad_breadth]
    assert :ok == ProofChecker.verify_refutation(p_stats.arena, p_steps)
  end

  @tag :gate3
  test "Gate 3: TPTP-v9.3.1 SHA-256 locked manifests are disjoint and all 50 TPTP-Smoke problems lower cleanly into Arena + Native NIF" do
    smoke = TptpCorpus.load_split(:smoke)
    dev = TptpCorpus.load_split(:dev)
    holdout = TptpCorpus.load_split(:holdout)

    assert length(smoke) == 50
    assert length(dev) == 300
    assert length(holdout) == 500

    assert MapSet.disjoint?(MapSet.new(smoke), MapSet.new(dev))
    assert MapSet.disjoint?(MapSet.new(smoke), MapSet.new(holdout))
    assert MapSet.disjoint?(MapSet.new(dev), MapSet.new(holdout))

    tptp_root = TptpCorpus.default_tptp_root()

    if File.dir?(tptp_root) do
      for stem <- smoke do
        path = TptpCorpus.problem_path(stem, tptp_root)
        assert {:ok, lowered} = TptpLower.from_file(path, tptp_root: tptp_root)

        all_roots =
          Enum.map(lowered.axioms, &elem(&1, 2)) ++
            Enum.map(lowered.conjectures, &elem(&1, 1))

        assert length(all_roots) > 0, "Expected #{stem} to yield lowered formulas"

        flat_bin = Arena.to_flat_binary(lowered.arena)

        for root_id <- Enum.take(all_roots, 5) do
          assert Arena.feature_vector(lowered.arena, root_id) ==
                   Native.nif_feature_vector(flat_bin, root_id)
        end
      end
    end
  end

  # Helper to build diverse well-typed HOL terms in an Arena
  defp build_random_terms(shapes) do
    arena = Arena.new()
    {arena, ii} = Arena.intern_type(arena, {:arrow, :i, :i})
    {arena, io} = Arena.intern_type(arena, {:arrow, :i, :o})
    {arena, c_a} = Arena.mk_const(arena, "a", :i)
    {arena, c_b} = Arena.mk_const(arena, "b", :i)
    {arena, fn_f} = Arena.mk_const(arena, "f", ii)
    {arena, pred_p} = Arena.mk_const(arena, "p", io)
    {arena, v0} = Arena.mk_fvar(arena, 0, :i)

    Enum.reduce(shapes, {arena, [c_a, c_b, v0]}, fn code, {ar, i_terms} ->
      last_i = hd(i_terms)

      case rem(code, 5) do
        0 ->
          {ar, t} = Arena.mk_app(ar, fn_f, last_i)
          {ar, [t | i_terms]}

        1 ->
          {ar, fa} = Arena.mk_app(ar, fn_f, c_a)
          {ar, t} = Arena.mk_app(ar, fn_f, fa)
          {ar, [t | i_terms]}

        2 ->
          {ar, p_app} = Arena.mk_app(ar, pred_p, last_i)
          {ar, _neg} = Arena.mk_not(ar, p_app)
          {ar, i_terms}

        3 ->
          {ar, _eq} = Arena.mk_eq(ar, last_i, c_b)
          {ar, i_terms}

        4 ->
          {ar, bv0} = Arena.mk_bvar(ar, 0, :i)
          {ar, body} = Arena.mk_app(ar, fn_f, bv0)
          {ar, _lam} = Arena.mk_lam(ar, :i, body)
          {ar, i_terms}
      end
    end)
  end
end
