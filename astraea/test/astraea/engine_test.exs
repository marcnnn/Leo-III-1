defmodule Astraea.EngineTest do
  use ExUnit.Case, async: true
  use ExUnitProperties

  alias Astraea.{Arena, NxKernel, ProofChecker, Prover}
  alias Astraea.Engine.{Demodulator, FVIndex, HeadIndex, Kernels, PassiveQueue, Subsumption}
  alias Astraea.Calculus.Terms

  # ---------------------------------------------------------------------------
  # Feature-vector index: every backend against the plain-Elixir reference
  # ---------------------------------------------------------------------------

  defp fv_gen, do: map(list_of(integer(0..6), length: 16), &FVIndex.fv/1)

  defp reference(entries, fv, :subsumers),
    do: for({id, row} <- entries, FVIndex.le?(row, fv), do: id)

  defp reference(entries, fv, :subsumed),
    do: for({id, row} <- entries, FVIndex.le?(fv, row), do: id)

  defp soa(fvs) do
    fvs
    |> Enum.map(&Tuple.to_list/1)
    |> Nx.tensor(type: :u16)
    |> Nx.transpose()
  end

  property "defn kernels agree with the reference lane test" do
    check all(
            fvs <- list_of(fv_gen(), min_length: 1, max_length: 40),
            queries <- list_of(fv_gen(), min_length: 1, max_length: 5)
          ) do
      block = soa(fvs)
      entries = Enum.with_index(fvs, fn fv, i -> {i, fv} end)

      for q <- queries, dir <- [:subsumers, :subsumed] do
        q_t = Nx.tensor(Tuple.to_list(q), type: :u16)
        mask = apply(Kernels, dir, [q_t, block]) |> Nx.to_flat_list()
        found = for {1, i} <- Enum.with_index(mask), do: i
        assert found == reference(entries, q, dir)
      end

      batch = apply(Kernels, :subsumers_batch, [soa(queries), block]) |> Nx.to_list()

      for {row, q} <- Enum.zip(batch, queries) do
        assert for({1, i} <- Enum.with_index(row), do: i) == reference(entries, q, :subsumers)
      end
    end
  end

  # Inserts and deletes enough entries to seal and merge segments.
  property "incremental index answers like a linear scan, through seals and deletions" do
    check all(
            n <- member_of([7, 300, 1_024, 1_700, 2_600]),
            fvs <- list_of(fv_gen(), length: n),
            dead <- list_of(integer(0..2_599), max_length: 400),
            queries <- list_of(fv_gen(), min_length: 1, max_length: 6),
            max_runs: 15
          ) do
      entries = Enum.with_index(fvs, fn fv, i -> {i, fv} end)
      dead = MapSet.new(dead)
      live = Enum.reject(entries, &MapSet.member?(dead, elem(&1, 0)))

      index =
        Enum.reduce(entries, FVIndex.new(backend: :elixir), fn {id, fv}, idx ->
          idx = FVIndex.insert(idx, id, fv)
          # Interleave deletions with insertions.
          if rem(id, 7) == 0, do: FVIndex.delete(idx, Enum.filter(dead, &(&1 <= id))), else: idx
        end)
        |> FVIndex.delete(dead)

      assert FVIndex.size(index) == length(live)
      if n >= 1_024, do: assert(index.segments != [])

      for dir <- [:subsumers, :subsumed] do
        batch = apply(FVIndex, :"#{dir}_batch", [index, queries])

        for {q, got} <- Enum.zip(queries, batch) do
          assert Enum.sort(got) == Enum.sort(reference(live, q, dir))
          assert Enum.sort(apply(FVIndex, dir, [index, q])) == Enum.sort(got)
        end
      end
    end
  end

  @tag :nx_simd
  test "NxSimd-compiled kernels agree with the defn reference" do
    if NxKernel.available?() do
      fvs = for i <- 1..1_024, do: FVIndex.fv(for(l <- 0..15, do: rem(i * (l + 3), 7)))
      q = Nx.tensor(List.duplicate(4, 16), type: :u16)
      block = soa(fvs)

      for dir <- [:subsumers, :subsumed] do
        compiled = Kernels.compile_kernel(dir, [{16}, {16, 1_024}])
        assert Nx.to_binary(compiled.(q, block)) == Nx.to_binary(apply(Kernels, dir, [q, block]))
      end
    end
  end

  # ---------------------------------------------------------------------------
  # Passive queue
  # ---------------------------------------------------------------------------

  property "passive queue follows the pick ratio and the priority orders" do
    check all(
            scores <- list_of(integer(0..50), min_length: 1, max_length: 60),
            removed <- list_of(integer(1..60), max_length: 10)
          ) do
      items = Enum.with_index(scores, 1) |> Enum.map(fn {s, id} -> %{id: id, score: s} end)
      q = Enum.reduce(items, PassiveQueue.new(score: 2, age: 1), &PassiveQueue.insert(&2, &1))
      q = PassiveQueue.delete(q, removed)
      live = Enum.reject(items, &(&1.id in removed))
      assert PassiveQueue.size(q) == length(live)

      {popped, _} =
        Enum.map_reduce(1..length(live)//1, {q, live}, fn n, {q, left} ->
          {item, q} = PassiveQueue.pop(q)

          expected =
            if rem(n, 3) == 0,
              do: Enum.min_by(left, & &1.id),
              else: Enum.min_by(left, &{&1.score, -&1.id})

          assert item == expected
          {item, {q, List.delete(left, item)}}
        end)

      assert Enum.sort_by(popped, & &1.id) == live
    end
  end

  # ---------------------------------------------------------------------------
  # Subsumption & demodulation on small first-order clause sets
  # ---------------------------------------------------------------------------

  defp signature do
    arena = Arena.new()
    {arena, ii} = Arena.intern_type(arena, {:arrow, :i, :i})
    {arena, iii} = Arena.intern_type(arena, {:arrow, :i, ii})
    {arena, io} = Arena.intern_type(arena, {:arrow, :i, :o})
    {arena, a} = Arena.mk_const(arena, "a", :i)
    {arena, b} = Arena.mk_const(arena, "b", :i)
    {arena, f} = Arena.mk_const(arena, "f", ii)
    {arena, g} = Arena.mk_const(arena, "g", iii)
    {arena, p} = Arena.mk_const(arena, "p", io)
    {arena, x} = Arena.mk_fvar(arena, 1, :i)
    {arena, y} = Arena.mk_fvar(arena, 2, :i)
    {arena, %{a: a, b: b, f: f, g: g, p: p, x: x, y: y}}
  end

  defp term_gen(depth) do
    leaf = member_of([:a, :b, :x, :y])

    if depth == 0,
      do: leaf,
      else:
        one_of([
          leaf,
          map(term_gen(depth - 1), &{:f, &1}),
          map({term_gen(depth - 1), term_gen(depth - 1)}, fn {l, r} -> {:g, l, r} end)
        ])
  end

  defp build(arena, s, sym) when is_atom(sym), do: {arena, Map.fetch!(s, sym)}

  defp build(arena, s, {:f, t}) do
    {arena, t} = build(arena, s, t)
    Arena.mk_app(arena, s.f, t)
  end

  defp build(arena, s, {:g, l, r}) do
    {arena, l} = build(arena, s, l)
    {arena, r} = build(arena, s, r)
    {arena, gl} = Arena.mk_app(arena, s.g, l)
    Arena.mk_app(arena, gl, r)
  end

  defp lit_gen do
    one_of([
      map({member_of([:pos, :neg]), term_gen(2)}, fn {pol, t} -> {pol, {:p, t}} end),
      map({member_of([:pos, :neg]), term_gen(2), term_gen(2)}, fn {pol, l, r} ->
        {pol, {:eq, l, r}}
      end)
    ])
  end

  defp build_lit(arena, s, {pol, {:p, t}}) do
    {arena, t} = build(arena, s, t)
    {arena, atom} = Arena.mk_app(arena, s.p, t)
    {arena, {pol, atom}}
  end

  defp build_lit(arena, s, {pol, {:eq, l, r}}) do
    {arena, l} = build(arena, s, l)
    {arena, r} = build(arena, s, r)
    {arena, atom} = Arena.mk_eq(arena, l, r)
    {arena, {pol, atom}}
  end

  defp item(arena, lits, id) do
    lits = MapSet.new(lits)
    %{id: id, lits: lits, sfv: Subsumption.clause_fv(arena, lits)}
  end

  property "subsumption implies feature-vector dominance and holds for instances" do
    {arena0, s} = signature()

    check all(
            c_lits <- list_of(lit_gen(), min_length: 1, max_length: 3),
            extra <- list_of(lit_gen(), max_length: 2),
            inst_x <- term_gen(1),
            other <- list_of(lit_gen(), min_length: 1, max_length: 3)
          ) do
      {c, arena} = Enum.map_reduce(c_lits, arena0, &swap(build_lit(&2, s, &1)))
      {e, arena} = Enum.map_reduce(extra, arena, &swap(build_lit(&2, s, &1)))
      {o, arena} = Enum.map_reduce(other, arena, &swap(build_lit(&2, s, &1)))
      {arena, xi} = build(arena, s, inst_x)

      # d = c[X := t] plus extra literals, which c subsumes unless the instance
      # merged literals of the set c (multiset subsumption needs an injection).
      {d, arena} =
        Enum.map_reduce(c, arena, fn {pol, atom}, ar ->
          {ar, atom} = Arena.subst_fvar(ar, atom, %{1 => xi})
          {{pol, atom}, ar}
        end)

      c_item = item(arena, c, 1)
      d_item = item(arena, d ++ e, 2)

      if MapSet.size(MapSet.new(d)) == MapSet.size(c_item.lits) do
        assert Subsumption.subsumes?(arena, c_item, d_item)
      end

      o_item = item(arena, o, 3)

      for {x, y} <- [{c_item, d_item}, {c_item, o_item}, {o_item, c_item}],
          Subsumption.subsumes?(arena, x, y) do
        assert FVIndex.le?(x.sfv, y.sfv)
        assert MapSet.size(x.lits) <= MapSet.size(y.lits)
      end
    end
  end

  defp swap({a, b}), do: {b, a}

  test "multiset subsumption needs an injective literal mapping" do
    {arena, s} = signature()
    {arena, {_, px}} = build_lit(arena, s, {:pos, {:p, :x}})
    {arena, {_, py}} = build_lit(arena, s, {:pos, {:p, :y}})
    {arena, {_, pa}} = build_lit(arena, s, {:pos, {:p, :a}})

    two = item(arena, [{:pos, px}, {:pos, py}], 1)
    one = item(arena, [{:pos, pa}], 2)
    refute Subsumption.subsumes?(arena, two, one)
    assert Subsumption.subsumes?(arena, item(arena, [{:pos, px}], 3), one)
  end

  test "demodulation finds KBO-decreasing redexes only" do
    {arena, s} = signature()
    # f(f(X)) = X orients left to right.
    {arena, ffx} = build(arena, s, {:f, {:f, :x}})
    {arena, rule_eq} = Arena.mk_eq(arena, ffx, s.x)
    rule = %{id: 1, lits: MapSet.new([{:pos, rule_eq}]), fvar_ids: MapSet.new([1])}
    assert [%{lhs: ^ffx}] = rules = Demodulator.rules(arena, rule)
    index = Demodulator.add_rules(HeadIndex.new(), arena, rules)

    {arena, {_, target}} = build_lit(arena, s, {:neg, {:p, {:f, {:f, {:f, :a}}}}})
    d = %{id: 2, lits: MapSet.new([{:neg, target}]), fvar_ids: MapSet.new()}
    assert {:ok, arena, redex} = Demodulator.find_redex(arena, index, d)
    {_arena, fa} = build(arena, s, {:f, :a})
    assert redex.to == fa

    {arena, {_, plain}} = build_lit(arena, s, {:pos, {:p, {:f, :a}}})

    assert {:none, _} =
             Demodulator.find_redex(arena, index, %{d | lits: MapSet.new([{:pos, plain}])})
  end

  # ---------------------------------------------------------------------------
  # End to end: verified proofs with redundancy elimination, completeness flag
  # ---------------------------------------------------------------------------

  @rewrite_src """
  thf(f_type, type, f: $i > $i).
  thf(p_type, type, p: $i > $o).
  thf(a_type, type, a: $i).
  thf(ax_inv, axiom, ! [X: $i]: ((f @ (f @ X)) = X)).
  thf(ax_p, axiom, p @ a).
  thf(conj, conjecture, p @ (f @ (f @ (f @ (f @ a))))).
  """

  test "demodulation yields a kernel-verified refutation" do
    assert {:proved, steps, stats} = Prover.prove_string(@rewrite_src)
    assert stats.rewrites > 0
    assert :demodulation in stats.incomplete_reasons
    assert :ok == ProofChecker.verify_refutation(stats.arena, steps)
  end

  test "redundancy elimination can be switched off without losing the proof" do
    opts = [demodulation: false, backward_subsumption: false, index_backend: :elixir]
    assert {:proved, steps, stats} = Prover.prove_string(@rewrite_src, opts)
    assert stats.rewrites == 0
    assert :ok == ProofChecker.verify_refutation(stats.arena, steps)
  end

  @arith_src """
  tff(p_type, type, p: $int > $o).
  tff(q_type, type, q: $int > $o).
  tff(ax1, axiom, ! [X: $int]: (p(X) => q($sum(X, 1)))).
  tff(ax2, axiom, p(2)).
  tff(conj, conjecture, q(3)).
  """

  test "ground arithmetic is evaluated during search with an :arith_eval step" do
    assert {:proved, steps, stats} = Prover.prove_string(@arith_src)
    assert Enum.any?(steps, &match?({:arith_eval, _, _, _}, &1))
    assert :ok == ProofChecker.verify_refutation(stats.arena, steps)
  end

  @sat_src """
  thf(p_type, type, p: $i > $o).
  thf(q_type, type, q: $i > $o).
  thf(a_type, type, a: $i).
  thf(ax1, axiom, ! [X: $i]: ((p @ X) => (q @ X))).
  thf(ax2, axiom, p @ a).
  thf(conj, conjecture, ~ (q @ a)).
  """

  test "a saturation without limits is complete, one with limits is not" do
    assert {:saturated, stats} = Prover.prove_string(@sat_src)
    assert stats.complete
    assert stats.incomplete_reasons == []

    assert {:saturated, capped} = Prover.prove_string(@sat_src, max_clause_lits: 1)
    refute capped.complete
    assert :clause_lits_limit in capped.incomplete_reasons
  end

  @boolean_src """
  thf(a_const, type, a: $o).
  thf(b_const, type, b: $o).
  thf(p_const, type, p: $o > $o).
  thf(thm, conjecture, ((p @ a) & (p @ b)) => (p @ (a & b))).
  """

  # A theorem the calculus cannot refute (it needs Boolean extensionality): its
  # saturation must not count as a model.
  test "a higher-order saturation is never complete" do
    case Prover.prove_string(@boolean_src, timeout_ms: 1_000) do
      {:saturated, stats} -> assert :higher_order in stats.incomplete_reasons
      {tag, _} -> assert tag == :resource_out
      {:proved, _, _} -> :ok
    end
  end
  test "Boolean unit demodulation indexes non-equational units and rewrites subterms" do
    {arena, s} = signature()
    # Positive unit: p(a)
    {arena, pa} = Arena.mk_app(arena, s.p, s.a)
    unit_pos = %{id: 1, lits: MapSet.new([{:pos, pa}]), fvar_ids: MapSet.new()}
    assert [%{lhs: ^pa, rhs: true_const}] = Demodulator.rules(arena, unit_pos)
    assert Terms.const_named?(arena, true_const, "$true")

    # Negative unit: p(b)
    {arena, pb} = Arena.mk_app(arena, s.p, s.b)
    unit_neg = %{id: 2, lits: MapSet.new([{:neg, pb}]), fvar_ids: MapSet.new()}
    assert [%{lhs: ^pb, rhs: false_const}] = Demodulator.rules(arena, unit_neg)
    assert Terms.const_named?(arena, false_const, "$false")

    index =
      HeadIndex.new()
      |> Demodulator.add_rules(arena, Demodulator.rules(arena, unit_pos))
      |> Demodulator.add_rules(arena, Demodulator.rules(arena, unit_neg))

    # Target clause: holds(p(a) => q)
    {arena, q} = Arena.mk_const(arena, "q", :o)
    {arena, imp} = Arena.mk_imp(arena, pa, q)
    {arena, h_ty} = Arena.intern_type(arena, {:arrow, Arena.ty_o(), Arena.ty_o()})
    {arena, holds} = Arena.mk_const(arena, "holds", h_ty)
    {arena, target_atom} = Arena.mk_app(arena, holds, imp)

    target_clause = %{id: 3, lits: MapSet.new([{:pos, target_atom}]), fvar_ids: MapSet.new()}

    # Should find redex p(a) inside holds(p(a) => q)
    assert {:ok, arena, redex} = Demodulator.find_redex(arena, index, target_clause)
    assert redex.from == pa
    assert redex.to == true_const

    # When replaced and beta-eta normalized, holds($true => q) simplifies to holds(q)
    {arena, replaced} = ProofChecker.replace_subterm(arena, target_atom, redex.from, redex.to)
    {_arena, norm} = Arena.beta_eta_norm(arena, replaced)
    {_arena, expected} = Arena.mk_app(arena, holds, q)
    assert norm == expected
  end
end
