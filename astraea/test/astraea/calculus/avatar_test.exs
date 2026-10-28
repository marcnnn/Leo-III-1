defmodule Astraea.Calculus.AvatarTest do
  use ExUnit.Case, async: true
  alias Astraea.Arena
  alias Astraea.Calculus.Avatar

  setup do
    arena = Arena.new()
    {:ok, arena: arena}
  end

  test "splits clause with two ground literals into two independent components", %{arena: arena} do
    {arena, p} = Arena.mk_const(arena, "p", :o)
    {arena, q} = Arena.mk_const(arena, "q", :o)

    lits = MapSet.new([{:pos, p}, {:neg, q}])

    assert Avatar.splittable?(arena, lits)
    comps = Avatar.components(arena, lits)
    assert length(comps) == 2
    assert MapSet.new([{:pos, p}]) in comps
    assert MapSet.new([{:neg, q}]) in comps
  end

  test "does not split clause where all literals share free variable X", %{arena: arena} do
    {arena, p} = Arena.mk_const(arena, "p", {:arrow, :i, :o})
    {arena, q} = Arena.mk_const(arena, "q", {:arrow, :i, :o})
    {arena, x} = Arena.mk_fvar(arena, 10, :i)

    {arena, px} = Arena.mk_app(arena, p, x)
    {arena, qx} = Arena.mk_app(arena, q, x)

    lits = MapSet.new([{:pos, px}, {:neg, qx}])

    refute Avatar.splittable?(arena, lits)
    comps = Avatar.components(arena, lits)
    assert length(comps) == 1
  end

  test "splits mixed clause with one ground literal and two linked variable literals", %{
    arena: arena
  } do
    # C = r(c) | p(X, Y) | q(Y, Z)
    # Ground: r(c)
    # Linked by Y: p(X, Y) and q(Y, Z)
    {arena, r} = Arena.mk_const(arena, "r", {:arrow, :i, :o})
    {arena, c} = Arena.mk_const(arena, "c", :i)
    {arena, rc} = Arena.mk_app(arena, r, c)

    {arena, p} = Arena.mk_const(arena, "p", {:arrow, :i, {:arrow, :i, :o}})
    {arena, q} = Arena.mk_const(arena, "q", {:arrow, :i, {:arrow, :i, :o}})

    {arena, x} = Arena.mk_fvar(arena, 1, :i)
    {arena, y} = Arena.mk_fvar(arena, 2, :i)
    {arena, z} = Arena.mk_fvar(arena, 3, :i)

    {arena, px} = Arena.mk_app(arena, p, x)
    {arena, pxy} = Arena.mk_app(arena, px, y)

    {arena, qy} = Arena.mk_app(arena, q, y)
    {arena, qyz} = Arena.mk_app(arena, qy, z)

    lits = MapSet.new([{:pos, rc}, {:pos, pxy}, {:neg, qyz}])

    assert Avatar.splittable?(arena, lits)
    comps = Avatar.components(arena, lits)
    assert length(comps) == 2

    ground_comp = Enum.find(comps, &(MapSet.size(&1) == 1))
    open_comp = Enum.find(comps, &(MapSet.size(&1) == 2))

    assert ground_comp == MapSet.new([{:pos, rc}])
    assert open_comp == MapSet.new([{:pos, pxy}, {:neg, qyz}])
  end

  test "resolve_propositional_unsat reconstructs valid resolution DAG ending in empty clause", %{
    arena: arena
  } do
    alias Astraea.ProofChecker

    {arena, g1} = Arena.mk_const(arena, "g1", :o)
    {arena, g2} = Arena.mk_const(arena, "g2", :o)

    # Clause 1 (split): g1 | g2
    c1 = MapSet.new([{:pos, g1}, {:pos, g2}])
    # Clause 2 (branch 1 conflict): ~g1
    c2 = MapSet.new([{:neg, g1}])
    # Clause 3 (branch 2 conflict): ~g2
    c3 = MapSet.new([{:neg, g2}])

    clauses_map = %{1 => c1, 2 => c2, 3 => c3}

    assert {:ok, steps, empty_id} = Avatar.resolve_propositional_unsat(clauses_map, 4)
    assert empty_id == 5
    assert length(steps) == 2

    all_steps =
      [
        {:axiom, 1, c1},
        {:axiom, 2, c2},
        {:axiom, 3, c3}
      ] ++ steps

    assert :ok == ProofChecker.verify_refutation(arena, all_steps)
  end

  test "ProofChecker verifies avatar_split and avatar_comp end-to-end", %{arena: arena} do
    alias Astraea.ProofChecker

    {arena, p} = Arena.mk_const(arena, "p", :o)
    {arena, q} = Arena.mk_const(arena, "q", :o)
    # The guard of a ground component is the literal itself.
    {arena, g1} = ProofChecker.avatar_guard(arena, MapSet.new([{:pos, p}]))
    {arena, g2} = ProofChecker.avatar_guard(arena, MapSet.new([{:pos, q}]))
    assert {g1, g2} == {p, q}

    # Axiom 1: p | q
    # Axiom 2: ~p
    # Axiom 3: ~q
    steps = [
      {:axiom, 1, MapSet.new([{:pos, p}, {:pos, q}])},
      {:axiom, 2, MapSet.new([{:neg, p}])},
      {:axiom, 3, MapSet.new([{:neg, q}])},
      # AVATAR split of Axiom 1
      {:avatar_split, 4, 1, [g1, g2]},
      {:avatar_comp, 5, 1, g1, MapSet.new([{:pos, p}])},
      {:avatar_comp, 6, 1, g2, MapSet.new([{:pos, q}])},
      # Branch 1: resolve (p | ~g1) with ~p on p -> ~g1
      {:resolve, 7, 5, 2, {:pos, p}},
      # Branch 2: resolve (q | ~g2) with ~q on q -> ~g2
      {:resolve, 8, 6, 3, {:pos, q}},
      # SAT resolution: resolve (g1 | g2) with ~g1 on g1 -> g2
      {:resolve, 9, 4, 7, {:pos, g1}},
      # SAT resolution: resolve g2 with ~g2 on g2 -> empty clause
      {:resolve, 10, 9, 8, {:pos, g2}}
    ]

    assert :ok == ProofChecker.verify_refutation(arena, steps)
  end

  test "ProofChecker rejects AVATAR guards that are not the components' closures", %{
    arena: arena
  } do
    alias Astraea.ProofChecker

    {arena, i} = Arena.intern_type(arena, :i)
    {arena, pt} = Arena.intern_type(arena, {:arrow, i, Arena.ty_o()})
    {arena, p} = Arena.mk_const(arena, "p", pt)
    {arena, q} = Arena.mk_const(arena, "q", pt)
    {arena, x} = Arena.mk_fvar(arena, 1, i)
    {arena, y} = Arena.mk_fvar(arena, 2, i)
    {arena, px} = Arena.mk_app(arena, p, x)
    {arena, qy} = Arena.mk_app(arena, q, y)
    {arena, qx} = Arena.mk_app(arena, q, x)
    {arena, fake} = Arena.mk_const(arena, "$avatar_g_1", :o)

    c1 = MapSet.new([{:pos, px}])
    c2 = MapSet.new([{:neg, qy}])
    parent = MapSet.union(c1, c2)
    {arena, g1} = ProofChecker.avatar_guard(arena, c1)
    {arena, g2} = ProofChecker.avatar_guard(arena, c2)

    # `! [X]: p @ X` and `! [Y]: ~ (q @ Y)`
    assert {9, _, _, _, _} = Arena.get_node(arena, g1)
    assert {9, _, _, _, _} = Arena.get_node(arena, g2)

    ok = [{:axiom, 1, parent}, {:avatar_split, 2, 1, [g1, g2]}, {:avatar_comp, 3, 1, g1, c1}]
    assert {:ok, _, derived} = ProofChecker.derive_steps(arena, ok)
    assert derived[2] == MapSet.new([{:pos, g1}, {:pos, g2}])
    assert derived[3] == MapSet.new([{:pos, px}, {:neg, g1}])

    forged = [
      # arbitrary guard constants
      [{:axiom, 1, parent}, {:avatar_split, 2, 1, [fake, g2]}],
      [{:axiom, 1, parent}, {:avatar_comp, 2, 1, fake, c1}],
      # a guard that is not the closure of its component
      [{:axiom, 1, parent}, {:avatar_comp, 2, 1, g2, c1}],
      # the parent is not split into these components
      [{:axiom, 1, parent}, {:avatar_split, 2, 1, [g1, g1]}],
      # components sharing a variable cannot be split
      [{:axiom, 1, MapSet.new([{:pos, px}, {:neg, qx}])}, {:avatar_split, 2, 1, [g1, g2]}]
    ]

    for steps <- forged do
      assert {:error, _} = ProofChecker.derive_steps(arena, steps)
    end
  end
end
