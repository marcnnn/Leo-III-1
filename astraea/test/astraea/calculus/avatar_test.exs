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

  test "splits mixed clause with one ground literal and two linked variable literals", %{arena: arena} do
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
end
