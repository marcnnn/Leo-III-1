defmodule Astraea.ProverAvatarTest do
  use ExUnit.Case, async: true
  alias Astraea.Arena
  alias Astraea.ProofChecker
  alias Astraea.Prover

  setup do
    arena = Arena.new()
    {:ok, arena: arena}
  end

  test "proves propositional problem requiring AVATAR clause splitting with LCF certificate", %{arena: arena} do
    # Axioms (no unit clauses on p or q):
    # 1. p | q
    # 2. ~p | r
    # 3. ~q | r
    # 4. ~r
    {arena, p} = Arena.mk_const(arena, "p", :o)
    {arena, q} = Arena.mk_const(arena, "q", :o)
    {arena, r} = Arena.mk_const(arena, "r", :o)

    clauses = [
      MapSet.new([{:pos, p}, {:pos, q}]),
      MapSet.new([{:neg, p}, {:pos, r}]),
      MapSet.new([{:neg, q}, {:pos, r}]),
      MapSet.new([{:neg, r}])
    ]

    assert {:proved, steps, stats} = Prover.prove_clauses(arena, clauses, avatar: true)
    assert stats.avatar_splits >= 1
    assert :ok == ProofChecker.verify_refutation(stats.arena, steps)
  end

  test "proves first-order problem with independent ground components under AVATAR", %{arena: arena} do
    # Problem:
    # 1. p(a) | q(b)
    # 2. ~p(X) | r(X)
    # 3. ~q(Y) | r(Y)
    # 4. ~r(a)
    # 5. ~r(b)
    {arena, a} = Arena.mk_const(arena, "a", :i)
    {arena, b} = Arena.mk_const(arena, "b", :i)
    {arena, p} = Arena.mk_const(arena, "p", {:arrow, :i, :o})
    {arena, q} = Arena.mk_const(arena, "q", {:arrow, :i, :o})
    {arena, r} = Arena.mk_const(arena, "r", {:arrow, :i, :o})
    {arena, x} = Arena.mk_fvar(arena, 1, :i)
    {arena, y} = Arena.mk_fvar(arena, 2, :i)

    {arena, pa} = Arena.mk_app(arena, p, a)
    {arena, qb} = Arena.mk_app(arena, q, b)
    {arena, px} = Arena.mk_app(arena, p, x)
    {arena, rx} = Arena.mk_app(arena, r, x)
    {arena, qy} = Arena.mk_app(arena, q, y)
    {arena, ry} = Arena.mk_app(arena, r, y)
    {arena, ra} = Arena.mk_app(arena, r, a)
    {arena, rb} = Arena.mk_app(arena, r, b)

    clauses = [
      MapSet.new([{:pos, pa}, {:pos, qb}]),
      MapSet.new([{:neg, px}, {:pos, rx}]),
      MapSet.new([{:neg, qy}, {:pos, ry}]),
      MapSet.new([{:neg, ra}]),
      MapSet.new([{:neg, rb}])
    ]

    assert {:proved, steps, stats} = Prover.prove_clauses(arena, clauses, avatar: true)
    assert stats.avatar_splits >= 1
    assert :ok == ProofChecker.verify_refutation(stats.arena, steps)
  end
end
