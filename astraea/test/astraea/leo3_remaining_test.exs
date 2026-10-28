defmodule Astraea.Leo3RemainingTest do
  @moduledoc """
  The kernel's type check on substitutions.
  """
  use ExUnit.Case, async: true

  alias Astraea.{Arena, ProofChecker}

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
end
