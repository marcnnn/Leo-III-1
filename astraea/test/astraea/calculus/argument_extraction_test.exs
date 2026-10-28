defmodule Astraea.Calculus.ArgumentExtractionTest do
  use ExUnit.Case, async: true

  alias Astraea.{Arena, TptpLower}
  alias Astraea.Calculus.{ArgumentExtraction, RenameCnf}
  alias Astraea.External.ThfPrinter

  @decls """
  thf(p_t, type, p: $o > $o).
  thf(h_t, type, h: ($i > $o) > $o).
  thf(k_t, type, k: ($i > $i) > $o).
  thf(g_t, type, g: $i > $i).
  thf(q_t, type, q: $i > $o).
  thf(a_t, type, a: $o).
  thf(b_t, type, b: $o).
  """

  defp lower(src) do
    {:ok, lowered} = TptpLower.from_string(@decls <> src)
    {lowered.arena, Map.new(lowered.axioms, fn {name, _role, id} -> {name, id} end)}
  end

  defp show(arena, id) do
    {text, _} = ThfPrinter.formula(arena, id, MapSet.new())
    IO.iodata_to_binary(text)
  end

  defp const_name(arena, const) do
    {1, _, _, sym, _} = Arena.get_node(arena, const)
    Map.fetch!(arena.symbol_names, sym)
  end

  test "extracts formulas below uninterpreted symbols and defines them" do
    {arena, ids} = lower("thf(ax, axiom, p @ (a & b)).\nthf(conj, axiom, (a & b)).")
    {arena, new, [{const, def_formula}]} = ArgumentExtraction.apply(arena, ids["ax"])

    name = const_name(arena, const)
    assert name =~ ~r/^xarg_[0-9a-f]{16}$/
    assert show(arena, new) == "(p @ #{name})"
    {arena, expected_def} = Arena.mk_eq(arena, const, ids["conj"])
    assert def_formula == expected_def
    assert Arena.type_of(arena, const) == Arena.ty_o()
  end

  test "leaves arguments of connectives and atomic arguments alone" do
    {arena, ids} = lower("thf(ax, axiom, ~ (a & b) | (p @ a)).")
    assert {_arena, id, []} = ArgumentExtraction.apply(arena, ids["ax"])
    assert id == ids["ax"]
  end

  test "terms with bound variables need local extraction" do
    {arena, ids} = lower("thf(ax, axiom, ! [X: $i]: (p @ ((q @ X) & a))).")
    assert {arena, same, []} = ArgumentExtraction.apply(arena, ids["ax"])
    assert same == ids["ax"]

    {arena, new, [{const, def_formula}]} = ArgumentExtraction.apply(arena, same, local: true)
    name = const_name(arena, const)
    assert show(arena, new) == "(! [B0: $i]: (p @ (#{name} @ B0)))"

    assert show(arena, def_formula) ==
             "(! [B0: $i]: ((#{name} @ B0) = (~ ((~ (q @ B0)) | (~ a)))))"
  end

  test "extraction modes follow Leo-III's xType" do
    {arena, ids} =
      lower("""
      thf(pred, axiom, h @ (^ [X: $i]: ((q @ X) & a))).
      thf(fun, axiom, k @ (^ [X: $i]: (g @ (g @ X)))).
      """)

    assert {_, _, []} = ArgumentExtraction.apply(arena, ids["pred"], type: :boolean)
    assert {_, _, [_]} = ArgumentExtraction.apply(arena, ids["pred"], type: :predicate)
    assert {_, _, []} = ArgumentExtraction.apply(arena, ids["fun"], type: 1)
    assert {_, _, [_]} = ArgumentExtraction.apply(arena, ids["fun"], type: 2)
  end

  test "clause variables become arguments of the extracted symbol" do
    {arena, ids} = lower("thf(ax, axiom, ! [X: $i]: (p @ ((q @ X) & a))).")
    {:ok, arena, [clause], _} = RenameCnf.clausify(arena, ids["ax"])
    {arena, new_clause, [{const, def_formula}]} = ArgumentExtraction.apply_clause(arena, clause)
    name = const_name(arena, const)

    assert ThfPrinter.clause_to_string(arena, new_clause) ==
             "( ! [V1: $i]: ((p @ (#{name} @ V1))) )"

    assert Arena.free_vars(arena, def_formula) == MapSet.new()
  end

  test "symbols are content-addressed: equal terms share them in any arena" do
    {arena1, ids1} =
      lower("thf(ax1, axiom, p @ (a & b)).\nthf(ax2, axiom, (p @ (a & b)) | (p @ a)).")

    {arena1, _, [{c1, _}]} = ArgumentExtraction.apply(arena1, ids1["ax1"])
    {arena1, _, [{c2, _}]} = ArgumentExtraction.apply(arena1, ids1["ax2"])
    assert c1 == c2

    # A different arena (other insertion order) yields the same name.
    {arena2, ids2} =
      lower("thf(other, axiom, ! [X0: $i]: (q @ (g @ (g @ X0)))).\nthf(ax, axiom, p @ (a & b)).")

    {arena2, _, [{c3, _}]} = ArgumentExtraction.apply(arena2, ids2["ax"])
    assert const_name(arena1, c1) == const_name(arena2, c3)
  end
end
