defmodule Astraea.Calculus.RenameCnfTest do
  use ExUnit.Case, async: true
  use ExUnitProperties

  alias Astraea.{Arena, TptpLower}
  alias Astraea.Calculus.RenameCnf

  @tag_const 1
  @tag_app 4
  @tag_not 7
  @tag_skolem 10

  defp lower(src) do
    {:ok, lowered} = TptpLower.from_string(src)
    {lowered.arena, Map.new(lowered.axioms, fn {name, _role, id} -> {name, id} end)}
  end

  defp name_of(arena, id) do
    {@tag_const, _, _, sym, _} = Arena.get_node(arena, id)
    Map.fetch!(arena.symbol_names, sym)
  end

  test "Skolemizes existentials over the enclosing universal variables" do
    {arena, ids} =
      lower("""
      thf(r_t, type, r: $i > $i > $o).
      thf(ax, axiom, ! [X: $i]: ? [Y: $i]: (r @ X @ Y)).
      """)

    assert {:ok, arena, [clause], _defined} = RenameCnf.clausify(arena, ids["ax"])
    assert [{:pos, atom}] = MapSet.to_list(clause)
    {arena, x} = Arena.mk_fvar(arena, 1, :i)
    {@tag_app, _, _, r_x, sk_x} = Arena.get_node(arena, atom)
    {@tag_app, _, _, _r, ^x} = Arena.get_node(arena, r_x)
    {@tag_app, _, _, sk, ^x} = Arena.get_node(arena, sk_x)
    assert {@tag_skolem, _, _, _hash, _phi} = Arena.get_node(arena, sk)
  end

  test "renames the right disjunct when distribution would blow up" do
    {arena, ids} =
      lower("""
      thf(a_t, type, a: $o). thf(b_t, type, b: $o). thf(c_t, type, c: $o).
      thf(d_t, type, d: $o). thf(e_t, type, e: $o).
      thf(ax, axiom, (a & b & c) | (d & e)).
      """)

    {:ok, arena, plain, _} = RenameCnf.clausify(arena, ids["ax"], renaming: false)
    assert length(plain) == 6

    {:ok, arena, renamed, defined} = RenameCnf.clausify(arena, ids["ax"])
    # `a | def`, `b | def`, `c | def`, `~def | d`, `~def | e`
    assert length(renamed) == 5
    assert [{const, :pos}] = MapSet.to_list(defined)
    assert name_of(arena, const) =~ ~r/^def_[0-9a-f]{16}$/

    # Sharing: an already defined renaming adds no definition clauses again.
    {:ok, _arena, again, ^defined} = RenameCnf.clausify(arena, ids["ax"], defined: defined)
    assert length(again) == 3
  end

  test "expands Boolean and functional equations" do
    {arena, ids} =
      lower("""
      thf(a_t, type, a: $o). thf(b_t, type, b: $o).
      thf(f_t, type, f: $i > $i). thf(g_t, type, g: $i > $i).
      thf(iff, axiom, (a = b)).
      thf(fun, axiom, (f = g)).
      thf(nfun, axiom, (f != g)).
      """)

    {:ok, arena, iff, _} = RenameCnf.clausify(arena, ids["iff"])
    assert Enum.sort(Enum.map(iff, &MapSet.size/1)) == [2, 2]

    {:ok, arena, [fun], _} = RenameCnf.clausify(arena, ids["fun"])
    assert [{:pos, eq}] = MapSet.to_list(fun)
    assert Arena.free_vars(arena, eq) |> MapSet.size() == 1

    {:ok, arena, [nfun], _} = RenameCnf.clausify(arena, ids["nfun"])
    assert [{:neg, neq}] = MapSet.to_list(nfun)
    assert Arena.free_vars(arena, neq) |> MapSet.size() == 0

    {:ok, _arena, [unexpanded], _} = RenameCnf.clausify(arena, ids["fun"], extensionality: false)
    assert MapSet.to_list(unexpanded) == [{:pos, ids["fun"]}]
  end

  test "refuses to exceed the clause limit instead of truncating" do
    {arena, ids} =
      lower("""
      thf(a_t, type, a: $o). thf(b_t, type, b: $o). thf(c_t, type, c: $o). thf(d_t, type, d: $o).
      thf(ax, axiom, (a & b) | (c & d)).
      """)

    assert {:error, {:cnf_too_large, 4}} =
             RenameCnf.clausify(arena, ids["ax"], renaming: false, max_clauses: 3)
  end

  # Random quantifier-free formulas over p0, p1, p2: for every assignment, the
  # formula holds iff some interpretation of the renaming symbols satisfies the
  # clauses (renaming extends models and its clauses entail the formula).
  defp formula_gen do
    leaf = StreamData.integer(0..2)

    StreamData.tree(leaf, fn child ->
      StreamData.one_of([
        StreamData.tuple({StreamData.constant(:not), child}),
        StreamData.tuple({StreamData.member_of([:or, :and, :iff]), child, child})
      ])
    end)
  end

  defp build(arena, i) when is_integer(i), do: Arena.mk_const(arena, "p#{i}", :o)

  defp build(arena, {:not, a}) do
    {arena, a} = build(arena, a)
    Arena.mk_not(arena, a)
  end

  defp build(arena, {op, a, b}) do
    {arena, a} = build(arena, a)
    {arena, b} = build(arena, b)

    case op do
      :or -> Arena.mk_or(arena, a, b)
      :and -> Arena.mk_and(arena, a, b)
      :iff -> Arena.mk_eq(arena, a, b)
    end
  end

  defp holds?(arena, id, interp) do
    case Arena.get_node(arena, id) do
      {@tag_const, _, _, sym, _} ->
        case Map.fetch!(arena.symbol_names, sym) do
          "$true" -> true
          "$false" -> false
          name -> Map.fetch!(interp, name)
        end

      {@tag_not, _, _, a, _} ->
        not holds?(arena, a, interp)

      {8, _, _, a, b} ->
        holds?(arena, a, interp) or holds?(arena, b, interp)

      {6, _, _, a, b} ->
        holds?(arena, a, interp) == holds?(arena, b, interp)
    end
  end

  defp satisfied?(arena, clauses, interp) do
    Enum.all?(clauses, fn clause ->
      Enum.any?(clause, fn {pol, atom} -> holds?(arena, atom, interp) == (pol == :pos) end)
    end)
  end

  defp assignments([]), do: [%{}]

  defp assignments([name | rest]) do
    for m <- assignments(rest), v <- [true, false], do: Map.put(m, name, v)
  end

  property "renaming CNF extends exactly the models of the formula" do
    check all(shape <- formula_gen(), max_runs: 150) do
      {arena, id} = build(Arena.new(), shape)
      {:ok, arena, clauses, defined} = RenameCnf.clausify(arena, id)
      defs = Enum.map(defined, fn {const, :pos} -> name_of(arena, const) end)
      assert length(defs) <= 10

      for base <- assignments(["p0", "p1", "p2"]) do
        extended = Enum.any?(assignments(defs), &satisfied?(arena, clauses, Map.merge(base, &1)))
        assert extended == holds?(arena, id, base)
      end
    end
  end
end
