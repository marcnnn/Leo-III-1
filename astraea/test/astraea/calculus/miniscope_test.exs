defmodule Astraea.Calculus.MiniscopeTest do
  use ExUnit.Case, async: true
  use ExUnitProperties

  alias Astraea.{Arena, TptpLower}
  alias Astraea.Calculus.{Miniscope, Simplification}

  @tag_const 1
  @tag_bvar 2
  @tag_eq 6
  @tag_not 7
  @tag_or 8
  @tag_forall 9

  @decls """
  thf(p_t, type, p: $o).
  thf(q_t, type, q: $i > $o).
  thf(r_t, type, r: $i > $i > $o).
  """

  # Lowers `pairs` of `{input, expected}` formulas into one arena, so that results
  # can be compared by term id (hash-consing).
  defp lower_pairs(pairs) do
    src =
      pairs
      |> Enum.with_index()
      |> Enum.map_join(fn {{input, expected}, i} ->
        "thf(in#{i}, axiom, #{input}).\nthf(out#{i}, axiom, #{expected}).\n"
      end)

    {:ok, lowered} = TptpLower.from_string(@decls <> src)
    ids = Map.new(lowered.axioms, fn {name, _role, id} -> {name, id} end)
    {lowered.arena, Enum.map(0..(length(pairs) - 1), &{ids["in#{&1}"], ids["out#{&1}"]})}
  end

  defp assert_rewrites(fun, pairs) do
    {arena, ids} = lower_pairs(pairs)

    Enum.zip(pairs, ids)
    |> Enum.reduce(arena, fn {{input, expected}, {in_id, out_id}}, arena ->
      {arena, result} = fun.(arena, in_id)
      # The lowered expectation may still contain double negations (`?` inside `&`).
      {arena, out_id} = Arena.beta_eta_norm(arena, out_id)
      assert result == out_id, "#{input} should become #{expected}"
      arena
    end)
  end

  describe "Simplification" do
    test "propositional identities and vacuous quantifiers" do
      assert_rewrites(&Simplification.apply/2, [
        {"p & p", "p"},
        {"p | ~ p", "$true"},
        {"p & ~ p", "$false"},
        {"p | $false", "p"},
        {"(p = $false)", "~ p"},
        {"(p = $true)", "p"},
        {"~ ~ p", "p"},
        {"! [X: $i]: p", "p"},
        {"! [X: $i]: ((q @ X) = (q @ X))", "$true"}
      ])
    end
  end

  describe "Miniscope" do
    test "pushes universal quantifiers into disjunctions and conjunctions" do
      assert_rewrites(&Miniscope.apply/2, [
        {"! [X: $i]: (p | (q @ X))", "p | (! [X: $i]: (q @ X))"},
        {"! [X: $i]: ((q @ X) & p)", "(! [X: $i]: (q @ X)) & p"},
        {"! [X: $i]: ((q @ X) & (r @ X @ X))", "(! [X: $i]: (q @ X)) & (! [X: $i]: (r @ X @ X))"}
      ])
    end

    test "distributes existential quantifiers over disjunctions" do
      assert_rewrites(&Miniscope.apply/2, [
        {"? [X: $i]: ((q @ X) | (r @ X @ X))", "(? [X: $i]: (q @ X)) | (? [X: $i]: (r @ X @ X))"},
        {"? [X: $i]: ((q @ X) & p)", "(? [X: $i]: (q @ X)) & p"}
      ])
    end

    test "swaps adjacent universal quantifiers to move one further in" do
      assert_rewrites(&Miniscope.apply/2, [
        {"! [X: $i, Y: $i]: ((r @ X @ Y) | (q @ Y))",
         "! [Y: $i]: ((! [X: $i]: (r @ X @ Y)) | (q @ Y))"}
      ])
    end

    test "keeps quantifiers whose variable occurs on both sides" do
      assert_rewrites(&Miniscope.apply/2, [
        {"! [X: $i]: ((q @ X) | (r @ X @ X))", "! [X: $i]: ((q @ X) | (r @ X @ X))"},
        {"! [X: $i]: ? [Y: $i]: (r @ X @ Y)", "! [X: $i]: ? [Y: $i]: (r @ X @ Y)"}
      ])
    end
  end

  # Random closed formulas over the Boolean constants p0, p1, p2 with quantifiers
  # over `$o`, evaluated by brute force.
  defp formula_gen do
    leaf = StreamData.tuple({StreamData.constant(:atom), StreamData.integer(0..4)})

    StreamData.tree(leaf, fn child ->
      StreamData.one_of([
        StreamData.tuple({StreamData.constant(:not), child}),
        StreamData.tuple({StreamData.member_of([:or, :and, :iff]), child, child}),
        StreamData.tuple({StreamData.member_of([:all, :ex]), child})
      ])
    end)
  end

  defp build(arena, {:atom, i}, scope) when i >= 3 and scope > 0,
    do: Arena.mk_bvar(arena, rem(i, scope), :o)

  defp build(arena, {:atom, i}, _scope), do: Arena.mk_const(arena, "p#{rem(i, 3)}", :o)

  defp build(arena, {:not, a}, scope) do
    {arena, a} = build(arena, a, scope)
    Arena.mk_not(arena, a)
  end

  defp build(arena, {op, a, b}, scope) do
    {arena, a} = build(arena, a, scope)
    {arena, b} = build(arena, b, scope)

    case op do
      :or -> Arena.mk_or(arena, a, b)
      :and -> Arena.mk_and(arena, a, b)
      :iff -> Arena.mk_eq(arena, a, b)
    end
  end

  defp build(arena, {q, a}, scope) do
    {arena, body} = build(arena, a, scope + 1)
    if q == :all, do: Arena.mk_forall(arena, :o, body), else: Arena.mk_exists(arena, :o, body)
  end

  defp eval(arena, id, env, interp) do
    case Arena.get_node(arena, id) do
      {@tag_const, _, _, sym, _} ->
        case Map.fetch!(arena.symbol_names, sym) do
          "$true" -> true
          "$false" -> false
          name -> Map.fetch!(interp, name)
        end

      {@tag_bvar, _, _, idx, _} ->
        Enum.at(env, idx)

      {@tag_not, _, _, a, _} ->
        not eval(arena, a, env, interp)

      {@tag_or, _, _, a, b} ->
        eval(arena, a, env, interp) or eval(arena, b, env, interp)

      {@tag_eq, _, _, a, b} ->
        eval(arena, a, env, interp) == eval(arena, b, env, interp)

      {@tag_forall, _, _, _ty, body} ->
        eval(arena, body, [true | env], interp) and eval(arena, body, [false | env], interp)
    end
  end

  defp interpretations do
    for a <- [true, false],
        b <- [true, false],
        c <- [true, false],
        do: %{"p0" => a, "p1" => b, "p2" => c}
  end

  property "simplification and miniscoping preserve the truth value" do
    check all(shape <- formula_gen(), max_runs: 200) do
      {arena, id} = build(Arena.new(), shape, 0)
      {arena, simp} = Simplification.apply(arena, id)
      {arena, mini} = Miniscope.apply(arena, simp)

      for interp <- interpretations() do
        expected = eval(arena, id, [], interp)
        assert eval(arena, simp, [], interp) == expected
        assert eval(arena, mini, [], interp) == expected
      end
    end
  end
end
