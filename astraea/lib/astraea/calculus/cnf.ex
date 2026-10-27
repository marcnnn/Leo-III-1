defmodule Astraea.Calculus.Cnf do
  @moduledoc """
  Search-time clausification of derived clauses (Leo-III `CNFControl`) together with
  the extensionality inferences `BoolExt` and `FuncExt` (Leo-III `BoolExtControl`,
  `FuncExtControl`).

  After instantiation (primitive substitution, imitation of a connective) literals
  can become non-atomic: `~A`, `A | B`, `! [X]: A`, `$true`, `$false`. `expand/4`
  computes an expansion tree whose every edge is one `:cnf` kernel step; the
  resulting literal sets are computed by `Astraea.ProofChecker.expand_literal/3`
  itself, so the prover replays exactly what the kernel will check.

  With `bool_ext: true`, Boolean equations `A = B` (`A: $o`) are expanded as well
  (`BoolExt`), with `func_ext: true` equations at arrow type become quantified
  equations (`FuncExt`; negative ones are then Skolemized). Both are used as extra
  inferences that keep their premise.
  """

  alias Astraea.{Arena, ProofChecker}
  alias Astraea.Calculus.Terms

  @tag_eq 6
  @tag_not 7
  @tag_or 8
  @tag_forall 9

  @default_max_leaves 16

  @type literal :: ProofChecker.literal()
  @type tree ::
          :atomic
          | :tautology
          | {:expand, literal(), [{ProofChecker.cnf_rule(), ProofChecker.clause(), tree()}]}

  @doc """
  Expansion tree of the clause `lits`. Options: `:bool_ext`, `:func_ext` (default
  `false`) and `:max_leaves` (default 16). Returns `{arena, next_fvar, tree, cutoffs}`
  where an over-large expansion yields `:tautology` (dropped) and one cutoff.
  """
  @spec expand(Arena.t(), ProofChecker.clause(), non_neg_integer(), keyword()) ::
          {Arena.t(), non_neg_integer(), tree(), non_neg_integer()}
  def expand(%Arena{} = arena, lits, next_fvar, opts \\ []) do
    ctx = %{
      arena: arena,
      next_fvar: next_fvar,
      leaves: 0,
      max_leaves: Keyword.get(opts, :max_leaves, @default_max_leaves),
      bool_ext: Keyword.get(opts, :bool_ext, false),
      func_ext: Keyword.get(opts, :func_ext, false)
    }

    {ctx, tree} = expand_clause(ctx, lits)

    if ctx.leaves > ctx.max_leaves,
      do: {ctx.arena, ctx.next_fvar, :tautology, 1},
      else: {ctx.arena, ctx.next_fvar, tree, 0}
  end

  @doc "Returns true iff no literal of `lits` would be expanded under `opts`."
  @spec atomic?(Arena.t(), ProofChecker.clause(), keyword()) :: boolean()
  def atomic?(%Arena{} = arena, lits, opts \\ []) do
    ctx = %{arena: arena, next_fvar: 0, bool_ext: opts[:bool_ext], func_ext: opts[:func_ext]}
    Enum.all?(lits, &(rules(ctx, &1) == :atomic))
  end

  @doc "The leaf clauses of an expansion tree."
  @spec leaves(tree(), ProofChecker.clause()) :: [ProofChecker.clause()]
  def leaves(:atomic, lits), do: [lits]
  def leaves(:tautology, _lits), do: []

  def leaves({:expand, _lit, branches}, _lits),
    do: Enum.flat_map(branches, fn {_rule, lits, sub} -> leaves(sub, lits) end)

  defp expand_clause(%{leaves: n, max_leaves: max} = ctx, _lits) when n > max,
    do: {ctx, :tautology}

  defp expand_clause(ctx, lits) do
    lits
    |> Enum.reduce_while(:atomic, fn lit, :atomic ->
      case rules(ctx, lit) do
        :atomic -> {:cont, :atomic}
        other -> {:halt, {lit, other}}
      end
    end)
    |> case do
      :atomic -> {%{ctx | leaves: ctx.leaves + 1}, :atomic}
      {_lit, :tautology} -> {ctx, :tautology}
      {lit, rules} -> expand_lit(ctx, lits, lit, rules)
    end
  end

  defp expand_lit(ctx, lits, lit, rules) do
    {ctx, rules} = fresh_instances(ctx, rules)

    {branches, ctx} =
      Enum.map_reduce(rules, ctx, fn rule, ctx ->
        {:ok, arena, new} = ProofChecker.expand_literal(ctx.arena, lit, rule)
        child = lits |> MapSet.delete(lit) |> MapSet.union(MapSet.new(new))
        {ctx, sub} = expand_clause(%{ctx | arena: arena}, child)
        {{rule, child, sub}, ctx}
      end)

    {ctx, {:expand, lit, branches}}
  end

  defp fresh_instances(ctx, [:forall]),
    do: {%{ctx | next_fvar: ctx.next_fvar + 1}, [{:forall, ctx.next_fvar}]}

  defp fresh_instances(ctx, rules), do: {ctx, rules}

  # Kernel rules that expand `lit`, `:atomic` or `:tautology`.
  defp rules(ctx, {pol, atom}) do
    case {pol, Arena.get_node(ctx.arena, atom)} do
      {_, {@tag_not, _, _, _, _}} -> [:not]
      {:pos, {@tag_or, _, _, _, _}} -> [:or]
      {:neg, {@tag_or, _, _, _, _}} -> [{:or, :left}, {:or, :right}]
      {:pos, {@tag_forall, _, _, _, _}} -> [:forall]
      {:neg, {@tag_forall, _, _, _, _}} -> [:skolem]
      {_, {@tag_eq, _, _, l, _}} -> eq_rules(ctx, l)
      _ -> truth_rules(ctx.arena, pol, atom)
    end
  end

  defp eq_rules(ctx, lhs) do
    ty = Arena.type_of(ctx.arena, lhs)

    cond do
      ctx.bool_ext && ty == Arena.ty_o() -> [{:bool_eq, :left}, {:bool_eq, :right}]
      ctx.func_ext && Terms.arrow_domain(ctx.arena, ty) != nil -> [:ext]
      true -> :atomic
    end
  end

  defp truth_rules(arena, pol, atom) do
    case {pol, Terms.const_named?(arena, atom, "$true"),
          Terms.const_named?(arena, atom, "$false")} do
      {:pos, true, _} -> :tautology
      {:neg, _, true} -> :tautology
      {:neg, true, _} -> [:truth]
      {:pos, _, true} -> [:truth]
      _ -> :atomic
    end
  end
end
