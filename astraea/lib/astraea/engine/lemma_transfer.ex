defmodule Astraea.Engine.LemmaTransfer do
  @moduledoc """
  Moves a derived clause together with its derivation from one prover arena into
  another, for lemma sharing between portfolio workers (`Astraea.Portfolio.LemmaBus`).

  Every worker clausifies the problem into its own `Astraea.Arena`, so term ids
  differ between workers. `export/4` turns the ancestor steps of a clause into a
  portable form (symbols by name, types structurally, Skolem constants by their
  quantified formula, so `Arena.mk_skolem/3` reproduces the same content hash) and
  `import/4` re-interns it under fresh step and free-variable ids.

  An imported clause is not trusted: its whole derivation becomes part of the
  receiving worker's step map and is replayed by `ProofChecker.verify_refutation/2`
  with every refutation that uses it. The derivation's `:axiom` steps are the
  sending worker's clausification of the same problem; Skolem constants of a
  different clausification are distinct symbols, which keeps the union of both
  clause sets equisatisfiable with the problem. AVATAR steps (whose clauses only
  hold under split guards) are not exported.
  """

  alias Astraea.Arena
  alias Astraea.ProofChecker

  @tag_const 1
  @tag_bvar 2
  @tag_fvar 3
  @tag_app 4
  @tag_lam 5
  @tag_eq 6
  @tag_not 7
  @tag_or 8
  @tag_forall 9
  @tag_skolem 10
  @tag_comb 11

  @type payload :: %{
          steps: [{non_neg_integer(), tuple()}],
          root: non_neg_integer(),
          max_var: integer()
        }

  @doc """
  The portable derivation of step `root` from `steps` (a map from step id to step),
  or `:error` if it has more than `max_steps` steps or uses a step kind that is not
  exported.
  """
  @spec export(Arena.t(), map(), non_neg_integer(), pos_integer()) :: {:ok, payload()} | :error
  def export(%Arena{} = arena, steps, root, max_steps \\ 40) do
    with {:ok, ids} <- ancestors(steps, [root], MapSet.new(), max_steps) do
      ids
      |> Enum.sort()
      |> Enum.reduce_while({:ok, [], -1}, fn id, {:ok, acc, max_var} ->
        case export_step(arena, Map.fetch!(steps, id)) do
          {:ok, portable, vars} ->
            {:cont, {:ok, [{id, portable} | acc], Enum.max([max_var | vars])}}

          :error ->
            {:halt, :error}
        end
      end)
      |> case do
        {:ok, acc, max_var} -> {:ok, %{steps: Enum.reverse(acc), root: root, max_var: max_var}}
        :error -> :error
      end
    end
  end

  defp ancestors(_steps, [], seen, _max), do: {:ok, seen}

  defp ancestors(steps, [id | rest], seen, max) do
    cond do
      MapSet.member?(seen, id) ->
        ancestors(steps, rest, seen, max)

      MapSet.size(seen) >= max ->
        :error

      true ->
        ancestors(
          steps,
          ProofChecker.step_parents(Map.fetch!(steps, id)) ++ rest,
          MapSet.put(seen, id),
          max
        )
    end
  end

  @doc """
  Re-interns `payload` into `arena`, numbering its steps from `next_step` and
  shifting its free variables past `next_fvar`. Returns
  `{:ok, arena, steps, root_id, next_step, next_fvar}`.
  """
  @spec import(Arena.t(), payload(), non_neg_integer(), non_neg_integer()) ::
          {:ok, Arena.t(), [tuple()], non_neg_integer(), non_neg_integer(), non_neg_integer()}
  def import(
        %Arena{} = arena,
        %{steps: steps, root: root, max_var: max_var},
        next_step,
        next_fvar
      ) do
    ids = steps |> Enum.with_index(next_step) |> Map.new(fn {{old, _}, new} -> {old, new} end)
    ctx = %{ids: ids, var: &(&1 + next_fvar)}

    {imported, arena} =
      Enum.map_reduce(steps, arena, fn {old, portable}, ar ->
        {ar, step} = import_step(ar, ctx, Map.fetch!(ids, old), portable)
        {step, ar}
      end)

    {:ok, arena, imported, Map.fetch!(ids, root), next_step + length(steps),
     next_fvar + max_var + 1}
  end

  # ---------------------------------------------------------------------------
  # Steps: term ids, literals, clauses, substitutions and variable ids are made
  # portable; step ids are kept and renumbered on import.
  # ---------------------------------------------------------------------------

  defp export_step(arena, step) do
    case step do
      {:axiom, _, c} ->
        ok([:axiom, {:clause, c}], arena)

      {:refl, _, t} ->
        ok([:refl, {:term, t}], arena)

      {:symm, _, p} ->
        ok([:symm, {:id, p}], arena)

      {:trans, _, p1, p2} ->
        ok([:trans, {:id, p1}, {:id, p2}], arena)

      {:subst, _, p, s} ->
        ok([:subst, {:id, p}, {:subst, s}], arena)

      {:cong, _, p, t1, t2} ->
        ok([:cong, {:id, p}, {:term, t1}, {:term, t2}], arena)

      {:func_ext, _, p, v, ty} ->
        ok([:func_ext, {:id, p}, {:var, v}, {:type, ty}], arena)

      {:paramod, _, p1, p2, t, l1, l2} ->
        ok([:paramod, {:id, p1}, {:id, p2}, {:term, t}, {:lit, l1}, {:lit, l2}], arena)

      {:resolve, _, p1, p2, l} ->
        ok([:resolve, {:id, p1}, {:id, p2}, {:lit, l}], arena)

      {:cnf, _, p, l, {:forall, v}} ->
        ok([:cnf, {:id, p}, {:lit, l}, {:forall_rule, v}], arena)

      {:cnf, _, p, l, rule} ->
        ok([:cnf, {:id, p}, {:lit, l}, {:raw, rule}], arena)

      {:choice, _, t, v} ->
        ok([:choice, {:term, t}, {:var, v}], arena)

      {:arith_eval, _, p, c} ->
        ok([:arith_eval, {:id, p}, {:clause, c}], arena)

      {:eval, _, p, c} ->
        ok([:eval, {:id, p}, {:clause, c}], arena)

      {:eq_fact, _, p, t1, t2} ->
        ok([:eq_fact, {:id, p}, {:term, t1}, {:term, t2}], arena)

      _ ->
        :error
    end
  end

  defp ok([kind | fields], arena) do
    {fields, vars} = Enum.map_reduce(fields, [], &export_field(arena, &1, &2))
    {:ok, List.to_tuple([kind | fields]), vars}
  end

  defp export_field(arena, {:term, t}, vars), do: export_term(arena, t, vars)

  defp export_field(arena, {:lit, {pol, t}}, vars) do
    {t, vars} = export_term(arena, t, vars)
    {{pol, t}, vars}
  end

  defp export_field(arena, {:clause, c}, vars) do
    Enum.map_reduce(Enum.sort(c), vars, &export_field(arena, {:lit, &1}, &2))
  end

  defp export_field(arena, {:subst, s}, vars) do
    Enum.map_reduce(Enum.sort(s), [], fn {v, t}, vs ->
      {t, vs} = export_term(arena, t, [v | vs])
      {{v, t}, vs}
    end)
    |> then(fn {pairs, vs} -> {pairs, vs ++ vars} end)
  end

  defp export_field(_arena, {:var, v}, vars), do: {v, [v | vars]}
  defp export_field(_arena, {:forall_rule, v}, vars), do: {v, [v | vars]}
  defp export_field(arena, {:type, ty}, vars), do: {export_type(arena, ty), vars}
  defp export_field(_arena, {:id, p}, vars), do: {p, vars}
  defp export_field(_arena, {:raw, x}, vars), do: {x, vars}

  @step_layouts %{
    axiom: [:clause],
    refl: [:term],
    symm: [:id],
    trans: [:id, :id],
    subst: [:id, :subst],
    cong: [:id, :term, :term],
    func_ext: [:id, :var, :type],
    paramod: [:id, :id, :term, :lit, :lit],
    resolve: [:id, :id, :lit],
    choice: [:term, :var],
    arith_eval: [:id, :clause],
    eval: [:id, :clause],
    eq_fact: [:id, :term, :term]
  }

  defp import_step(arena, ctx, new_id, portable) do
    [kind | fields] = Tuple.to_list(portable)

    {fields, arena} =
      case kind do
        :cnf ->
          [p, l, rule] = fields
          {l, arena} = import_field(arena, ctx, :lit, l)

          rule =
            case rule do
              {:forall, _} -> rule
              v when is_integer(v) -> {:forall, ctx.var.(v)}
              other -> other
            end

          {[Map.fetch!(ctx.ids, p), l, rule], arena}

        _ ->
          @step_layouts
          |> Map.fetch!(kind)
          |> Enum.zip(fields)
          |> Enum.map_reduce(arena, fn {layout, f}, ar -> import_field(ar, ctx, layout, f) end)
      end

    {arena, List.to_tuple([kind, new_id | fields])}
  end

  defp import_field(arena, ctx, :id, p), do: {Map.fetch!(ctx.ids, p), arena}
  defp import_field(arena, ctx, :var, v), do: {ctx.var.(v), arena}
  defp import_field(arena, _ctx, :type, ty), do: arena |> Arena.intern_type(ty) |> swap()

  defp import_field(arena, ctx, :term, t), do: arena |> import_term(ctx, t) |> swap()

  defp import_field(arena, ctx, :lit, {pol, t}) do
    {arena, t} = import_term(arena, ctx, t)
    {{pol, t}, arena}
  end

  defp import_field(arena, ctx, :clause, lits) do
    {lits, arena} = Enum.map_reduce(lits, arena, &import_field(&2, ctx, :lit, &1))
    {MapSet.new(lits), arena}
  end

  defp import_field(arena, ctx, :subst, pairs) do
    {pairs, arena} =
      Enum.map_reduce(pairs, arena, fn {v, t}, ar ->
        {ar, t} = import_term(ar, ctx, t)
        {{ctx.var.(v), t}, ar}
      end)

    {Map.new(pairs), arena}
  end

  defp swap({a, b}), do: {b, a}

  # ---------------------------------------------------------------------------
  # Terms and types
  # ---------------------------------------------------------------------------

  @doc "Structural form of a type id: `:o`, `:i`, `{:base, name}` or `{:arrow, dom, cod}`."
  @spec export_type(Arena.t(), Arena.type_id()) :: term()
  def export_type(%Arena{} = arena, ty) do
    case Map.fetch!(arena.type_table, ty) do
      {:arrow, dom, cod} -> {:arrow, export_type(arena, dom), export_type(arena, cod)}
      other -> other
    end
  end

  @doc "Portable form of a term, plus the free-variable ids it contains added to `vars`."
  @spec export_term(Arena.t(), Arena.term_id(), [integer()]) :: {term(), [integer()]}
  def export_term(%Arena{} = arena, term, vars \\ []) do
    {tag, _flags, ty, left, right} = Arena.get_node(arena, term)

    case tag do
      @tag_const ->
        {{:c, export_type(arena, ty), Map.fetch!(arena.symbol_names, left)}, vars}

      @tag_bvar ->
        {{:b, export_type(arena, ty), left}, vars}

      @tag_fvar ->
        {{:v, export_type(arena, ty), left}, [left | vars]}

      @tag_comb ->
        {{:k, export_type(arena, ty), left}, vars}

      @tag_skolem ->
        {pred, vars} = export_term(arena, right, vars)
        {{:s, export_type(arena, ty), pred}, vars}

      @tag_lam ->
        {body, vars} = export_term(arena, right, vars)
        {{:lam, export_type(arena, left), body}, vars}

      @tag_forall ->
        {body, vars} = export_term(arena, right, vars)
        {{:all, export_type(arena, left), body}, vars}

      @tag_not ->
        {a, vars} = export_term(arena, left, vars)
        {{:not, a}, vars}

      t when t in [@tag_app, @tag_eq, @tag_or] ->
        {l, vars} = export_term(arena, left, vars)
        {r, vars} = export_term(arena, right, vars)
        {{t, l, r}, vars}
    end
  end

  @doc "Re-interns a portable term; `var` maps exported free-variable ids."
  @spec import_term(Arena.t(), map(), term()) :: {Arena.t(), Arena.term_id()}
  def import_term(%Arena{} = arena, ctx, portable) do
    case portable do
      {:c, ty, name} ->
        Arena.mk_const(arena, name, ty)

      {:b, ty, idx} ->
        Arena.mk_bvar(arena, idx, ty)

      {:v, ty, id} ->
        Arena.mk_fvar(arena, ctx.var.(id), ty)

      {:k, ty, code} ->
        {arena, ty_id} = Arena.intern_type(arena, ty)
        Arena.intern_node(arena, @tag_comb, 0, ty_id, code, 0)

      {:s, ty, pred} ->
        {arena, pred} = import_term(arena, ctx, pred)
        Arena.mk_skolem(arena, pred, ty)

      {:lam, dom, body} ->
        {arena, body} = import_term(arena, ctx, body)
        Arena.mk_lam(arena, dom, body)

      {:all, dom, body} ->
        {arena, body} = import_term(arena, ctx, body)
        Arena.mk_forall(arena, dom, body)

      {:not, a} ->
        {arena, a} = import_term(arena, ctx, a)
        Arena.mk_not(arena, a)

      {tag, l, r} ->
        {arena, l} = import_term(arena, ctx, l)
        {arena, r} = import_term(arena, ctx, r)

        case tag do
          @tag_app -> Arena.mk_app(arena, l, r)
          @tag_eq -> Arena.mk_eq(arena, l, r)
          @tag_or -> Arena.mk_or(arena, l, r)
        end
    end
  end
end
