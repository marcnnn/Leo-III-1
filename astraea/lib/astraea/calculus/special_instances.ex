defmodule Astraea.Calculus.SpecialInstances do
  @moduledoc """
  Quantifier Instantiation with Canonical Terms (Leo-III `Control.instantiateDomain` / `Control.specialInstances`).

  For clauses with universally quantified variables (free variables) of higher-order types:
  1. Boolean predicates X: T -> $o:
     instantiate with ^ [_]: $true and ^ [_]: $false.
  2. Identity functions X: T -> T:
     instantiate with ^ [z]: z.
  3. Choice operators X: (T -> $o) -> T:
     instantiate with "$choice" of type (T -> $o) -> T (or registered choice operator).
  """

  alias Astraea.Arena

  @doc """
  Enumerates candidate canonical instances for higher-order free variables in a clause item.
  Returns `{arena, [{var_id, [term_id]}]}`.
  """
  @spec candidates(Arena.t(), map(), [Arena.term_id()]) ::
          {Arena.t(), [{non_neg_integer(), [Arena.term_id()]}]}
  def candidates(%Arena{} = arena, clause_item, choice_heads \\ []) do
    fvars = Map.get(clause_item, :fvars, MapSet.new())

    Enum.reduce(fvars, {arena, []}, fn {var_id, ty_id}, {ar, acc} ->
      {ar, insts} = variable_instances(ar, ty_id, choice_heads)

      if insts == [] do
        {ar, acc}
      else
        {ar, [{var_id, Enum.uniq(insts)} | acc]}
      end
    end)
  end

  defp variable_instances(arena, ty_id, choice_heads) do
    {arena, pred_insts} = predicate_instances(arena, ty_id)
    {arena, id_insts} = identity_instances(arena, ty_id)
    {arena, choice_insts} = choice_instances(arena, ty_id, choice_heads)

    {arena, pred_insts ++ id_insts ++ choice_insts}
  end

  # Case 1: Boolean predicate X: T -> $o
  defp predicate_instances(arena, ty_id) do
    case Map.get(arena.type_table, ty_id) do
      {:arrow, dom, cod} when cod == 0 or cod == :o ->
        {arena, t_true} = Arena.mk_const(arena, "$true", Arena.ty_o())
        {arena, lam_true} = Arena.mk_lam(arena, dom, t_true)

        {arena, t_false} = Arena.mk_const(arena, "$false", Arena.ty_o())
        {arena, lam_false} = Arena.mk_lam(arena, dom, t_false)

        {arena, [lam_true, lam_false]}

      _ ->
        {arena, []}
    end
  end

  # Case 2: Identity function X: T -> T
  defp identity_instances(arena, ty_id) do
    case Map.get(arena.type_table, ty_id) do
      {:arrow, dom, cod} when dom == cod ->
        {arena, z} = Arena.mk_bvar(arena, 0, dom)
        {arena, lam_id} = Arena.mk_lam(arena, dom, z)
        {arena, [lam_id]}

      _ ->
        {arena, []}
    end
  end

  # Case 3: Choice operator X: (T -> $o) -> T
  defp choice_instances(arena, ty_id, choice_heads) do
    case Map.get(arena.type_table, ty_id) do
      {:arrow, pred_ty, cod} ->
        case Map.get(arena.type_table, pred_ty) do
          {:arrow, dom, o_ty} when dom == cod ->
            if o_ty == 0 or o_ty == :o or o_ty == Arena.ty_o() do
              choice_op =
                Enum.find(choice_heads, fn head ->
                  Arena.type_of(arena, head) == ty_id
                end)

              {arena, eps} =
                if choice_op do
                  {arena, choice_op}
                else
                  Arena.mk_const(arena, "$choice", ty_id)
                end

              {arena, [eps]}
            else
              {arena, []}
            end

          _ ->
            {arena, []}
        end

      _ ->
        {arena, []}
    end
  end
end
