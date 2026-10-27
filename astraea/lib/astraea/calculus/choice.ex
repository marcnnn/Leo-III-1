defmodule Astraea.Calculus.Choice do
  @moduledoc """
  Hilbert choice (Leo-III `Choice` / `ChoiceControl.instantiateChoice`).

  The choice operator is the constant `"$choice"` of type `(T > $o) > T`, one constant
  per type `T` under the same name (interface agreed with the input agent). For every
  term `$choice @ P` occurring in a clause, the choice rule adds the instance

      ~(P @ X) | P @ ($choice @ P)

  of the axiom of choice, which the kernel checks as a `{:choice, id, P, X}` step
  (`Astraea.ProofChecker.choice_instance/3`).

  Also supports user-defined choice functions (Leo-III `detectChoiceClause`).
  Axiom clauses of the form:

      ~(P @ X) | P @ (F @ P)    or    P @ (F @ P) | ~(P @ X)

  are detected and registered. Occurrences of `F @ P` generate instances of the axiom
  instantiated with `P := pred` via kernel `:subst` steps.
  """

  alias Astraea.Arena
  alias Astraea.Calculus.Terms

  @name "$choice"
  @tag_fvar 3
  @tag_eq 6

  @doc "The name of the choice constant."
  @spec name() :: String.t()
  def name, do: @name

  @doc """
  Detects whether a clause literal set represents a higher-order choice axiom:

      ~(P @ X) | P @ (F @ P)    or    P @ (F @ P) | ~(P @ X)

  where `P` and `X` are distinct free variables, `X: T`, `P: T > $o`, and `F` is a
  function term of type `(T > $o) > T`.
  """
  @spec detect_axiom(Arena.t(), Astraea.ProofChecker.clause()) ::
          {:ok,
           %{
             choice_head: Arena.term_id(),
             pred_fvar_id: non_neg_integer(),
             witness_fvar_id: non_neg_integer(),
             dom_ty: Arena.type_id()
           }}
          | :none
  def detect_axiom(%Arena{} = arena, lits) do
    case Enum.sort_by(MapSet.to_list(lits), &elem(&1, 0)) do
      [{:neg, neg_atom}, {:pos, pos_atom}] ->
        with false <- eq_atom?(arena, neg_atom),
             false <- eq_atom?(arena, pos_atom),
             {p_fvar, [x_fvar]} <- Terms.spine(arena, neg_atom),
             true <- Terms.fvar?(arena, p_fvar) and Terms.fvar?(arena, x_fvar),
             true <- p_fvar != x_fvar,
             {@tag_fvar, _, p_ty, p_var_id, _} <- Arena.get_node(arena, p_fvar),
             {@tag_fvar, _, x_ty, x_var_id, _} <- Arena.get_node(arena, x_fvar),
             {:arrow, dom_ty, o_ty} <- Map.get(arena.type_table, p_ty),
             true <- o_ty == Arena.ty_o() and x_ty == dom_ty,
             {^p_fvar, [f_app]} <- Terms.spine(arena, pos_atom),
             {f_head, [^p_fvar]} <- Terms.spine(arena, f_app),
             true <- f_head != p_fvar and f_head != x_fvar,
             f_ty <- Arena.type_of(arena, f_head),
             {:arrow, ^p_ty, ^dom_ty} <- Map.get(arena.type_table, f_ty) do
          {:ok,
           %{
             choice_head: f_head,
             pred_fvar_id: p_var_id,
             witness_fvar_id: x_var_id,
             dom_ty: dom_ty
           }}
        else
          _ -> :none
        end

      _ ->
        :none
    end
  end

  defp eq_atom?(arena, atom) do
    match?({@tag_eq, _, _, _, _}, Arena.get_node(arena, atom))
  end

  @doc """
  The closed choice arguments `P` of all occurrences of choice operator applications in `lits`.
  Returns a list of `{operator, pred}` tuples, where `operator` is `:builtin` for `"$choice"`
  or the `term_id` of a user-defined choice function.
  """
  @spec predicates(Arena.t(), Astraea.ProofChecker.clause(), Enumerable.t()) ::
          [{:builtin | Arena.term_id(), Arena.term_id()}]
  def predicates(%Arena{} = arena, lits, choice_heads \\ []) do
    heads_set = MapSet.new(choice_heads)

    lits
    |> Enum.reduce(MapSet.new(), fn {_pol, atom}, acc ->
      collect(arena, atom, heads_set, acc)
    end)
    |> MapSet.to_list()
  end

  defp collect(arena, term_id, heads_set, acc) do
    acc =
      case Terms.spine(arena, term_id) do
        {head, [pred | _]} ->
          cond do
            Terms.const_named?(arena, head, @name) and not Arena.has_loose_bvar?(arena, pred, 0) ->
              MapSet.put(acc, {:builtin, pred})

            MapSet.member?(heads_set, head) and not Arena.has_loose_bvar?(arena, pred, 0) ->
              MapSet.put(acc, {head, pred})

            true ->
              acc
          end

        _ ->
          acc
      end

    case Terms.view(arena, term_id) do
      {:rigid, _head, children} ->
        Enum.reduce(children, acc, fn {c, _}, a -> collect(arena, c, heads_set, a) end)

      {:flex, _f, args} ->
        Enum.reduce(args, acc, &collect(arena, &1, heads_set, &2))

      {:lam, _dom, body} ->
        collect(arena, body, heads_set, acc)
    end
  end
end
