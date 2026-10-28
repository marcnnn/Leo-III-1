defmodule Astraea.Calculus.Disagreement do
  @moduledoc """
  Resolution up to extensionality (E `ext_sup`, Leo-III's unification constraints).

          C | p(s)     D | ~p(t)
    ─────────────────────────────────   s, t of function or Boolean type
            C | D | s != t

  `pairs/4` decomposes two atoms with the same rigid head into the disagreement pairs
  `{s, t}`. It fails if a pair has base type (a real clash), contains a bare free
  variable (pre-unification covers it) or a loose bound variable, or if there are
  more than `max` pairs. The prover derives the conclusion from existing kernel
  steps: `{:refl}` and `{:cnf, {:bool_eq, :left}}` give `~(s = t) | s = t`,
  `:paramod` turns `p(s)` into `p(t)`, and `:resolve` removes it.
  """

  alias Astraea.Arena
  alias Astraea.Calculus.Terms

  @tag_eq 6

  @spec pairs(Arena.t(), Arena.term_id(), Arena.term_id(), pos_integer()) ::
          {:ok, [{Arena.term_id(), Arena.term_id()}]} | :error
  def pairs(%Arena{} = arena, a1, a2, max) do
    with false <- a1 == a2,
         false <- eq?(arena, a1) or eq?(arena, a2),
         {:rigid, {:sym, h}, args1} <- Terms.view(arena, a1),
         {:rigid, {:sym, ^h}, args2} <- Terms.view(arena, a2),
         true <- length(args1) == length(args2),
         {:ok, pairs} <- decompose(arena, Enum.zip(args1, args2), []),
         true <- pairs != [] and length(pairs) <= max do
      {:ok, Enum.reverse(pairs)}
    else
      _ -> :error
    end
  end

  defp decompose(_arena, [], acc), do: {:ok, acc}

  defp decompose(arena, [{{s, 0}, {t, 0}} | rest], acc) when s == t,
    do: decompose(arena, rest, acc)

  defp decompose(arena, [{{s, 0}, {t, 0}} | rest], acc) do
    case {Terms.view(arena, s), Terms.view(arena, t)} do
      {{:rigid, {:sym, h}, sargs}, {:rigid, {:sym, h}, targs}}
      when length(sargs) == length(targs) ->
        decompose(arena, Enum.zip(sargs, targs) ++ rest, acc)

      _ ->
        if constraint?(arena, s) and constraint?(arena, t),
          do: decompose(arena, rest, [{s, t} | acc]),
          else: :error
    end
  end

  defp constraint?(arena, term_id) do
    ty = Arena.type_of(arena, term_id)

    (ty == Arena.ty_o() or match?({:arrow, _, _}, Map.get(arena.type_table, ty))) and
      not Terms.fvar?(arena, term_id) and
      not Arena.has_loose_bvar?(arena, term_id, 0)
  end

  defp eq?(arena, term_id), do: match?({@tag_eq, _, _, _, _}, Arena.get_node(arena, term_id))
end
