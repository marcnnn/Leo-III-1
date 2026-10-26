defmodule Astraea.Calculus.Choice do
  @moduledoc """
  Hilbert choice (Leo-III `Choice` / `ChoiceControl.instantiateChoice`).

  The choice operator is the constant `"$choice"` of type `(T > $o) > T`, one constant
  per type `T` under the same name (interface agreed with the input agent). For every
  term `$choice @ P` occurring in a clause, the choice rule adds the instance

      ~(P @ X) | P @ ($choice @ P)

  of the axiom of choice, which the kernel checks as a `{:choice, id, P, X}` step
  (`Astraea.ProofChecker.choice_instance/3`).
  """

  alias Astraea.Arena
  alias Astraea.Calculus.Terms

  @name "$choice"

  @doc "The name of the choice constant."
  @spec name() :: String.t()
  def name, do: @name

  @doc """
  The closed choice arguments `P` of all occurrences of `$choice @ P` in `lits`.
  """
  @spec predicates(Arena.t(), Astraea.ProofChecker.clause()) :: [Arena.term_id()]
  def predicates(%Arena{} = arena, lits) do
    lits
    |> Enum.reduce(MapSet.new(), fn {_pol, atom}, acc -> collect(arena, atom, acc) end)
    |> MapSet.to_list()
  end

  defp collect(arena, term_id, acc) do
    acc =
      case Terms.spine(arena, term_id) do
        {head, [pred | _]} ->
          if Terms.const_named?(arena, head, @name) and not Arena.has_loose_bvar?(arena, pred, 0),
            do: MapSet.put(acc, pred),
            else: acc

        _ ->
          acc
      end

    case Terms.view(arena, term_id) do
      {:rigid, _head, children} ->
        Enum.reduce(children, acc, fn {c, _}, a -> collect(arena, c, a) end)

      {:flex, _f, args} ->
        Enum.reduce(args, acc, &collect(arena, &1, &2))

      {:lam, _dom, body} ->
        collect(arena, body, acc)
    end
  end
end
