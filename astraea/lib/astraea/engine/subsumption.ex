defmodule Astraea.Engine.Subsumption do
  @moduledoc """
  Clause subsumption (Leo-III `Subsumption.subsumes`): `c` subsumes `d` when one
  substitution `σ`, binding only variables of `c`, maps the literals of `c`
  injectively onto literals of `d` of the same polarity (multiset subsumption, so a
  clause never subsumes one with fewer literals). Matching is syntactic via
  `Astraea.Arena.match_pattern/4`, with both orientations of equations.

  `subsumption_fv/1` is the feature vector used to prefilter candidates in
  `Astraea.Engine.FVIndex`: every lane is monotone under instantiation and literal
  inclusion, so `c` can only subsume `d` if `fv(c) <= fv(d)` lane-wise.
  """

  alias Astraea.Arena
  alias Astraea.Engine.FVIndex

  @tag_eq 6
  # Lane of the free-variable occurrence count in `Arena.feature_vector/2`; it
  # shrinks under instantiation, so it carries the negative literal count instead.
  @fvar_lane 4

  @doc "The subsumption feature vector of a clause item."
  @spec subsumption_fv(map()) :: FVIndex.fv()
  def subsumption_fv(%{fv: fv, lits: lits}) do
    negs = Enum.count(lits, &match?({:neg, _}, &1))
    fv |> List.replace_at(@fvar_lane, negs) |> FVIndex.fv()
  end

  @doc "Whether clause item `c` subsumes clause item `d`."
  @spec subsumes?(Arena.t(), map(), map()) :: boolean()
  def subsumes?(%Arena{} = arena, c, d) do
    MapSet.size(c.lits) <= MapSet.size(d.lits) and
      (MapSet.subset?(c.lits, d.lits) or
         match_lits(arena, heaviest_first(arena, c.lits), MapSet.to_list(d.lits), %{}))
  end

  defp heaviest_first(arena, lits) do
    Enum.sort_by(lits, fn {_pol, atom} -> -elem(Arena.term_weight_and_vars(arena, atom), 0) end)
  end

  defp match_lits(_arena, [], _targets, _subst), do: true

  defp match_lits(arena, [{pol, atom} | rest], targets, subst) do
    Enum.any?(targets, fn {t_pol, t_atom} = target ->
      t_pol == pol and
        arena
        |> match_atom(atom, t_atom, subst)
        |> Enum.any?(&match_lits(arena, rest, List.delete(targets, target), &1))
    end)
  end

  @doc """
  All matchers of `pat` onto `target` extending `subst`; for two equations both
  orientations are tried, since either may be needed for the remaining literals.
  """
  @spec match_atom(Arena.t(), Arena.term_id(), Arena.term_id(), Arena.subst()) :: [Arena.subst()]
  def match_atom(%Arena{} = arena, pat, target, subst) do
    case {Arena.get_node(arena, pat), Arena.get_node(arena, target)} do
      {{@tag_eq, _, _, l, r}, {@tag_eq, _, _, s, t}} ->
        for {a, b} <- [{s, t}, {t, s}],
            {:ok, s1} <- [Arena.match_pattern(arena, l, a, subst)],
            {:ok, s2} <- [Arena.match_pattern(arena, r, b, s1)],
            uniq: true,
            do: s2

      _ ->
        case Arena.match_pattern(arena, pat, target, subst) do
          {:ok, s} -> [s]
          :error -> []
        end
    end
  end
end
