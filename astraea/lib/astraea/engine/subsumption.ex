defmodule Astraea.Engine.Subsumption do
  @moduledoc """
  Clause subsumption (Leo-III `Subsumption.subsumes`): `c` subsumes `d` when one
  substitution `σ`, binding only variables of `c`, maps the literals of `c`
  injectively onto literals of `d` of the same polarity (multiset subsumption, so a
  clause never subsumes one with fewer literals). Matching is syntactic via
  `Astraea.Arena.match_pattern/4`, with both orientations of equations.

  `clause_fv/2` is the feature vector that prefilters candidates in
  `Astraea.Engine.FVIndex` (Schulz, "Simple and Efficient Clause Subsumption with
  Feature Vector Indexing"): literal counts, the symbol count, and rigid-symbol
  occurrences hashed into buckets per polarity. Every lane is monotone under
  instantiation and polarity-preserving literal inclusion, so `c` can only subsume
  `d` if `clause_fv(c) <= clause_fv(d)` lane-wise.
  """

  alias Astraea.Arena
  alias Astraea.Engine.FVIndex

  @tag_const 1
  @tag_fvar 3
  @tag_app 4
  @tag_lam 5
  @tag_eq 6
  @tag_not 7
  @tag_or 8
  @tag_forall 9
  @tag_skolem 10
  @tag_comb 11

  # Lanes: 0 literals, 1 negative literals, 2 symbols (non-variable nodes),
  # 4..9 positive and 10..15 negative rigid-symbol buckets.
  @buckets 6
  @pos_base 4
  @neg_base @pos_base + @buckets

  @doc "The subsumption feature vector of the clause `lits`."
  @spec clause_fv(Arena.t(), Enumerable.t()) :: FVIndex.fv()
  def clause_fv(%Arena{} = arena, lits) do
    counts =
      Enum.reduce(lits, :array.new(16, default: 0), fn {pol, atom}, acc ->
        acc = bump(acc, 0)
        acc = if pol == :neg, do: bump(acc, 1), else: acc
        walk(arena, atom, if(pol == :pos, do: @pos_base, else: @neg_base), acc)
      end)

    counts |> :array.to_list() |> FVIndex.fv()
  end

  @doc """
  Query vector bounding every clause that contains an instance of `term`
  (for backward demodulation candidates): one literal, at least its symbols.
  """
  @spec term_query_fv(Arena.t(), Arena.term_id()) :: FVIndex.fv()
  def term_query_fv(%Arena{} = arena, term) do
    symbols = :array.get(2, walk(arena, term, @pos_base, :array.new(16, default: 0)))
    FVIndex.fv([1, 0, symbols | List.duplicate(0, 13)])
  end

  @doc "The cached subsumption feature vector of a clause item."
  @spec subsumption_fv(map()) :: FVIndex.fv()
  def subsumption_fv(%{sfv: sfv}), do: sfv

  defp walk(arena, term, base, acc) do
    {tag, _flags, _ty, left, right} = Arena.get_node(arena, term)
    acc = if tag == @tag_fvar, do: acc, else: bump(acc, 2)

    case tag do
      t when t in [@tag_const, @tag_skolem, @tag_comb] ->
        bump(acc, base + rem(left, @buckets))

      t when t in [@tag_app, @tag_eq, @tag_or] ->
        walk(arena, right, base, walk(arena, left, base, acc))

      @tag_not ->
        walk(arena, left, base, acc)

      t when t in [@tag_lam, @tag_forall] ->
        walk(arena, right, base, acc)

      _ ->
        acc
    end
  end

  defp bump(counts, lane), do: :array.set(lane, :array.get(lane, counts) + 1, counts)

  @doc """
  Whether clause item `c` subsumes clause item `d` (items carry `:lits`, optionally
  the cached `:lits_by_weight` of `Astraea.Prover`). `method` follows Leo-III's
  `--subsumption`: `:matching` (default, `ho-pattern`) matches the literals of `c`
  onto those of `d`, `:trivial` only accepts `c` whose literals all occur in `d`.
  """
  @spec subsumes?(Arena.t(), map(), map(), :matching | :trivial) :: boolean()
  def subsumes?(arena, c, d, method \\ :matching)

  def subsumes?(%Arena{}, c, d, :trivial),
    do: MapSet.size(c.lits) <= MapSet.size(d.lits) and MapSet.subset?(c.lits, d.lits)

  def subsumes?(%Arena{} = arena, c, d, :matching) do
    MapSet.size(c.lits) <= MapSet.size(d.lits) and
      (MapSet.subset?(c.lits, d.lits) or
         match_lits(arena, heaviest_first(arena, c), MapSet.to_list(d.lits), %{}))
  end

  # Heavy literals first: they have the fewest matches. Clause items cache this order.
  defp heaviest_first(_arena, %{lits_by_weight: lits}), do: lits

  defp heaviest_first(arena, %{lits: lits}) do
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
