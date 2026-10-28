defmodule Astraea.Engine.Demodulator do
  @moduledoc """
  Demodulation (Leo-III `SimplificationControl.rewriteSimp` / `rewritable`): rewriting
  with positive unit equations `l = r` as rules `lσ -> rσ` wherever the instance is
  KBO-decreasing (`lσ > rσ`). Orientable equations give one rule; incomparable ones
  give both directions and act as ordered rewriting (this covers commutativity, the
  part of Leo-III's `acSimp` that is expressible without a new kernel rule).

  This module only finds redexes; the prover turns each one into the existing
  kernel steps (`:subst` on the unit, then `:paramod` on the target literal). As in
  `Astraea.ProofChecker.replace_subterm/4`, a step rewrites every occurrence of
  the redex in one literal, and never looks below a `forall`.

  Completeness side condition (Bachmair-Ganzinger, as in E): a whole side `s` of a
  positive equation `s = t` is only rewritten if the rule is strictly more general
  than `s` (the matcher is not a renaming) or `rσ < t`.
  """

  alias Astraea.Arena
  alias Astraea.Engine.HeadIndex

  @tag_fvar 3
  @tag_app 4
  @tag_lam 5
  @tag_eq 6
  @tag_not 7
  @tag_or 8

  @doc """
  The rules of a positive unit equation clause item: maps with the clause `:id`,
  the clause `:item`, its equation `:eq` and the directed `:lhs`/`:rhs`.
  """
  @spec rules(Arena.t(), map()) :: [map()]
  def rules(%Arena{} = arena, item, opts \\ []) do
    bool_rules? = Keyword.get(opts, :bool_rules, true)
    case MapSet.to_list(item.lits) do
      [{:pos, eq}] ->
        case Arena.get_node(arena, eq) do
          {@tag_eq, _, _, l, r} ->
            directions =
              case Arena.kbo_compare(arena, l, r) do
                :gt -> [{l, r}]
                :lt -> [{r, l}]
                :inc -> [{l, r}, {r, l}]
                :eq -> []
              end

            for {lhs, rhs} <- directions, not var?(arena, lhs) do
              %{id: item.id, item: item, eq: eq, lhs: lhs, rhs: rhs, kind: :eq}
            end

          _ ->
            if bool_rules? and Arena.type_of(arena, eq) == Arena.ty_o() and not var?(arena, eq) and
                 not Arena.truth_const?(arena, eq, "$true") and
                 not Arena.truth_const?(arena, eq, "$false") do
              case Arena.lookup_const(arena, "$true", :o) do
                nil ->
                  []

                true_const ->
                  [%{id: item.id, item: item, eq: nil, lhs: eq, rhs: true_const, kind: :pos_bool}]
              end
            else
              []
            end
        end

      [{:neg, p}] ->
        case Arena.get_node(arena, p) do
          {@tag_eq, _, _, _, _} ->
            []

          _ ->
            if Arena.type_of(arena, p) == Arena.ty_o() and not var?(arena, p) and
                 not Arena.truth_const?(arena, p, "$true") and
                 not Arena.truth_const?(arena, p, "$false") do
              case Arena.lookup_const(arena, "$false", :o) do
                nil ->
                  []

                false_const ->
                  [%{id: item.id, item: item, eq: nil, lhs: p, rhs: false_const, kind: :neg_bool}]
              end
            else
              []
            end
        end

      _ ->
        []
    end
  end

  @spec add_rules(HeadIndex.t(), Arena.t(), [map()]) :: HeadIndex.t()
  def add_rules(index, %Arena{} = arena, rules) do
    Enum.reduce(rules, index, &HeadIndex.put(&2, arena, :rule, &1.lhs, &1))
  end

  @doc """
  The first redex of `item` for the rules in `index`:
  `{:ok, arena, %{rule:, subst:, lit:, from:, to:}}`, or `{:none, arena}`.
  """
  @spec find_redex(Arena.t(), HeadIndex.t(), map()) ::
          {:ok, Arena.t(), map()} | {:none, Arena.t()}
  def find_redex(%Arena{} = arena, index, item) do
    Enum.reduce_while(item.lits, {:none, arena}, fn {_pol, atom} = lit, {:none, ar} ->
      ar
      |> redex_positions(atom)
      |> Enum.reduce_while({:none, ar}, fn sub, {:none, ar} ->
        case rewrite_at(ar, index, item, lit, sub) do
          {:ok, _, _} = found -> {:halt, found}
          none -> {:cont, none}
        end
      end)
      |> case do
        {:ok, _, _} = found -> {:halt, found}
        none -> {:cont, none}
      end
    end)
  end

  defp rewrite_at(arena, index, item, lit, sub) do
    index
    |> HeadIndex.lookup(arena, :rule, sub)
    |> Enum.reduce_while({:none, arena}, fn rule, {:none, ar} ->
      is_bool_rule = Map.get(rule, :kind) in [:pos_bool, :neg_bool]

      with true <- rule.id != item.id,
           true <- not is_bool_rule or sub != elem(lit, 1),
           {:ok, subst} <- Arena.match_pattern(ar, rule.lhs, sub),
           true <- idempotent?(ar, subst),
           {ar, to} = Arena.subst_fvar(ar, rule.rhs, subst),
           true <- is_bool_rule or Arena.kbo_compare(ar, sub, to) == :gt,
           true <- side_condition?(ar, lit, sub, to, subst, is_bool_rule) do
        {:halt, {:ok, ar, %{rule: rule, subst: subst, lit: lit, from: sub, to: to}}}
      else
        _ -> {:cont, {:none, ar}}
      end
    end)
  end

  defp side_condition?(_arena, _lit, _sub, _to, _subst, true), do: true

  defp side_condition?(arena, lit, sub, to, subst, false),
    do: side_condition?(arena, lit, sub, to, subst)

  defp side_condition?(arena, {:pos, atom}, sub, to, subst) do
    case Arena.get_node(arena, atom) do
      {@tag_eq, _, _, s, t} when sub in [s, t] ->
        other = if sub == s, do: t, else: s
        not renaming?(arena, subst) or Arena.kbo_compare(arena, other, to) == :gt

      _ ->
        true
    end
  end

  defp side_condition?(_arena, {:neg, _}, _sub, _to, _subst), do: true

  defp renaming?(arena, subst) do
    targets = Map.values(subst)
    Enum.all?(targets, &var?(arena, &1)) and length(Enum.uniq(targets)) == length(targets)
  end

  @doc """
  Subterms of `term` a rewrite step can replace: no variables, no loose bound
  variables, not below `forall` (outermost first).
  """
  @spec redex_positions(Arena.t(), Arena.term_id()) :: [Arena.term_id()]
  def redex_positions(%Arena{} = arena, term) do
    arena |> positions(term, []) |> Enum.reverse() |> Enum.uniq()
  end

  defp positions(arena, term, acc) do
    {tag, _flags, _ty, left, right} = Arena.get_node(arena, term)

    acc =
      if tag != @tag_fvar and not Arena.has_loose_bvar?(arena, term, 0),
        do: [term | acc],
        else: acc

    case tag do
      t when t in [@tag_app, @tag_eq, @tag_or] ->
        positions(arena, right, positions(arena, left, acc))

      @tag_not ->
        positions(arena, left, acc)

      @tag_lam ->
        positions(arena, right, acc)

      _ ->
        acc
    end
  end

  @doc """
  Whether no variable bound by `subst` occurs in its range. `Arena.subst_fvar/3`
  (and so the kernel's `:subst`) applies a substitution triangularly, which agrees
  with the simultaneous substitution a matcher computes exactly in this case.
  """
  @spec idempotent?(Arena.t(), Arena.subst()) :: boolean()
  def idempotent?(%Arena{} = arena, subst) do
    Enum.all?(subst, fn {_var, term} ->
      arena |> Arena.free_vars(term) |> Enum.all?(fn {id, _ty} -> not is_map_key(subst, id) end)
    end)
  end

  defp var?(arena, term), do: match?({@tag_fvar, _, _, _, _}, Arena.get_node(arena, term))
end
