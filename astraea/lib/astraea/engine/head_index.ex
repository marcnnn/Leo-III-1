defmodule Astraea.Engine.HeadIndex do
  @moduledoc """
  Clause-carrying entries keyed by the head symbol of a pattern term, a one-level
  discrimination index (Leo-III keeps its rewrite rules and units in similar
  symbol-keyed maps). A pattern can only match a target with the same rigid head,
  so a lookup returns the entries filed under the target's head plus those whose
  pattern has a flexible (variable) head.

  Entries are `{group, pattern, value}`; `group` separates e.g. positive from
  negative units. Values must be maps carrying the clause `:id`.
  """

  alias Astraea.Arena

  @tag_const 1
  @tag_fvar 3
  @tag_app 4
  @tag_eq 6
  @tag_skolem 10
  @tag_comb 11

  @type t :: %{term() => [map()]}

  @spec new() :: t()
  def new, do: %{}

  @doc "Head key of a term: rigid symbol, `:flex` for a variable head, else the node tag."
  @spec head(Arena.t(), Arena.term_id()) :: term()
  def head(%Arena{} = arena, term_id) do
    case Arena.get_node(arena, term_id) do
      {@tag_app, _, _, fun, _} -> head(arena, fun)
      {@tag_fvar, _, _, _, _} -> :flex
      {tag, _, _, sym, _} when tag in [@tag_const, @tag_skolem, @tag_comb] -> {tag, sym}
      {@tag_eq, _, _, lhs, _} -> {@tag_eq, Arena.type_of(arena, lhs)}
      {tag, _, _, _, _} -> tag
    end
  end

  @spec put(t(), Arena.t(), term(), Arena.term_id(), map()) :: t()
  def put(index, %Arena{} = arena, group, pattern, value) do
    Map.update(index, {group, head(arena, pattern)}, [value], &[value | &1])
  end

  @doc "Entries of `group` whose pattern may match `target`."
  @spec lookup(t(), Arena.t(), term(), Arena.term_id()) :: [map()]
  def lookup(index, %Arena{} = arena, group, target) do
    flex = Map.get(index, {group, :flex}, [])

    case head(arena, target) do
      :flex -> flex
      key -> Map.get(index, {group, key}, []) ++ flex
    end
  end

  @doc "Drops the entries of the clauses in `ids`."
  @spec reject(t(), MapSet.t()) :: t()
  def reject(index, ids) do
    if MapSet.size(ids) == 0,
      do: index,
      else: Map.new(index, fn {k, vs} -> {k, Enum.reject(vs, &MapSet.member?(ids, &1.id))} end)
  end

  @spec values(t()) :: [map()]
  def values(index), do: index |> Map.values() |> Enum.concat()
end
