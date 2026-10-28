defmodule Astraea.Engine.DiscriminationTree do
  @moduledoc """
  Discrimination tree for generalization retrieval: given a target term, return
  the entries whose pattern may match it (Pillar 2 of
  `Notes/beating_zipperposition_plan.md`; McCune, "Experiments with
  Discrimination-Tree Indexing and Path Indexing for Term Retrieval", 1992).

  Patterns are flattened in preorder over the binary arena nodes, the same
  structure `Astraea.Arena.match_pattern/4` walks, into keys

    * `{:var, ty}` for a free variable (matches any one target subterm of `ty`),
    * `{:id, id}` for a ground subterm (matches only the identical hash-consed node,
      as `match_pattern/4` compares ground subterms by id),
    * `{tag, ty}` / `{tag, ty, binder}` for an application, equation, `~`, `|`,
      lambda or `forall` containing variables, followed by its children.

  Retrieval walks the tree with a stack of pending target subterms. At each target
  node it follows the variable edge of the node's type, the `{:id, node}` edge and
  the structural edge; equations are also tried with swapped sides, as the matcher
  does. Every key test is a necessary condition of `match_pattern/4`, so no match
  is lost; only repeated variables (non-linear patterns) are left to the matcher.
  Compared with `Astraea.Engine.HeadIndex`, which only discriminates on the head
  symbol, the tree also rejects candidates on types, arguments and ground
  subterms at every depth.

  Entries are `{group, pattern, value}` with `value` a map carrying the clause
  `:id`, as in `HeadIndex`. Lookups return values newest first.
  """

  import Bitwise

  alias Astraea.Arena

  @tag_fvar 3
  @tag_app 4
  @tag_lam 5
  @tag_eq 6
  @tag_not 7
  @tag_or 8
  @tag_forall 9

  # Must agree with `Astraea.Arena`.
  @flag_has_fvar 0x02

  # A trie node is `{seqs, children}`; `seqs` are the entries ending here.
  defstruct roots: %{}, entries: %{}, by_id: %{}, next: 0

  @type t :: %__MODULE__{}

  @spec new() :: t()
  def new, do: %__MODULE__{}

  @spec size(t()) :: non_neg_integer()
  def size(%__MODULE__{entries: entries}), do: map_size(entries)

  @spec empty?(t()) :: boolean()
  def empty?(%__MODULE__{entries: entries}), do: map_size(entries) == 0

  @doc "The preorder key sequence of a pattern."
  @spec keys(Arena.t(), Arena.term_id()) :: [term()]
  def keys(%Arena{} = arena, pattern), do: arena |> keys(pattern, []) |> Enum.reverse()

  defp keys(arena, term, acc) do
    {tag, flags, ty, left, right} = Arena.get_node(arena, term)

    cond do
      tag == @tag_fvar ->
        [{:var, ty} | acc]

      band(flags, @flag_has_fvar) == 0 ->
        [{:id, term} | acc]

      tag in [@tag_app, @tag_eq, @tag_or] ->
        keys(arena, right, keys(arena, left, [{tag, ty} | acc]))

      tag == @tag_not ->
        keys(arena, left, [{tag, ty} | acc])

      tag in [@tag_lam, @tag_forall] ->
        keys(arena, right, [{tag, ty, left} | acc])

      true ->
        [{:id, term} | acc]
    end
  end

  @spec put(t(), Arena.t(), term(), Arena.term_id(), map()) :: t()
  def put(%__MODULE__{} = index, %Arena{} = arena, group, pattern, value) do
    seq = index.next
    path = keys(arena, pattern)
    root = Map.get(index.roots, group, {[], %{}})

    %{
      index
      | roots: Map.put(index.roots, group, insert(root, path, seq)),
        entries: Map.put(index.entries, seq, {group, path, value}),
        by_id: Map.update(index.by_id, value.id, [seq], &[seq | &1]),
        next: seq + 1
    }
  end

  defp insert({seqs, kids}, [], seq), do: {[seq | seqs], kids}

  defp insert({seqs, kids}, [key | rest], seq) do
    child = Map.get(kids, key, {[], %{}})
    {seqs, Map.put(kids, key, insert(child, rest, seq))}
  end

  @doc "Entries of `group` whose pattern may match `target`, newest first."
  @spec lookup(t(), Arena.t(), term(), Arena.term_id()) :: [map()]
  def lookup(%__MODULE__{} = index, %Arena{} = arena, group, target) do
    case Map.fetch(index.roots, group) do
      :error ->
        []

      {:ok, root} ->
        arena
        |> retrieve(root, [target], [])
        |> Enum.sort(:desc)
        |> Enum.dedup()
        |> Enum.map(fn seq -> elem(Map.fetch!(index.entries, seq), 2) end)
    end
  end

  defp retrieve(_arena, {seqs, _kids}, [], acc), do: seqs ++ acc

  defp retrieve(arena, {_seqs, kids}, [term | rest], acc) do
    {tag, _flags, ty, left, right} = Arena.get_node(arena, term)

    acc =
      case Map.fetch(kids, {:var, ty}) do
        {:ok, child} -> retrieve(arena, child, rest, acc)
        :error -> acc
      end

    acc =
      case Map.fetch(kids, {:id, term}) do
        {:ok, child} -> retrieve(arena, child, rest, acc)
        :error -> acc
      end

    case tag do
      t when t in [@tag_app, @tag_or] ->
        follow(arena, kids, {tag, ty}, [left, right | rest], acc)

      @tag_eq ->
        acc = follow(arena, kids, {tag, ty}, [left, right | rest], acc)
        if left == right, do: acc, else: follow(arena, kids, {tag, ty}, [right, left | rest], acc)

      @tag_not ->
        follow(arena, kids, {tag, ty}, [left | rest], acc)

      t when t in [@tag_lam, @tag_forall] ->
        follow(arena, kids, {tag, ty, left}, [right | rest], acc)

      _ ->
        acc
    end
  end

  defp follow(arena, kids, key, stack, acc) do
    case Map.fetch(kids, key) do
      {:ok, child} -> retrieve(arena, child, stack, acc)
      :error -> acc
    end
  end

  @doc "Drops the entries of the clauses in `ids`."
  @spec reject(t(), MapSet.t()) :: t()
  def reject(%__MODULE__{} = index, ids) do
    Enum.reduce(ids, index, fn id, idx ->
      case Map.pop(idx.by_id, id) do
        {nil, _} -> idx
        {seqs, by_id} -> Enum.reduce(seqs, %{idx | by_id: by_id}, &delete_seq(&2, &1))
      end
    end)
  end

  defp delete_seq(index, seq) do
    {{group, path, _value}, entries} = Map.pop!(index.entries, seq)

    roots =
      case delete(Map.fetch!(index.roots, group), path, seq) do
        nil -> Map.delete(index.roots, group)
        root -> Map.put(index.roots, group, root)
      end

    %{index | roots: roots, entries: entries}
  end

  # Removes `seq` along `path`; returns `nil` for a node left without entries.
  defp delete({seqs, kids}, [], seq), do: prune({List.delete(seqs, seq), kids})

  defp delete({seqs, kids}, [key | rest], seq) do
    kids =
      case delete(Map.fetch!(kids, key), rest, seq) do
        nil -> Map.delete(kids, key)
        child -> Map.put(kids, key, child)
      end

    prune({seqs, kids})
  end

  defp prune({[], kids}) when map_size(kids) == 0, do: nil
  defp prune(node), do: node

  @spec values(t()) :: [map()]
  def values(%__MODULE__{} = index) do
    index.entries |> Enum.sort_by(&elem(&1, 0), :desc) |> Enum.map(fn {_, {_, _, v}} -> v end)
  end
end
