defmodule Astraea.Engine.PassiveQueue do
  @moduledoc """
  Passive (unprocessed) clause set as a multi-priority queue, after Leo-III's
  `MultiPriorityQueue` with weighted round-robin selection (`State.nextUnprocessed`).

  Every priority is a `:gb_sets` ordered by `{key, id}`; selection takes `weight`
  clauses from one priority before moving on to the next, so `[score: 3, age: 1]`
  is the classic pick-given ratio of three best-scored clauses per oldest one.
  Insertion, selection and removal are O(p log n) for p priorities.
  """

  @type key :: :score | :age | :weight | :depth
  @type t :: %__MODULE__{
          items: %{non_neg_integer() => map()},
          queues: tuple(),
          schedule: tuple(),
          slot: non_neg_integer(),
          taken: non_neg_integer()
        }

  defstruct items: %{}, queues: {}, schedule: {}, slot: 0, taken: 0

  @doc "A queue selecting by `ratio`, a list of `{priority, weight}` pairs."
  @spec new([{key(), pos_integer()}]) :: t()
  def new(ratio \\ [score: 3, age: 1]) when ratio != [] do
    %__MODULE__{
      queues: ratio |> Enum.map(fn _ -> :gb_sets.empty() end) |> List.to_tuple(),
      schedule: List.to_tuple(ratio)
    }
  end

  @spec size(t()) :: non_neg_integer()
  def size(%__MODULE__{items: items}), do: map_size(items)

  @spec empty?(t()) :: boolean()
  def empty?(%__MODULE__{items: items}), do: map_size(items) == 0

  @spec member?(t(), non_neg_integer()) :: boolean()
  def member?(%__MODULE__{items: items}, id), do: is_map_key(items, id)

  @spec insert(t(), map()) :: t()
  def insert(%__MODULE__{} = q, item) do
    %{q | items: Map.put(q.items, item.id, item), queues: map_queues(q, item, &:gb_sets.add/2)}
  end

  @doc "Removes the clauses with the given ids (absent ids are ignored)."
  @spec delete(t(), Enumerable.t()) :: t()
  def delete(%__MODULE__{} = q, ids) do
    Enum.reduce(ids, q, fn id, acc ->
      case Map.pop(acc.items, id) do
        {nil, _} -> acc
        {item, items} -> %{acc | items: items, queues: map_queues(acc, item, &:gb_sets.delete/2)}
      end
    end)
  end

  @doc "Pops the next given clause according to the selection schedule."
  @spec pop(t()) :: {map(), t()} | :empty
  def pop(%__MODULE__{} = q) do
    if empty?(q) do
      :empty
    else
      {_key, weight} = elem(q.schedule, q.slot)
      {_, id} = :gb_sets.smallest(elem(q.queues, q.slot))
      item = Map.fetch!(q.items, id)
      q = delete(q, [id])

      q =
        if q.taken + 1 >= weight do
          %{q | slot: rem(q.slot + 1, tuple_size(q.schedule)), taken: 0}
        else
          %{q | taken: q.taken + 1}
        end

      {item, q}
    end
  end

  @doc "The `n` best clauses of the first priority, without removing them."
  @spec take_best(t(), non_neg_integer()) :: [map()]
  def take_best(%__MODULE__{} = q, n) do
    q.queues
    |> elem(0)
    |> :gb_sets.to_list()
    |> Enum.take(n)
    |> Enum.map(fn {_, id} -> Map.fetch!(q.items, id) end)
  end

  @spec to_list(t()) :: [map()]
  def to_list(%__MODULE__{items: items}), do: Map.values(items)

  defp map_queues(q, item, fun) do
    q.schedule
    |> Tuple.to_list()
    |> Enum.with_index()
    |> Enum.reduce(q.queues, fn {{key, _w}, i}, queues ->
      put_elem(queues, i, fun.({priority(key, item), item.id}, elem(queues, i)))
    end)
  end

  # Ties go to the newest clause (its id is larger), except in the age queue.
  defp priority(:score, item), do: {item.score, -item.id}
  defp priority(:age, item), do: item.id
  defp priority(:weight, item), do: {item.weight, -item.id}
  defp priority(:depth, item), do: {item.depth, -item.id}
end
