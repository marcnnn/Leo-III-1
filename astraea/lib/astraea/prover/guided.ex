defmodule Astraea.Prover.Guided do
  @moduledoc """
  Guided (interactive) proof search, after Leo-III's `Interaction` (`--guided`).

  With the prover option `guided: true`, `Astraea.Prover` calls `interact/1` before
  every given-clause iteration. Unless asleep, it prompts `> ` on the `:guided_io`
  device and evaluates commands until one continues the search:

    * `exit` or an empty line - continue
    * `kill` - stop the run (the prover returns `{:resource_out, stats}` with
      `stats.guided == :killed`)
    * `skip [n]` - stop asking for `n` iterations, or until the end of the run
    * `step` - continue for one iteration (a trigger reports `#triggered`)
    * `queue` - the passive queue, in the order of each priority
    * `peek` - the id of the clause selected next
    * `pretty n`, `tptp n` - clause `n`, as text or as THF with its inference
    * `parents n` - the derivation of clause `n` in THF
    * `eval n m` - the key of clause `n` in priority `m` of the passive queue
    * `take n` - select passive clause `n` next (Leo-III's hot list)
    * `processed` - the active clauses

  Clause numbers are step ids. A clause that is neither passive nor active (for
  example a deleted one) is replayed from its derivation. End of input puts the
  interaction to sleep for the rest of the run, so scripted input cannot block.

  Triggers (`add_trigger/3`) are predicates on the prover state checked before
  every prompt; a firing trigger wakes the interaction, prints `#triggered`, runs
  its action and is removed.
  """

  alias Astraea.{ProofChecker, Tstp}
  alias Astraea.Engine.PassiveQueue
  alias Astraea.External.ThfPrinter

  @invalid "Invalid input, try again"
  @unrecognized "Unrecognized command. Type \"exit\" to exit interactive shell."

  @type trigger :: (map() -> boolean())
  @type t :: %__MODULE__{
          io: IO.device(),
          sleep: boolean(),
          triggers: [{trigger(), (-> any()) | nil}],
          hot: [non_neg_integer()]
        }

  defstruct io: :stdio, sleep: false, triggers: [], hot: []

  @doc "A fresh interaction reading commands from and printing to `io`."
  @spec new(IO.device()) :: t()
  def new(io \\ :stdio), do: %__MODULE__{io: io}

  @doc """
  Adds a trigger: once `pred` holds for the prover state, the interaction wakes up
  and runs `action` (a 0-arity function, or `nil`).
  """
  @spec add_trigger(t(), trigger(), (-> any()) | nil) :: t()
  def add_trigger(%__MODULE__{} = g, pred, action \\ nil),
    do: %{g | triggers: g.triggers ++ [{pred, action}]}

  @doc """
  Checks the triggers and, unless asleep, asks for commands. `state` is the prover
  state with the interaction in `state.guided`. Returns `{:kill, state}` after
  `kill`, else `{:cont, state}`.
  """
  @spec interact(map()) :: {:cont | :kill, map()}
  def interact(%{guided: %__MODULE__{} = g} = state) do
    state = %{state | guided: check_triggers(g, state)}
    if state.guided.sleep, do: {:cont, state}, else: ask(state)
  end

  @doc """
  Selects the next given clause: the first hot clause still in the passive queue,
  else the queue's own choice. Hot selections leave the round-robin schedule as
  it is (as in Leo-III). Returns `{given, passive, guided}`.
  """
  @spec select(t(), PassiveQueue.t()) :: {map(), PassiveQueue.t(), t()}
  def select(%__MODULE__{} = g, passive) do
    case Enum.drop_while(g.hot, &(not PassiveQueue.member?(passive, &1))) do
      [id | rest] ->
        {Map.fetch!(passive.items, id), PassiveQueue.delete(passive, [id]), %{g | hot: rest}}

      [] ->
        {given, passive} = PassiveQueue.pop(passive)
        {given, passive, %{g | hot: []}}
    end
  end

  defp check_triggers(%__MODULE__{} = g, state) do
    {fired, kept} = Enum.split_with(g.triggers, fn {pred, _action} -> pred.(state) end)

    Enum.each(fired, fn {_pred, action} ->
      IO.puts(g.io, "#triggered")
      if action, do: action.()
    end)

    %{g | triggers: kept, sleep: g.sleep and fired == []}
  end

  defp ask(state) do
    case IO.gets(state.guided.io, "> ") do
      line when is_binary(line) ->
        case command(String.split(line), state) do
          {:done, state} -> {:cont, state}
          {:again, state} -> ask(state)
          {:kill, state} -> {:kill, state}
        end

      _eof_or_error ->
        {:cont, update(state, &%{&1 | sleep: true})}
    end
  end

  # ---------------------------------------------------------------------------
  # Commands
  # ---------------------------------------------------------------------------

  defp command([], state), do: {:done, state}
  defp command(["exit"], state), do: {:done, state}
  defp command(["kill"], state), do: {:kill, state}
  defp command(["skip"], state), do: {:done, update(state, &%{&1 | sleep: true})}

  defp command(["skip", n], state) do
    with_int(state, [n], fn [n] ->
      m = state.iterations

      update(state, fn g ->
        %{add_trigger(g, &(&1.iterations >= m + n)) | sleep: true}
      end)
      |> then(&{:done, &1})
    end)
  end

  defp command(["step"], state) do
    m = state.iterations
    {:done, update(state, &add_trigger(&1, fn s -> s.iterations >= m + 1 end))}
  end

  defp command(["queue"], state) do
    print_queue(state)
    {:again, state}
  end

  defp command(["peek"], state) do
    case PassiveQueue.empty?(state.passive) do
      true ->
        puts(state, "<empty>")

      false ->
        {given, _passive, _g} = select(state.guided, state.passive)
        puts(state, Integer.to_string(given.id))
    end

    {:again, state}
  end

  defp command(["pretty", n], state), do: show(state, n, &pretty_line/3)
  defp command(["tptp", n], state), do: show(state, n, &tptp_line/3)

  defp command(["parents", n], state) do
    with_int(state, [n], fn [id] ->
      if Map.has_key?(state.steps, id) do
        steps = derivation(state, id)
        {arena, clauses} = Tstp.replay(state.arena, steps)
        Enum.each(steps, &puts(state, tptp_line(arena, &1, Map.fetch!(clauses, elem(&1, 1)))))
      else
        puts(state, @invalid)
      end

      {:again, state}
    end)
  end

  defp command(["eval", n, m], state) do
    with_int(state, [n, m], fn [id, prio] ->
      schedule = state.passive.schedule
      item = Map.get(state.passive.items, id) || Map.get(state.active_by_id, id)

      if item && prio >= 0 && prio < tuple_size(schedule) do
        {key, _weight} = elem(schedule, prio)
        puts(state, inspect(priority_key(key, item)))
      else
        puts(state, @invalid)
      end

      {:again, state}
    end)
  end

  defp command(["take", n], state) do
    with_int(state, [n], fn [id] ->
      if PassiveQueue.member?(state.passive, id) do
        {:again, update(state, &%{&1 | hot: &1.hot ++ [id]})}
      else
        puts(state, @invalid)
        {:again, state}
      end
    end)
  end

  defp command(["processed"], state) do
    case state.active do
      [] ->
        puts(state, "<empty>")

      active ->
        puts(state, "Processed clauses:")

        active
        |> Enum.sort_by(& &1.id)
        |> Enum.each(&puts(state, pretty_line(state.arena, step(state, &1.id), &1.lits)))
    end

    {:again, state}
  end

  defp command([cmd | _], state)
       when cmd in ~w(skip queue peek pretty tptp parents eval take processed exit kill step) do
    puts(state, @invalid)
    {:again, state}
  end

  defp command(_words, state) do
    puts(state, @unrecognized)
    {:again, state}
  end

  # ---------------------------------------------------------------------------
  # Printing
  # ---------------------------------------------------------------------------

  defp show(state, n, render) do
    with_int(state, [n], fn [id] ->
      case clause(state, id) do
        {:ok, arena, lits} -> puts(state, render.(arena, step(state, id), lits))
        :error -> puts(state, @invalid)
      end

      {:again, state}
    end)
  end

  defp print_queue(state) do
    q = state.passive
    items = PassiveQueue.to_list(q)
    puts(state, "Passive queue (#{length(items)} clauses):")

    q.schedule
    |> Tuple.to_list()
    |> Enum.with_index()
    |> Enum.each(fn {{key, weight}, i} ->
      ids = items |> Enum.sort_by(&{priority_order(key, &1), &1.id}) |> Enum.map(& &1.id)
      cur = if i == q.slot, do: " (current)", else: ""
      puts(state, "priority #{i} #{key}/#{weight}#{cur}: #{Enum.join(ids, " ")}")
    end)

    if state.guided.hot != [], do: puts(state, "hot: #{Enum.join(state.guided.hot, " ")}")

    items
    |> Enum.sort_by(& &1.id)
    |> Enum.each(&puts(state, pretty_line(state.arena, step(state, &1.id), &1.lits)))
  end

  # The value `Astraea.Engine.PassiveQueue` orders priority `key` by (before ties).
  defp priority_key(:score, item), do: item.score
  defp priority_key(:age, item), do: item.id
  defp priority_key(:weight, item), do: item.weight
  defp priority_key(:depth, item), do: item.depth

  # Full order as in `Astraea.Engine.PassiveQueue`: ties go to the newest clause,
  # except in the age queue.
  defp priority_order(:age, item), do: item.id
  defp priority_order(key, item), do: {priority_key(key, item), -item.id}

  defp pretty_line(arena, step, lits) do
    origin =
      case step do
        nil -> ""
        {:axiom, _, _} -> "  [axiom]"
        step -> "  [#{elem(step, 0)} #{inspect(ProofChecker.step_parents(step))}]"
      end

    "[#{id_of(step)}] #{ThfPrinter.clause_to_string(arena, lits)}#{origin}"
  end

  # `thf(c_<id>, Role, Clause, Source)`, named like the steps of `Astraea.Tstp`.
  defp tptp_line(arena, step, lits) do
    body = ThfPrinter.clause_to_string(arena, lits)

    case step do
      {:axiom, id, _} ->
        "thf(c_#{id}, axiom, #{body})."

      step ->
        parents = step |> ProofChecker.step_parents() |> Enum.map_join(", ", &"c_#{&1}")

        "thf(c_#{elem(step, 1)}, plain, #{body}, " <>
          "inference(#{elem(step, 0)}, [status(thm)], [#{parents}]))."
    end
  end

  defp id_of(nil), do: "?"
  defp id_of(step), do: elem(step, 1)

  # ---------------------------------------------------------------------------
  # Clause lookup
  # ---------------------------------------------------------------------------

  defp step(state, id), do: Map.get(state.steps, id)

  # The clause of step `id` with the arena its terms live in.
  defp clause(state, id) do
    cond do
      item = Map.get(state.passive.items, id) ->
        {:ok, state.arena, item.lits}

      item = Map.get(state.active_by_id, id) ->
        {:ok, state.arena, item.lits}

      Map.has_key?(state.steps, id) ->
        {arena, clauses} = Tstp.replay(state.arena, derivation(state, id))
        {:ok, arena, Map.fetch!(clauses, id)}

      true ->
        :error
    end
  end

  # The steps `id` depends on, itself included, in id order.
  defp derivation(state, id) do
    ancestors(state.steps, [id], MapSet.new())
    |> Enum.sort()
    |> Enum.map(&Map.fetch!(state.steps, &1))
  end

  defp ancestors(_steps, [], seen), do: seen

  defp ancestors(steps, [id | rest], seen) do
    if MapSet.member?(seen, id) or not Map.has_key?(steps, id) do
      ancestors(steps, rest, seen)
    else
      parents = steps |> Map.fetch!(id) |> ProofChecker.step_parents()
      ancestors(steps, parents ++ rest, MapSet.put(seen, id))
    end
  end

  # ---------------------------------------------------------------------------
  # Helpers
  # ---------------------------------------------------------------------------

  defp with_int(state, strs, fun) do
    ints = Enum.map(strs, &Integer.parse/1)

    if Enum.all?(ints, &match?({n, ""} when n >= 0, &1)) do
      fun.(Enum.map(ints, &elem(&1, 0)))
    else
      puts(state, @invalid)
      {:again, state}
    end
  end

  defp update(state, fun), do: %{state | guided: fun.(state.guided)}

  defp puts(state, line), do: IO.puts(state.guided.io, line)
end
