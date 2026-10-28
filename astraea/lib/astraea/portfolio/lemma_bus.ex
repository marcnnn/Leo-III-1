defmodule Astraea.Portfolio.LemmaBus do
  @moduledoc """
  Lemma sharing between the internal workers of one portfolio race (Pillar 5 of
  `Notes/beating_zipperposition_plan.md`).

  There is no central process: `connect/1` tells every worker the pids of its
  siblings, and a worker sends each derived lemma to them directly, so publishing
  never waits on a shared mailbox. A lemma travels as an
  `Astraea.Engine.LemmaTransfer` payload (the clause with its whole derivation);
  the receiver replays the derivation through the kernel before using the clause,
  and it stays part of every refutation built on it.
  """

  @doc "Sends every worker in `pids` the list of its siblings."
  @spec connect([pid()]) :: :ok
  def connect(pids) do
    Enum.each(pids, fn pid -> send(pid, {:astraea_peers, List.delete(pids, pid)}) end)
  end

  @doc "Sends `payload` to `peers`."
  @spec publish([pid()], map()) :: :ok
  def publish(peers, payload) do
    Enum.each(peers, &send(&1, {:astraea_lemma, payload}))
  end

  @doc """
  Collects the messages that arrived since the last call without blocking:
  `{peers, payloads}` with `peers` the new sibling list (or `nil`).
  """
  @spec drain() :: {[pid()] | nil, [map()]}
  def drain, do: drain(nil, [])

  defp drain(peers, acc) do
    receive do
      {:astraea_peers, new_peers} -> drain(new_peers, acc)
      {:astraea_lemma, payload} -> drain(peers, [payload | acc])
    after
      0 -> {peers, Enum.reverse(acc)}
    end
  end
end
