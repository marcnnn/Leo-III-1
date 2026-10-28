defmodule Astraea.GuidedTest do
  use ExUnit.Case, async: true

  alias Astraea.{ProofChecker, Prover}

  @chain """
  thf(i_t, type, a: $i). thf(f_t, type, f: $i > $i).
  thf(p_t, type, p: $i > $o). thf(q_t, type, q: $i > $o). thf(r_t, type, r: $i > $o).
  thf(a1, axiom, p @ a). thf(a2, axiom, ! [X: $i]: ((p @ X) => (q @ (f @ X)))).
  thf(a3, axiom, ! [X: $i]: ((q @ X) => (r @ X))).
  thf(c, conjecture, r @ (f @ a)).
  """

  @csa """
  thf(p_t, type, p: $i > $o). thf(a_t, type, a: $i). thf(b_t, type, b: $i).
  thf(ax, axiom, p @ a). thf(c, conjecture, p @ b).
  """

  # Runs the prover on `src` with `script` as input; returns the result and output.
  defp guided(src, script, opts \\ []) do
    {:ok, io} = StringIO.open(script, capture_prompt: true)
    result = Prover.prove_string(src, [guided: true, guided_io: io, timeout_ms: 2_000] ++ opts)
    {:ok, {_rest, out}} = StringIO.close(io)
    {result, out}
  end

  defp assert_kernel_proof(result) do
    assert {:proved, steps, stats} = result
    assert :ok == ProofChecker.verify_refutation(stats.arena, steps)
  end

  # Clause ids printed by `queue` for its first priority.
  defp queue_ids(out) do
    [_, ids] = Regex.run(~r/priority 0 [^:]*: ([\d ]*)/, out)
    ids |> String.split() |> Enum.map(&String.to_integer/1)
  end

  test "without :guided the prover does not read input" do
    assert_kernel_proof(Prover.prove_string(@chain, timeout_ms: 2_000))
  end

  test "exit continues and a guided run still finds a verified proof" do
    {result, out} = guided(@chain, String.duplicate("exit\n", 50))
    assert_kernel_proof(result)
    assert out =~ "> "
  end

  test "end of input puts the interaction to sleep" do
    {result, out} = guided(@chain, "")
    assert_kernel_proof(result)
    assert out == "> "
  end

  test "kill stops the run with a recognisable result" do
    {result, out} = guided(@chain, "kill\n")
    assert {:resource_out, %{guided: :killed, iterations: 0}} = result
    assert out == "> "
  end

  test "unknown commands and malformed arguments are reported" do
    {_result, out} = guided(@chain, "frobnicate\npretty x\neval 1\nkill\n")
    assert out =~ ~s(Unrecognized command. Type "exit" to exit interactive shell.)
    assert length(String.split(out, "Invalid input, try again")) == 3
  end

  test "step continues one iteration and fires a trigger" do
    {result, out} = guided(@chain, "step\nkill\n")
    assert {:resource_out, %{guided: :killed, iterations: 1}} = result
    assert out =~ "#triggered"
  end

  test "skip n sleeps for n iterations, skip sleeps to the end" do
    {result, out} = guided(@chain, "skip 2\nkill\n")
    assert {:resource_out, %{guided: :killed, iterations: 2}} = result
    assert out =~ "#triggered"

    {result, out} = guided(@chain, "skip\nkill\n")
    assert_kernel_proof(result)
    assert out == "> "
  end

  test "queue, peek, pretty, tptp, eval and processed show the search state" do
    {_result, out} = guided(@chain, "queue\npeek\nkill\n")
    [first | _] = ids = queue_ids(out)
    assert out =~ ~r/> #{first}\n/
    id = List.last(ids)

    script = "pretty #{id}\ntptp #{id}\neval #{id} 1\nprocessed\nstep\nprocessed\nkill\n"
    {_result, out} = guided(@chain, script)
    assert out =~ ~r/\[#{id}\] .*/
    assert out =~ ~r/thf\(c_#{id}, (axiom|plain), .*\)\./
    # Priority 1 of the default `[score: 3, age: 1]` queue is the age, i.e. the id.
    assert out =~ ~r/> #{id}\n/
    assert out =~ "<empty>"
    assert out =~ "Processed clauses:"
  end

  test "parents prints the derivation of a clause in THF" do
    {_result, out} = guided(@chain, "skip 3\nqueue\nkill\n")
    id = out |> queue_ids() |> Enum.max()

    {_result, out} = guided(@chain, "skip 3\nparents #{id}\nkill\n")
    assert out =~ ~r/thf\(c_#{id}, plain, .*inference\(\w+, \[status\(thm\)\], \[c_\d+/
    assert out =~ ~r/thf\(c_\d+, axiom, /
  end

  test "take selects the chosen clause next without breaking the search" do
    {_result, out} = guided(@chain, "queue\nkill\n")
    ids = queue_ids(out)
    last = List.last(ids)
    assert hd(ids) != last

    {result, out} = guided(@chain, "take #{last}\npeek\nexit\nprocessed\nexit\n")
    assert out =~ ~r/> #{last}\n/
    assert out =~ ~r/Processed clauses:\n\[#{last}\] /
    assert_kernel_proof(result)
  end

  test "take rejects clauses that are not passive" do
    {_result, out} = guided(@chain, "take 999999\nkill\n")
    assert out =~ "Invalid input, try again"
  end

  test "the deadline does not end a guided run, the iteration limit does" do
    {result, _out} = guided(@csa, "skip\n", timeout_ms: 0, max_iterations: 1)
    assert {:resource_out, %{iterations: 1}} = result
    assert {:resource_out, %{iterations: 0}} = Prover.prove_string(@csa, timeout_ms: 0)
  end
end
