defmodule Astraea.DotGraphTest do
  use ExUnit.Case, async: true

  alias Astraea.{DotGraph, ProofChecker, Prover, TptpLower}

  @src """
  thf(p_type, type, p: $i > $o).
  thf(q_type, type, q: $i > $o).
  thf(a_type, type, a: $i).
  thf(ax1, axiom, p @ a).
  thf(ax2, axiom, ! [X: $i]: ((p @ X) => (q @ X))).
  thf(c, conjecture, q @ a).
  """

  defp node_lines(dot), do: dot |> String.split("\n") |> Enum.filter(&(&1 =~ ~r/^  n\d+ \[/))
  defp edge_lines(dot), do: dot |> String.split("\n") |> Enum.filter(&(&1 =~ ~r/^  n\d+ -> n\d+/))

  test "renders a verified proof as its derivation DAG" do
    {:proved, steps, stats} = Prover.prove_string(@src, timeout_ms: 3_000)
    dot = DotGraph.proof(stats.arena, steps)

    assert String.starts_with?(dot, "digraph \"proof\" {\n")
    assert String.ends_with?(dot, "}\n")
    assert length(node_lines(dot)) == length(steps)

    parents = steps |> Enum.flat_map(&ProofChecker.step_parents/1) |> length()
    assert length(edge_lines(dot)) == parents

    # The empty clause is marked, input clauses are filled.
    assert [refutation] = Enum.filter(node_lines(dot), &(&1 =~ "peripheries=2"))
    assert refutation =~ "$false"
    assert Enum.any?(node_lines(dot), &(&1 =~ "axiom\\n" and &1 =~ "fillcolor=lightgrey"))

    terse = DotGraph.proof(stats.arena, steps, clauses: false, name: "p")
    refute terse =~ "$false"
    assert String.starts_with?(terse, "digraph \"p\" {")
  end

  test "is accepted by graphviz when it is installed" do
    case System.find_executable("dot") do
      nil ->
        :ok

      dot_exe ->
        {:proved, steps, stats} = Prover.prove_string(@src, timeout_ms: 3_000)

        path =
          Path.join(System.tmp_dir!(), "astraea_dot_#{System.unique_integer([:positive])}.dot")

        File.write!(path, DotGraph.proof(stats.arena, steps))
        on_exit(fn -> File.rm(path) end)
        assert {_svg, 0} = System.cmd(dot_exe, ["-Tsvg", path], stderr_to_stdout: true)
    end
  end

  test "draws a term DAG with shared subterms once" do
    {:ok, lowered} = TptpLower.from_string(@src <> "thf(shared, axiom, (q @ a) | ~ (q @ a)).\n")
    {"shared", _role, id} = List.keyfind(lowered.axioms, "shared", 0)
    dot = DotGraph.term(lowered.arena, id)

    # `|`, `~`, `@`, `q`, `a`: the atom `q @ a` is one node with two parents.
    assert length(node_lines(dot)) == 5
    assert length(edge_lines(dot)) == 5
    assert dot =~ "[label=\"|\"]"
    assert dot =~ "[label=\"fun\"]"
  end
end
