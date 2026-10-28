defmodule Astraea.DotGraph do
  @moduledoc """
  Graphviz dot output, after Leo-III's `leo.modules.output.DotGraph`.

  Leo-III's class draws a single term as its spine/argument graph and is not
  reachable from the command line. Astraea offers the same for arena terms
  (`term/2`; hash-consing makes it a DAG, every shared subterm is drawn once) and,
  more usefully, draws proofs: `proof/3` renders a list of `Astraea.ProofChecker`
  steps as their derivation DAG, one node per step labelled with its id, rule
  and conclusion, and an edge from every premise to its conclusion.

      dot -Tsvg proof.dot -o proof.svg
  """

  alias Astraea.{Arena, ProofChecker, Tstp}
  alias Astraea.External.ThfPrinter

  # Node tags (u8) matching `Astraea.Arena`
  @tag_const 1
  @tag_bvar 2
  @tag_fvar 3
  @tag_app 4
  @tag_lam 5
  @tag_eq 6
  @tag_not 7
  @tag_or 8
  @tag_forall 9
  @tag_skolem 10
  @tag_comb 11

  @default_max_label 160

  @doc """
  Renders the derivation DAG of `steps` (as in `{:proved, steps, stats}`, with
  `stats.arena`). Options:
    * `:clauses` - print each step's conclusion in THF (default `true`)
    * `:max_label` - truncate conclusions to this many characters (default 160)
    * `:name` - graph name (default `"proof"`)

  Input clauses are filled grey, the empty clause has a double border.
  """
  @spec proof(Arena.t(), [ProofChecker.step()], keyword()) :: String.t()
  def proof(%Arena{} = arena, steps, opts \\ []) do
    show = Keyword.get(opts, :clauses, true)
    max = Keyword.get(opts, :max_label, @default_max_label)
    {arena, clauses} = Tstp.replay(arena, steps)

    nodes =
      Enum.map(steps, fn step ->
        id = elem(step, 1)
        clause = Map.fetch!(clauses, id)

        text =
          if show, do: ["\n", truncate(ThfPrinter.clause_to_string(arena, clause), max)], else: []

        label = IO.iodata_to_binary([Integer.to_string(id), ": ", rule(step), text])

        attrs =
          [
            ["label=", quote_id(label)],
            if(elem(step, 0) in [:axiom, :choice],
              do: "style=filled, fillcolor=lightgrey",
              else: []
            ),
            if(MapSet.size(clause) == 0, do: "peripheries=2", else: [])
          ]
          |> Enum.reject(&(&1 == []))
          |> Enum.intersperse(", ")

        ["  ", node_id(id), " [", attrs, "];\n"]
      end)

    edges =
      for step <- steps, parent <- ProofChecker.step_parents(step) do
        ["  ", node_id(parent), " -> ", node_id(elem(step, 1)), ";\n"]
      end

    graph(Keyword.get(opts, :name, "proof"), [
      "  node [shape=box, fontname=\"monospace\"];\n",
      nodes,
      edges
    ])
  end

  @doc """
  Renders the term DAG of `term_id`: one node per distinct subterm (symbols,
  variables, `@`, binders with their domain type, connectives) and edges to its
  children, labelled `fun`/`arg` for applications.
  """
  @spec term(Arena.t(), Arena.term_id(), keyword()) :: String.t()
  def term(%Arena{} = arena, term_id, opts \\ []) do
    {_seen, lines} = term_nodes(arena, term_id, MapSet.new(), [])
    graph(Keyword.get(opts, :name, "term"), Enum.reverse(lines))
  end

  defp term_nodes(arena, id, seen, acc) do
    if MapSet.member?(seen, id) do
      {seen, acc}
    else
      seen = MapSet.put(seen, id)
      {tag, _flags, ty, left, right} = Arena.get_node(arena, id)

      acc = [
        ["  ", node_id(id), " [label=", quote_id(term_label(arena, tag, ty, left)), "];\n"] | acc
      ]

      children =
        case tag do
          @tag_app -> [{left, "fun"}, {right, "arg"}]
          t when t in [@tag_eq, @tag_or] -> [{left, nil}, {right, nil}]
          @tag_not -> [{left, nil}]
          t when t in [@tag_lam, @tag_forall] -> [{right, nil}]
          _ -> []
        end

      Enum.reduce(children, {seen, acc}, fn {child, label}, {seen, acc} ->
        edge_attr = if label, do: [" [label=", quote_id(label), "]"], else: []
        acc = [["  ", node_id(id), " -> ", node_id(child), edge_attr, ";\n"] | acc]
        term_nodes(arena, child, seen, acc)
      end)
    end
  end

  defp term_label(arena, tag, ty, left) do
    case tag do
      @tag_const ->
        Map.fetch!(arena.symbol_names, left)

      @tag_skolem ->
        "sk_" <> String.downcase(String.pad_leading(Integer.to_string(left, 16), 8, "0"))

      @tag_bvar ->
        "#" <> Integer.to_string(left)

      @tag_fvar ->
        "V" <> Integer.to_string(left)

      @tag_app ->
        "@"

      @tag_lam ->
        IO.iodata_to_binary(["^ [", ThfPrinter.type(arena, left), "]"])

      @tag_forall ->
        IO.iodata_to_binary(["! [", ThfPrinter.type(arena, left), "]"])

      @tag_eq ->
        "="

      @tag_not ->
        "~"

      @tag_or ->
        "|"

      @tag_comb ->
        IO.iodata_to_binary([comb_name(left), ": ", ThfPrinter.type(arena, ty)])
    end
  end

  defp comb_name(1), do: "S"
  defp comb_name(2), do: "K"
  defp comb_name(3), do: "I"
  defp comb_name(4), do: "B"
  defp comb_name(5), do: "C"

  defp rule({:cnf, _id, _p, _lit, rule}), do: "cnf " <> cnf_rule(rule)
  defp rule(step), do: Atom.to_string(elem(step, 0))

  defp cnf_rule({:forall, _fvar}), do: "forall"
  defp cnf_rule({rule, side}) when is_atom(side), do: "#{rule}_#{side}"
  defp cnf_rule(rule) when is_atom(rule), do: Atom.to_string(rule)

  defp truncate(text, max) do
    if String.length(text) > max, do: String.slice(text, 0, max) <> "...", else: text
  end

  defp graph(name, body),
    do: IO.iodata_to_binary(["digraph ", quote_id(name), " {\n", body, "}\n"])

  defp node_id(id), do: ["n", Integer.to_string(id)]

  defp quote_id(text) do
    escaped =
      text
      |> String.replace("\\", "\\\\")
      |> String.replace("\"", "\\\"")
      |> String.replace("\n", "\\n")

    ["\"", escaped, "\""]
  end
end
