defmodule NimbleThf.Printer do
  @moduledoc """
  Prints the `NimbleThf.Parser` AST back to THF, parenthesising every compound
  subformula. Reparsing the output with `Tptp` therefore pins down exactly the tree
  the AST describes, which is what the oracle in `NimbleThf.Oracle` relies on.
  """

  @spellings %{
    or: "|",
    and: "&",
    app: "@",
    iff: "<=>",
    implies: "=>",
    if: "<=",
    xor: "<~>",
    nor: "~|",
    nand: "~&",
    eq: "=",
    neq: "!=",
    map: ">",
    xprod: "*",
    union: "+",
    identical: "==",
    assign: ":=",
    not: "~",
    forall: "!",
    exists: "?",
    lambda: "^",
    choice: "@+",
    description: "@-",
    pi: "!>",
    sigma: "?*",
    hash: "#",
    all: "!!",
    ex: "??",
    choose: "@@+",
    describe: "@@-",
    typed_eq: "@="
  }
  @th1_defined [:all, :ex, :choose, :describe, :typed_eq]

  @spec to_string(tuple()) :: String.t()
  def to_string(statement), do: statement |> statement() |> IO.iodata_to_binary()

  defp statement({:thf, name, role, formula, annotations}) do
    ["thf(", name, ", ", general(role), ", ", formula(formula), annotations(annotations), ")."]
  end

  defp statement({:include, file, nil}), do: ["include(", file, ")."]
  defp statement({:include, file, "*"}), do: ["include(", file, ", *)."]

  defp statement({:include, file, names}),
    do: ["include(", file, ", [", Enum.intersperse(names, ", "), "])."]

  defp annotations(nil), do: []
  defp annotations(terms), do: Enum.map(terms, &[", ", general(&1)])

  defp formula({:typing, atom, type}), do: [term(atom), ": ", term(type)]
  # `:=` only occurs in `$let` definitions, where the grammar forbids parentheses.
  defp formula({:binary, :assign, l, r}), do: [term(l), " := ", term(r)]
  defp formula(term), do: term(term)

  defp term({:quant, q, vars, body}) do
    vars = Enum.map_intersperse(vars, ", ", fn {name, type} -> [name, ": ", term(type)] end)
    ["(", @spellings[q], " [", vars, "]: ", term(body), ")"]
  end

  defp term({:binary, op, l, r}), do: ["(", term(l), " ", @spellings[op], " ", term(r), ")"]
  defp term({:not, f}), do: ["(~ ", term(f), ")"]
  defp term({:fun, head, args}), do: [term(head), "(", list(args), ")"]
  defp term({:tuple, items}), do: ["[", list(items), "]"]
  defp term({:conn, op}) when op in @th1_defined, do: @spellings[op]
  defp term({:conn, op}), do: ["(", @spellings[op], ")"]
  defp term({_atom, text}), do: text

  defp list(items), do: Enum.map_intersperse(items, ", ", &formula/1)

  defp general({:list, items}), do: ["[", Enum.map_intersperse(items, ", ", &general/1), "]"]
  defp general({:colon, data, term}), do: [general(data), ":", general(term)]
  defp general({:word, word}), do: word

  defp general({:general_function, word, args}),
    do: [word, "(", Enum.map_intersperse(args, ", ", &general/1), ")"]

  defp general({:formula_data, f}), do: ["$thf(", formula(f), ")"]
  defp general({role, subrole}) when is_binary(role), do: [role, "-", general(subrole)]
  defp general(role) when is_binary(role), do: role
  defp general(other), do: term(other)
end
