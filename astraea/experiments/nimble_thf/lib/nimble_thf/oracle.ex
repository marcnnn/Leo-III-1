defmodule NimbleThf.Oracle do
  @moduledoc """
  Checks `NimbleThf.Parser` against `Tptp` statement by statement.

  For each statement the NimbleParsec AST is printed fully parenthesised and
  reparsed with `Tptp`. Both `Tptp` trees, of the original and of the reprint, are
  compared after removing the nodes that only record parentheses. Any disagreement
  in precedence, associativity, binder scope or token classification shows up as a
  difference.
  """

  alias Tptp.Node
  alias Tptp.Statement.Annotated
  alias Tptp.Statement.Include

  @spec check(binary()) :: :ok | {:error, term()}
  def check(source) do
    {:ok, reference, []} = Tptp.from_string(source)

    with {:ok, ours} <- NimbleThf.Parser.parse(source),
         :ok <- same_length(reference.statements, ours) do
      reference.statements
      |> Enum.zip(ours)
      |> Enum.find_value(:ok, fn {expected, statement} ->
        printed = NimbleThf.Printer.to_string(statement)

        case Tptp.Parser.statement_from_string(printed) do
          {:ok, reprinted, []} ->
            if shape(expected) == shape(reprinted), do: nil, else: {:error, {:mismatch, printed}}

          other ->
            {:error, {:unparsable, printed, other}}
        end
      end)
    end
  end

  defp same_length(a, b) when length(a) == length(b), do: :ok
  defp same_length(a, b), do: {:error, {:count, length(a), length(b)}}

  @doc false
  def shape(%Annotated{} = s) do
    {Node.value(s.name), shape(s.role), shape(s.formula), shape(s.source), shape(s.info)}
  end

  def shape(%Include{} = s), do: {:include, shape(s.file_name), shape(s.selection)}

  def shape(%Node{kind: kind, children: [child]})
       when kind in [:thf_unitary_formula, :thf_atom_typing],
       do: shape(child)

  def shape(%Node{kind: kind, text: text, children: children}),
    do: {kind, text, Enum.map(children, &shape/1)}

  def shape(nil), do: nil
end
