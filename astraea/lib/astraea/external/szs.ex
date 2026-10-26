defmodule Astraea.External.SZS do
  @moduledoc """
  Parses SZS ontology answers (`SZS status ...` lines and `SZS output start/end`
  blocks) from the stdout of external TPTP provers.

  Mirrors `leo.modules.external.TPTPProver.readSZSResults` from Leo-III. Status
  strings are mapped through a fixed whitelist so arbitrary prover output never
  creates atoms. Only TPTP comment lines (`%`, or `#` for E) count, so echoed input
  or error messages that merely mention an SZS status are ignored.
  """

  @statuses %{
    "Theorem" => :theorem,
    "Unsatisfiable" => :unsatisfiable,
    "ContradictoryAxioms" => :contradictory_axioms,
    "CounterSatisfiable" => :counter_satisfiable,
    "Satisfiable" => :satisfiable,
    "GaveUp" => :gave_up,
    "Timeout" => :timeout,
    "ResourceOut" => :resource_out,
    "MemoryOut" => :memory_out,
    "Inappropriate" => :inappropriate,
    "Unknown" => :unknown,
    "Error" => :error,
    "InputError" => :input_error,
    "SyntaxError" => :syntax_error,
    "TypeError" => :type_error,
    "Forced" => :forced,
    "User" => :user
  }

  @unsat_statuses [:theorem, :unsatisfiable, :contradictory_axioms]
  @sat_statuses [:counter_satisfiable, :satisfiable]

  @type status :: atom()

  @type parsed :: %{
          status: status(),
          status_raw: String.t() | nil,
          dataform: String.t() | nil,
          proof: [String.t()]
        }

  @status_re ~r/^\s*[%#]\s*SZS\s+status\s+([A-Za-z]+)/
  @start_re ~r/^\s*[%#]\s*SZS\s+output\s+start\s+([A-Za-z]+)/
  @end_re ~r/^\s*[%#]\s*SZS\s+output\s+end/

  @doc """
  Extracts the first SZS status and the first SZS output block from `output`.
  Returns `status: :unknown` when no status line is present.
  """
  @spec parse(String.t()) :: parsed()
  def parse(output) when is_binary(output) do
    lines = String.split(output, ~r/\r?\n/)

    status_raw =
      Enum.find_value(lines, fn line ->
        case Regex.run(@status_re, line) do
          [_, raw] -> raw
          nil -> nil
        end
      end)

    {dataform, proof} = extract_output_block(lines)

    %{
      status: Map.get(@statuses, status_raw, :unknown),
      status_raw: status_raw,
      dataform: dataform,
      proof: proof
    }
  end

  @doc """
  Classifies a status as a refutation (`:unsat`), a model (`:sat`), or `:unknown`.
  """
  @spec classify(status()) :: :unsat | :sat | :unknown
  def classify(status) when status in @unsat_statuses, do: :unsat
  def classify(status) when status in @sat_statuses, do: :sat
  def classify(_status), do: :unknown

  defp extract_output_block(lines) do
    case Enum.drop_while(lines, &(not Regex.match?(@start_re, &1))) do
      [] ->
        {nil, []}

      [start | rest] ->
        [_, dataform] = Regex.run(@start_re, start)
        {dataform, Enum.take_while(rest, &(not Regex.match?(@end_re, &1)))}
    end
  end
end
