defmodule Astraea.External.Reconstruct do
  @moduledoc """
  Turns external refutations into LCF-verified Astraea proofs (Sledgehammer-style).

  External TSTP proofs are not replayed inference by inference. Instead, the input
  formulas a proof uses (its unsat core, read from `file(_, Name)` source
  annotations) are handed back to `Astraea.Prover`, which usually refutes the much
  smaller core quickly. Every resulting proof passes `Astraea.ProofChecker`, so
  the external prover only acts as a relevance filter and never has to be trusted.
  """

  alias Astraea.{Arena, ProofChecker, Prover, TptpLower}

  @source_re ~r/file\(\s*'(?:[^'\\]|\\.)*'\s*,\s*('(?:[^'\\]|\\.)*'|[A-Za-z0-9_]+)\s*\)/
  @clause_name_re ~r/^c(\d+)$/

  @doc """
  Returns the names of the input formulas referenced by `file(_, Name)` source
  annotations in a TSTP proof (the lines of an SZS output block).
  """
  @spec core_names([String.t()]) :: MapSet.t(String.t())
  def core_names(proof_lines) do
    proof_lines
    |> Enum.join("\n")
    |> then(&Regex.scan(@source_re, &1, capture: :all_but_first))
    |> MapSet.new(fn [name] -> unquote_name(name) end)
  end

  @doc """
  Maps core names of a clause-set problem (`c<i>`, see
  `Astraea.External.prove_clauses/4`) to clause indices. Other names, such as the
  definitions `d<k>` of the TFF encoding, are dropped.
  """
  @spec clause_indices(MapSet.t(String.t())) :: [non_neg_integer()]
  def clause_indices(names) do
    names
    |> Enum.flat_map(fn name ->
      case Regex.run(@clause_name_re, name) do
        [_, idx] -> [String.to_integer(idx)]
        nil -> []
      end
    end)
    |> Enum.sort()
  end

  @doc """
  Re-proves the clauses of `clauses` named in `core` with `Astraea.Prover`.
  Returns `{:error, :empty_core}` when no clause of the core is known.
  """
  @spec clauses(Arena.t(), [ProofChecker.clause()], MapSet.t(String.t()), keyword()) ::
          Prover.result()
  def clauses(%Arena{} = arena, clauses, core, opts \\ []) do
    by_index = clauses |> Enum.with_index() |> Map.new(fn {c, i} -> {i, c} end)

    case core |> clause_indices() |> Enum.flat_map(&List.wrap(by_index[&1])) do
      [] -> {:error, :empty_core}
      core_clauses -> Prover.prove_clauses(arena, core_clauses, opts)
    end
  end

  @doc """
  Re-proves a lowered TPTP problem restricted to the axioms named in `core`.
  Conjectures and definitions are always kept, and SInE is disabled since the core
  already is the relevant premise set.
  """
  @spec problem(TptpLower.t(), MapSet.t(String.t()), keyword()) :: Prover.result()
  def problem(%TptpLower{} = lowered, core, opts \\ []) do
    if MapSet.size(core) == 0 do
      {:error, :empty_core}
    else
      axioms =
        Enum.filter(lowered.axioms, fn {name, role, _id} ->
          role == "definition" or MapSet.member?(core, name)
        end)

      Prover.prove_lowered(%{lowered | axioms: axioms}, Keyword.put(opts, :sine_limit, nil))
    end
  end

  defp unquote_name("'" <> rest) do
    rest
    |> String.slice(0..-2//1)
    |> String.replace(~r/\\(.)/, "\\1")
  end

  defp unquote_name(name), do: name
end
