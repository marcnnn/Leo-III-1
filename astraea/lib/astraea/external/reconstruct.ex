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

  # Matches file('...', name) or file("...", name) or file(path, name)
  @source_re ~r/file\(\s*(?:'(?:[^'\\]|\\.)*'|"(?:[^"\\]|\\.)*"|[^,]+)\s*,\s*('(?:[^'\\]|\\.)*'|"(?:[^"\\]|\\.)*"|[A-Za-z0-9_]+)\s*\)/
  # Matches fof/cnf/thf/tcf/tff(name, axiom/hypothesis, ...)
  @tptp_axiom_re ~r/^[a-z]{3}\(\s*('(?:[^'\\]|\\.)*'|"(?:[^"\\]|\\.)*"|[A-Za-z0-9_]+)\s*,\s*(?:axiom|hypothesis|negated_conjecture)\b/m
  # Plain identifiers (e.g. from an UnsatCore dataform block)
  @plain_core_re ~r/^\s*('(?:[^'\\]|\\.)*'|"(?:[^"\\]|\\.)*"|[A-Za-z0-9_]+)\s*$/
  @clause_name_re ~r/^c(\d+)$/

  @default_recon_opts [
    pick_ratio: [weight: 4, score: 2, age: 1],
    avatar: true
  ]

  @doc """
  Returns the names of the input formulas referenced by `file(_, Name)` source
  annotations or input definitions in a TSTP / UnsatCore proof (the lines of an SZS output block).
  """
  @spec core_names([String.t()]) :: MapSet.t(String.t())
  def core_names(proof_lines) do
    joined = Enum.join(proof_lines, "\n")

    file_matches =
      Regex.scan(@source_re, joined, capture: :all_but_first)
      |> MapSet.new(fn [name] -> unquote_name(name) end)

    if MapSet.size(file_matches) > 0 do
      file_matches
    else
      axiom_matches =
        Regex.scan(@tptp_axiom_re, joined, capture: :all_but_first)
        |> MapSet.new(fn [name] -> unquote_name(name) end)

      if MapSet.size(axiom_matches) > 0 do
        axiom_matches
      else
        proof_lines
        |> Enum.flat_map(fn line ->
          case Regex.run(@plain_core_re, line, capture: :all_but_first) do
            [name] when name not in ["", "%", "#"] -> [unquote_name(name)]
            _ -> []
          end
        end)
        |> MapSet.new()
      end
    end
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
      [] ->
        {:error, :empty_core}

      core_clauses ->
        merged_opts = Keyword.merge(@default_recon_opts, opts)
        Prover.prove_clauses(arena, core_clauses, merged_opts)
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

      merged_opts =
        @default_recon_opts
        |> Keyword.merge(opts)
        |> Keyword.put(:sine_limit, nil)

      Prover.prove_lowered(%{lowered | axioms: axioms}, merged_opts)
    end
  end

  defp unquote_name("'" <> rest) do
    rest
    |> String.slice(0..-2//1)
    |> String.replace(~r/\\(.)/, "\\1")
  end

  defp unquote_name("\"" <> rest) do
    rest
    |> String.slice(0..-2//1)
    |> String.replace(~r/\\(.)/, "\\1")
  end

  defp unquote_name(name), do: name
end
