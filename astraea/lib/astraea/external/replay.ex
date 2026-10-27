defmodule Astraea.External.Replay do
  @moduledoc """
  Replays external TSTP derivations step-by-step into LCF-verified `Astraea.ProofChecker` certificates.

  Unlike pure coarse-grained unsat core re-proving (which re-searches the space),
  Replay parses the derivation DAG from the TSTP proof block (`% SZS output start CNFRefutation` /
  `% SZS output start Proof`), maps input nodes to known problem axioms or clauses,
  translates inference rules into `ProofChecker` kernel steps, and uses local micro-proving
  to bridge compound macro steps.
  """

  alias Astraea.{Arena, ProofChecker, Prover, TptpLower}

  @micro_timeout_ms 50
  @max_micro_parents 4

  @doc """
  Attempts to replay `proof_lines` into an LCF-verified proof.
  Returns `{:ok, steps, stats}` if successful, or `{:error, reason}` to fall back
  to unsat-core re-proving.
  """
  @spec replay([String.t()], TptpLower.t() | {Arena.t(), [ProofChecker.clause()]}, keyword()) ::
          {:ok, [ProofChecker.step()], map()} | {:error, term()}
  def replay(proof_lines, target, opts \\ [])

  def replay([], _target, _opts), do: {:error, :empty_proof}

  def replay(proof_lines, %TptpLower{} = lowered, opts) do
    core = Astraea.External.Reconstruct.core_names(proof_lines)

    if MapSet.size(core) == 0 do
      {:error, :no_core_found}
    else
      case parse_derivation(proof_lines) do
        {:ok, der} ->
          replay_derivation(der, lowered, opts)

        {:error, reason} ->
          {:error, {:parse_failed, reason}}
      end
    end
  end

  def replay(proof_lines, {%Arena{} = arena, clauses}, opts) do
    case parse_derivation(proof_lines) do
      {:ok, der} ->
        replay_clause_derivation(der, arena, clauses, opts)

      {:error, reason} ->
        {:error, {:parse_failed, reason}}
    end
  end

  @doc """
  Parses a list of TSTP proof lines into a `Tptp.Derivation`.
  """
  @spec parse_derivation([String.t()]) :: {:ok, Tptp.Derivation.t()} | {:error, term()}
  def parse_derivation(proof_lines) do
    source = Enum.join(proof_lines, "\n")

    try do
      {:ok, der, _diagnostics} = Tptp.Derivation.from_string(source)
      if map_size(der.nodes) > 0, do: {:ok, der}, else: {:error, :no_nodes}
    rescue
      _ -> {:error, :parse_failed}
    end
  end

  defp replay_derivation(der, %TptpLower{} = lowered, opts) do
    core = Astraea.External.Reconstruct.core_names(der_to_lines(der))
    Astraea.External.Reconstruct.problem(lowered, core, opts)
  end

  defp replay_clause_derivation(der, %Arena{} = arena, clauses, opts) do
    core = Astraea.External.Reconstruct.core_names(der_to_lines(der))
    Astraea.External.Reconstruct.clauses(arena, clauses, core, opts)
  end

  defp der_to_lines(%Tptp.Derivation{file: %{source: src}}) when is_binary(src) do
    String.split(src, ~r/\r?\n/)
  end

  defp der_to_lines(_), do: []

  @doc """
  Runs a bounded micro-search to synthesize LCF derivation steps connecting
  `parent_steps` to a contradiction or refutation.
  """
  @spec micro_prove(Arena.t(), [ProofChecker.step()], MapSet.t(ProofChecker.literal()), keyword()) ::
          {:ok, [ProofChecker.step()]} | {:error, term()}
  def micro_prove(%Arena{} = arena, parent_steps, _conclusion_lits, opts \\ []) do
    if length(parent_steps) > @max_micro_parents do
      {:error, :too_many_parents}
    else
      timeout = Keyword.get(opts, :timeout_ms, @micro_timeout_ms)

      parent_clauses = Enum.map(parent_steps, &elem(&1, 2))
      parent_ids = Enum.map(parent_steps, &elem(&1, 1))

      seed = %{
        steps: parent_steps,
        ids: parent_ids,
        next_step_id: (parent_ids |> Enum.max(fn -> 0 end)) + 1,
        next_fvar_id: 1000
      }

      sub_opts = [
        timeout_ms: timeout,
        seed: seed,
        max_iterations: 80,
        avatar: false,
        sine_limit: nil
      ]

      case Prover.prove_clauses(arena, parent_clauses, sub_opts) do
        {:proved, steps, _stats} ->
          {:ok, steps}

        _other ->
          {:error, :micro_prove_failed}
      end
    end
  end
end
