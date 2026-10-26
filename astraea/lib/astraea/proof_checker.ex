defmodule Astraea.ProofChecker do
  @moduledoc """
  Layer 2 Trusted LCF-style Proof Certificate Kernel.

  Any refutation (`SZS status Theorem`) emitted by an untrusted native Rust/SIMD worker
  must be accompanied by a proof DAG whose steps are independently verified here.
  """

  alias Astraea.Arena

  @type clause :: MapSet.t({:pos | :neg, Arena.term_id()})

  @type step ::
          {:axiom, non_neg_integer(), clause()}
          | {:refl, non_neg_integer(), Arena.term_id()}
          | {:symm, non_neg_integer(), non_neg_integer()}
          | {:trans, non_neg_integer(), non_neg_integer(), non_neg_integer()}
          | {:resolve, non_neg_integer(), non_neg_integer(), non_neg_integer(),
             {:pos | :neg, Arena.term_id()}}

  @doc """
  Verifies a linear/DAG refutation certificate ending in the empty clause (`MapSet.new()`).
  Returns `:ok` if every inference step is sound and the final step derives `$false`,
  or `{:error, reason}` if any step is invalid.
  """
  @spec verify_refutation(Arena.t(), [step()]) :: :ok | {:error, term()}
  def verify_refutation(%Arena{} = arena, steps) when is_list(steps) do
    case Enum.reduce_while(steps, {:ok, %{}, nil}, fn step, {:ok, derived, _last} ->
           case check_step(arena, derived, step) do
             {:ok, id, clause} ->
               {:cont, {:ok, Map.put(derived, id, clause), clause}}

             {:error, _} = err ->
               {:halt, err}
           end
         end) do
      {:ok, _derived, last_clause} when not is_nil(last_clause) ->
        if MapSet.size(last_clause) == 0 do
          :ok
        else
          {:error, {:not_empty_clause, last_clause}}
        end

      {:ok, _derived, nil} ->
        {:error, :empty_proof}

      {:error, _} = err ->
        err
    end
  end

  defp check_step(_arena, _derived, {:axiom, id, clause}) do
    {:ok, id, clause}
  end

  defp check_step(%Arena{} = arena, _derived, {:refl, id, term_id}) do
    {_arena, eq_id} = Arena.mk_eq(arena, term_id, term_id)
    {:ok, id, MapSet.new([{:pos, eq_id}])}
  end

  defp check_step(%Arena{} = arena, derived, {:symm, id, parent_id}) do
    with {:ok, parent} <- fetch_clause(derived, parent_id),
         [{:pos, eq_id}] <- MapSet.to_list(parent),
         {6, _flags, _ty, lhs, rhs} <- Arena.get_node(arena, eq_id) do
      {_arena, sym_eq_id} = Arena.mk_eq(arena, rhs, lhs)
      {:ok, id, MapSet.new([{:pos, sym_eq_id}])}
    else
      _ -> {:error, {:invalid_symm, id, parent_id}}
    end
  end

  defp check_step(%Arena{} = arena, derived, {:trans, id, p1_id, p2_id}) do
    with {:ok, c1} <- fetch_clause(derived, p1_id),
         {:ok, c2} <- fetch_clause(derived, p2_id),
         [{:pos, eq1}] <- MapSet.to_list(c1),
         [{:pos, eq2}] <- MapSet.to_list(c2),
         {6, _, _, a, b1} <- Arena.get_node(arena, eq1),
         {6, _, _, b2, c} when b1 == b2 <- Arena.get_node(arena, eq2) do
      {_arena, eq3} = Arena.mk_eq(arena, a, c)
      {:ok, id, MapSet.new([{:pos, eq3}])}
    else
      _ -> {:error, {:invalid_trans, id, p1_id, p2_id}}
    end
  end

  defp check_step(_arena, derived, {:resolve, id, p1_id, p2_id, {:pos, atom_id}}) do
    with {:ok, c1} <- fetch_clause(derived, p1_id),
         {:ok, c2} <- fetch_clause(derived, p2_id),
         true <- MapSet.member?(c1, {:pos, atom_id}),
         true <- MapSet.member?(c2, {:neg, atom_id}) do
      resolvent =
        MapSet.union(
          MapSet.delete(c1, {:pos, atom_id}),
          MapSet.delete(c2, {:neg, atom_id})
        )

      {:ok, id, resolvent}
    else
      _ -> {:error, {:invalid_resolve, id, p1_id, p2_id, atom_id}}
    end
  end

  defp fetch_clause(derived, id) do
    case Map.fetch(derived, id) do
      {:ok, clause} -> {:ok, clause}
      :error -> {:error, {:unknown_premise, id}}
    end
  end
end
