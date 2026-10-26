defmodule Astraea.ProofChecker do
  @moduledoc """
  Layer 2 Trusted LCF-style Proof Certificate Kernel.

  Any refutation (`SZS status Theorem`) emitted by an untrusted native Rust/SIMD worker
  or saturation search loop must be accompanied by a proof DAG whose steps are
  independently verified here.

  Supported primitive kernel rules:
  - `{:axiom, id, clause}` — input clause from the clausified problem
  - `{:refl, id, term_id}` — reflexivity `|- t = t`
  - `{:symm, id, parent_id}` — symmetry `s = t |- t = s`
  - `{:trans, id, p1_id, p2_id}` — transitivity `a = b, b = c |- a = c`
  - `{:subst, id, parent_id, subst_map}` — capture-avoiding free-variable instantiation + beta-eta norm
  - `{:cong, id, parent_id, eq_atom_id, arg_id}` — functional congruence `f = g |- (f @ a) = (g @ a)`
  - `{:func_ext, id, parent_id, fvar_id, var_ty}` — lambda congruence / xi-rule `u = v |- (^ [X]: u) = (^ [X]: v)`
  - `{:paramod, id, eq_id, target_id, eq_atom_id, target_lit, rewritten_lit}` — Leibniz subterm replacement
  - `{:resolve, id, p1_id, p2_id, {:pos, atom_id}}` — ground resolution on matching complementary literals
  """

  alias Astraea.Arena

  @tag_app 4
  @tag_lam 5
  @tag_eq 6
  @tag_not 7
  @tag_or 8

  @type literal :: {:pos | :neg, Arena.term_id()}
  @type clause :: MapSet.t(literal())

  @type step ::
          {:axiom, non_neg_integer(), clause()}
          | {:refl, non_neg_integer(), Arena.term_id()}
          | {:symm, non_neg_integer(), non_neg_integer()}
          | {:trans, non_neg_integer(), non_neg_integer(), non_neg_integer()}
          | {:subst, non_neg_integer(), non_neg_integer(), Arena.subst()}
          | {:cong, non_neg_integer(), non_neg_integer(), Arena.term_id(), Arena.term_id()}
          | {:func_ext, non_neg_integer(), non_neg_integer(), non_neg_integer(), Arena.type_id()}
          | {:paramod, non_neg_integer(), non_neg_integer(), non_neg_integer(), Arena.term_id(),
             literal(), literal()}
          | {:resolve, non_neg_integer(), non_neg_integer(), non_neg_integer(),
             {:pos | :neg, Arena.term_id()}}

  @doc """
  Verifies a linear/DAG refutation certificate ending in the empty clause (`MapSet.new()`).
  Returns `:ok` if every inference step is sound and the final step derives `$false`,
  or `{:error, reason}` if any step is invalid.
  """
  @spec verify_refutation(Arena.t(), [step()]) :: :ok | {:error, term()}
  def verify_refutation(%Arena{} = arena, steps) when is_list(steps) do
    case Enum.reduce_while(steps, {:ok, arena, %{}, nil}, fn step, {:ok, ar, derived, _last} ->
           case check_step(ar, derived, step) do
             {:ok, ar2, id, clause} ->
               {:cont, {:ok, ar2, Map.put(derived, id, clause), clause}}

             {:error, _} = err ->
               {:halt, err}
           end
         end) do
      {:ok, _ar, _derived, last_clause} when not is_nil(last_clause) ->
        if MapSet.size(last_clause) == 0 do
          :ok
        else
          {:error, {:not_empty_clause, last_clause}}
        end

      {:ok, _ar, _derived, nil} ->
        {:error, :empty_proof}

      {:error, _} = err ->
        err
    end
  end

  defp check_step(%Arena{} = arena, _derived, {:axiom, id, clause}) do
    {:ok, arena, id, clause}
  end

  defp check_step(%Arena{} = arena, _derived, {:refl, id, term_id}) do
    {arena, norm_id} = Arena.beta_eta_norm(arena, term_id)
    {arena, eq_id} = Arena.mk_eq(arena, norm_id, norm_id)
    {:ok, arena, id, MapSet.new([{:pos, eq_id}])}
  end

  defp check_step(%Arena{} = arena, derived, {:symm, id, parent_id}) do
    with {:ok, parent} <- fetch_clause(derived, parent_id),
         [{:pos, eq_id}] <- MapSet.to_list(parent),
         {@tag_eq, _flags, _ty, lhs, rhs} <- Arena.get_node(arena, eq_id) do
      {arena, sym_eq_id} = Arena.mk_eq(arena, rhs, lhs)
      {:ok, arena, id, MapSet.new([{:pos, sym_eq_id}])}
    else
      _ -> {:error, {:invalid_symm, id, parent_id}}
    end
  end

  defp check_step(%Arena{} = arena, derived, {:trans, id, p1_id, p2_id}) do
    with {:ok, c1} <- fetch_clause(derived, p1_id),
         {:ok, c2} <- fetch_clause(derived, p2_id),
         [{:pos, eq1}] <- MapSet.to_list(c1),
         [{:pos, eq2}] <- MapSet.to_list(c2),
         {@tag_eq, _, _, a, b1} <- Arena.get_node(arena, eq1),
         {@tag_eq, _, _, b2, c} when b1 == b2 <- Arena.get_node(arena, eq2) do
      {arena, eq3} = Arena.mk_eq(arena, a, c)
      {:ok, arena, id, MapSet.new([{:pos, eq3}])}
    else
      _ -> {:error, {:invalid_trans, id, p1_id, p2_id}}
    end
  end

  defp check_step(%Arena{} = arena, derived, {:subst, id, parent_id, subst_map})
       when is_map(subst_map) do
    with {:ok, parent} <- fetch_clause(derived, parent_id),
         {:ok, arena} <- validate_subst_types(arena, subst_map) do
      {arena, new_lits} =
        Enum.reduce(parent, {arena, MapSet.new()}, fn {pol, atom_id}, {ar, acc} ->
          {ar, subbed_id} = Arena.subst_fvar(ar, atom_id, subst_map)
          {ar, MapSet.put(acc, {pol, subbed_id})}
        end)

      {:ok, arena, id, new_lits}
    else
      _ -> {:error, {:invalid_subst, id, parent_id}}
    end
  end

  defp check_step(%Arena{} = arena, derived, {:cong, id, parent_id, eq_atom_id, arg_id}) do
    with {:ok, parent} <- fetch_clause(derived, parent_id),
         true <- MapSet.member?(parent, {:pos, eq_atom_id}),
         {@tag_eq, _, _, lhs, rhs} <- Arena.get_node(arena, eq_atom_id) do
      {arena, fa} = Arena.mk_app(arena, lhs, arg_id)
      {arena, ga} = Arena.mk_app(arena, rhs, arg_id)
      {arena, fa_norm} = Arena.beta_eta_norm(arena, fa)
      {arena, ga_norm} = Arena.beta_eta_norm(arena, ga)
      {arena, new_eq} = Arena.mk_eq(arena, fa_norm, ga_norm)

      new_clause =
        parent
        |> MapSet.delete({:pos, eq_atom_id})
        |> MapSet.put({:pos, new_eq})

      {:ok, arena, id, new_clause}
    else
      _ -> {:error, {:invalid_cong, id, parent_id, eq_atom_id}}
    end
  end

  defp check_step(%Arena{} = arena, derived, {:func_ext, id, parent_id, fvar_id, var_ty}) do
    with {:ok, parent} <- fetch_clause(derived, parent_id),
         [{:pos, eq_id}] <- MapSet.to_list(parent),
         {@tag_eq, _, _, lhs, rhs} <- Arena.get_node(arena, eq_id) do
      {arena, fv_node} = Arena.mk_fvar(arena, fvar_id, var_ty)
      {arena, abs_l} = Arena.abstract_subterm(arena, lhs, fv_node, 0)
      {arena, abs_r} = Arena.abstract_subterm(arena, rhs, fv_node, 0)
      {arena, lam_l} = Arena.mk_lam(arena, var_ty, abs_l)
      {arena, lam_r} = Arena.mk_lam(arena, var_ty, abs_r)
      {arena, norm_l} = Arena.beta_eta_norm(arena, lam_l)
      {arena, norm_r} = Arena.beta_eta_norm(arena, lam_r)
      {arena, new_eq} = Arena.mk_eq(arena, norm_l, norm_r)
      {:ok, arena, id, MapSet.new([{:pos, new_eq}])}
    else
      _ -> {:error, {:invalid_func_ext, id, parent_id}}
    end
  end

  defp check_step(
         %Arena{} = arena,
         derived,
         {:paramod, id, eq_clause_id, target_clause_id, eq_atom_id,
          {pol, target_atom_id} = target_lit, {pol, expected_atom_id} = rewritten_lit}
       ) do
    with {:ok, eq_clause} <- fetch_clause(derived, eq_clause_id),
         {:ok, target_clause} <- fetch_clause(derived, target_clause_id),
         true <- MapSet.member?(eq_clause, {:pos, eq_atom_id}),
         true <- MapSet.member?(target_clause, target_lit),
         {@tag_eq, _, _, lhs, rhs} <- Arena.get_node(arena, eq_atom_id),
         {arena, true} <- valid_paramod_rewrite?(arena, target_atom_id, expected_atom_id, lhs, rhs) do
      new_clause =
        MapSet.union(
          MapSet.delete(eq_clause, {:pos, eq_atom_id}),
          MapSet.delete(target_clause, target_lit)
        )
        |> MapSet.put(rewritten_lit)

      {:ok, arena, id, new_clause}
    else
      _ -> {:error, {:invalid_paramod, id, eq_clause_id, target_clause_id}}
    end
  end

  defp check_step(%Arena{} = arena, derived, {:resolve, id, p1_id, p2_id, {:pos, atom_id}}) do
    with {:ok, c1} <- fetch_clause(derived, p1_id),
         {:ok, c2} <- fetch_clause(derived, p2_id),
         {:ok, arena, c1_lit, c2_lit} <- find_complementary_lit(arena, c1, c2, atom_id) do
      resolvent =
        MapSet.union(
          MapSet.delete(c1, c1_lit),
          MapSet.delete(c2, c2_lit)
        )

      {:ok, arena, id, resolvent}
    else
      _ -> {:error, {:invalid_resolve, id, p1_id, p2_id, atom_id}}
    end
  end

  defp validate_subst_types(%Arena{} = arena, subst_map) do
    valid? =
      Enum.all?(subst_map, fn {_fvar_id, rep_id} ->
        not Arena.has_loose_bvar?(arena, rep_id, 0)
      end)

    if valid?, do: {:ok, arena}, else: {:error, :escaping_bvar_in_subst}
  end

  defp find_complementary_lit(%Arena{} = arena, c1, c2, atom_id) do
    cond do
      MapSet.member?(c1, {:pos, atom_id}) and MapSet.member?(c2, {:neg, atom_id}) ->
        {:ok, arena, {:pos, atom_id}, {:neg, atom_id}}

      true ->
        case Arena.get_node(arena, atom_id) do
          {@tag_eq, _, _, l, r} ->
            {arena, sym_id} = Arena.mk_eq(arena, r, l)

            cond do
              MapSet.member?(c1, {:pos, atom_id}) and MapSet.member?(c2, {:neg, sym_id}) ->
                {:ok, arena, {:pos, atom_id}, {:neg, sym_id}}

              MapSet.member?(c1, {:pos, sym_id}) and MapSet.member?(c2, {:neg, atom_id}) ->
                {:ok, arena, {:pos, sym_id}, {:neg, atom_id}}

              true ->
                :error
            end

          _ ->
            :error
        end
    end
  end

  defp valid_paramod_rewrite?(%Arena{} = arena, target_id, expected_id, lhs, rhs) do
    {arena, rep1} = replace_subterm(arena, target_id, lhs, rhs)
    {arena, norm1} = Arena.beta_eta_norm(arena, rep1)

    if norm1 == expected_id or eq_modulo_sym?(arena, norm1, expected_id) do
      {arena, true}
    else
      {arena, rep2} = replace_subterm(arena, target_id, rhs, lhs)
      {arena, norm2} = Arena.beta_eta_norm(arena, rep2)
      {arena, norm2 == expected_id or eq_modulo_sym?(arena, norm2, expected_id)}
    end
  end

  defp eq_modulo_sym?(%Arena{} = arena, id1, id2) do
    case {Arena.get_node(arena, id1), Arena.get_node(arena, id2)} do
      {{@tag_eq, _, _, l1, r1}, {@tag_eq, _, _, l2, r2}} ->
        (l1 == l2 and r1 == r2) or (l1 == r2 and r1 == l2)

      _ ->
        false
    end
  end

  @doc """
  Replaces all occurrences of `from_id` inside `term_id` with `to_id`.
  """
  @spec replace_subterm(Arena.t(), Arena.term_id(), Arena.term_id(), Arena.term_id()) ::
          {Arena.t(), Arena.term_id()}
  def replace_subterm(%Arena{} = arena, term_id, from_id, to_id) do
    if term_id == from_id do
      {arena, to_id}
    else
      {tag, _flags, _ty_id, left, right} = Arena.get_node(arena, term_id)

      case tag do
        @tag_app ->
          {arena, l2} = replace_subterm(arena, left, from_id, to_id)
          {arena, r2} = replace_subterm(arena, right, from_id, to_id)
          Arena.mk_app(arena, l2, r2)

        @tag_eq ->
          {arena, l2} = replace_subterm(arena, left, from_id, to_id)
          {arena, r2} = replace_subterm(arena, right, from_id, to_id)
          Arena.mk_eq(arena, l2, r2)

        @tag_or ->
          {arena, l2} = replace_subterm(arena, left, from_id, to_id)
          {arena, r2} = replace_subterm(arena, right, from_id, to_id)
          Arena.mk_or(arena, l2, r2)

        @tag_not ->
          {arena, l2} = replace_subterm(arena, left, from_id, to_id)
          Arena.mk_not(arena, l2)

        @tag_lam ->
          {arena, from_s} = Arena.shift(arena, from_id, 1, 0)
          {arena, to_s} = Arena.shift(arena, to_id, 1, 0)
          {arena, b2} = replace_subterm(arena, right, from_s, to_s)
          Arena.mk_lam(arena, left, b2)

        _ ->
          {arena, term_id}
      end
    end
  end

  defp fetch_clause(derived, id) do
    case Map.fetch(derived, id) do
      {:ok, clause} -> {:ok, clause}
      :error -> {:error, {:unknown_premise, id}}
    end
  end
end
