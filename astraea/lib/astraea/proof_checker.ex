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
  - `{:subst, id, parent_id, subst_map}` — capture-avoiding, type-preserving free-variable instantiation + beta-eta norm
  - `{:cong, id, parent_id, eq_atom_id, arg_id}` — functional congruence `f = g |- (f @ a) = (g @ a)`
  - `{:func_ext, id, parent_id, fvar_id, var_ty}` — lambda congruence / xi-rule `u = v |- (^ [X]: u) = (^ [X]: v)`
  - `{:paramod, id, eq_id, target_id, eq_atom_id, target_lit, rewritten_lit}` — Leibniz subterm replacement
  - `{:resolve, id, p1_id, p2_id, {:pos, atom_id}}` — ground resolution on matching complementary literals

  Higher-order calculus rules (search-time clausification, extensionality, choice):
  - `{:cnf, id, parent_id, literal, rule}` — replaces `literal` of the parent by its
    one-step expansion `expand_literal/3` (see below)
  - `{:choice, id, pred_id, fvar_id}` — Hilbert choice instance
    `~(P @ X) | P @ ($choice @ P)` for a closed `P: T > $o`
  - `{:arith_eval, id, parent_id, clause}` — ground arithmetic evaluation; `clause` must
    equal `Astraea.Input.Arith.eval_clause/2` of the parent, which the kernel recomputes
    (soundness argument in `Astraea.Input.Arith`)
  - `{:eval, id, parent_id, clause}` — ground lambda/combinator/boolean evaluation; `clause` must
    equal `Astraea.Evaluator.eval_clause/2` of the parent, which the kernel recomputes

  Soundness of the `:cnf` rules (each conclusion is entailed by its premise in
  extensional Henkin semantics, or, for `:skolem`, in every expansion of a model that
  interprets Skolem symbols by choice):
  - `:not`, `:or`, `{:or, side}`, `{:bool_eq, side}`: propositional consequences of
    `C | L` (`{:or, side}` and `{:bool_eq, side}` select one clause of the CNF of `L`).
  - `{:forall, fvar_id}`: `C | ! [x]: A |- C | A[X]` is universal instantiation; it is
    sound for any variable `X` (fresh or not) of the binder type, which the kernel
    builds itself.
  - `:skolem`: `C | ~(! [x]: A) |- C | ~A[sk @ Y1 ... @ Yn]` where the kernel builds
    `sk = Arena.mk_skolem(phi, ty)` for `phi = ! [x]: A` and applies it to the free
    variables `Y1 < ... < Yn` of `phi` (by id). The Skolem node stores `phi` itself,
    so it is interpreted as `sk Y1 ... Yn := eps x. ~A` (any witness if one exists).
    That interpretation is the same for every occurrence of the node (also those made
    by `Astraea.Clausifier`, which applies the same Skolem to the same variables in
    the same order), so the conclusion holds in the expanded model. Substitutions
    never enter a Skolem node (it carries no free-variable flag).
  - `:truth`: `C | ~$true` and `C | $false` both entail `C`.
  - `:ext`: `C | [~](f = g) |- C | [~](! [x]: f @ x = g @ x)` for `f, g` of arrow type
    is the functional extensionality equivalence (Leo-III `FuncExt`; a negative
    literal then becomes a Skolem witness via `:skolem`).
  The Hilbert choice instance is an axiom of the TPTP choice operator `$choice`
  (one constant per type `(T > $o) > T`, shared with the input agent).
  """

  alias Astraea.Arena

  @tag_const 1
  @tag_app 4
  @tag_lam 5
  @tag_eq 6
  @tag_not 7
  @tag_or 8
  @tag_forall 9

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
          | {:cnf, non_neg_integer(), non_neg_integer(), literal(), cnf_rule()}
          | {:choice, non_neg_integer(), Arena.term_id(), non_neg_integer()}
          | {:arith_eval, non_neg_integer(), non_neg_integer(), clause()}
          | {:eval, non_neg_integer(), non_neg_integer(), clause()}
          | {:eq_fact, non_neg_integer(), non_neg_integer(), Arena.term_id(), Arena.term_id()}
          | {:avatar_split, non_neg_integer(), non_neg_integer(), [Arena.term_id()]}
          | {:avatar_comp, non_neg_integer(), non_neg_integer(), Arena.term_id(), clause()}

  @type cnf_rule ::
          :not
          | :or
          | {:or, :left | :right}
          | {:forall, non_neg_integer()}
          | :skolem
          | {:bool_eq, :left | :right}
          | :truth
          | :ext
          | :lift_bool

  @doc """
  Replays all `steps` through the kernel and returns `{:ok, arena, derived_map}`
  where `derived_map` maps each step ID to its verified clause, or `{:error, reason}`.
  """
  @spec derive_steps(Arena.t(), [step()]) ::
          {:ok, Arena.t(), %{non_neg_integer() => clause()}} | {:error, term()}
  def derive_steps(%Arena{} = arena, steps) when is_list(steps) do
    Enum.reduce_while(steps, {:ok, arena, %{}}, fn step, {:ok, ar, derived} ->
      case check_step(ar, derived, step) do
        {:ok, ar2, id, clause} ->
          {:cont, {:ok, ar2, Map.put(derived, id, clause)}}

        {:error, _} = err ->
          {:halt, err}
      end
    end)
  end

  @doc """
  Verifies a linear/DAG refutation certificate ending in the empty clause (`MapSet.new()`).
  Returns `:ok` if every inference step is sound and the final step derives `$false`,
  or `{:error, reason}` if any step is invalid.
  """
  @spec verify_refutation(Arena.t(), [step()]) :: :ok | {:error, term()}
  def verify_refutation(%Arena{} = arena, steps) when is_list(steps) do
    case derive_steps(arena, steps) do
      {:ok, _ar, derived} when map_size(derived) > 0 ->
        last_step = List.last(steps)
        last_id = elem(last_step, 1)
        last_clause = Map.get(derived, last_id)

        if last_clause && MapSet.size(last_clause) == 0 do
          :ok
        else
          {:error, {:not_empty_clause, last_clause}}
        end

      {:ok, _ar, _empty_derived} ->
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
         {:ok, arena} <- validate_subst_types(arena, subst_map, parent) do
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
         {arena, true} <-
           valid_paramod_rewrite?(arena, target_atom_id, expected_atom_id, lhs, rhs) do
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

  # ---------------------------------------------------------------------------
  # Higher-order calculus rules (`:cnf`, `:choice`, `:eval`), see the moduledoc
  # ---------------------------------------------------------------------------

  defp check_step(%Arena{} = arena, derived, {:cnf, id, parent_id, lit, rule}) do
    with {:ok, parent} <- fetch_clause(derived, parent_id),
         true <- MapSet.member?(parent, lit),
         {:ok, arena, lits} <- expand_literal(arena, lit, rule) do
      {:ok, arena, id, parent |> MapSet.delete(lit) |> MapSet.union(MapSet.new(lits))}
    else
      _ -> {:error, {:invalid_cnf, id, parent_id, rule}}
    end
  end

  defp check_step(%Arena{} = arena, _derived, {:choice, id, pred_id, fvar_id}) do
    case choice_instance(arena, pred_id, fvar_id) do
      {:ok, arena, clause} -> {:ok, arena, id, clause}
      :error -> {:error, {:invalid_choice, id, pred_id}}
    end
  end

  defp check_step(%Arena{} = arena, derived, {:arith_eval, id, parent_id, claimed}) do
    with {:ok, parent} <- fetch_clause(derived, parent_id),
         {arena, ^claimed} <- Astraea.Input.Arith.eval_clause(arena, parent) do
      {:ok, arena, id, claimed}
    else
      _ -> {:error, {:invalid_arith_eval, id, parent_id}}
    end
  end

  defp check_step(%Arena{} = arena, derived, {:eval, id, parent_id, claimed}) do
    with {:ok, parent} <- fetch_clause(derived, parent_id),
         {arena, ^claimed} <- Astraea.Evaluator.eval_clause(arena, parent) do
      {:ok, arena, id, claimed}
    else
      _ -> {:error, {:invalid_eval, id, parent_id}}
    end
  end

  defp check_step(%Arena{} = arena, derived, {:eq_fact, id, parent_id, eq1_id, eq2_id}) do
    with {:ok, parent} <- fetch_clause(derived, parent_id),
         true <- MapSet.member?(parent, {:pos, eq1_id}),
         true <- MapSet.member?(parent, {:pos, eq2_id}),
         true <- eq1_id != eq2_id,
         {@tag_eq, _, _, lhs1, rhs1} <- Arena.get_node(arena, eq1_id),
         {@tag_eq, _, _, lhs2, rhs2} <- Arena.get_node(arena, eq2_id),
         {_common, rem1, rem2} <- match_eq_sides(lhs1, rhs1, lhs2, rhs2) do
      {arena, neg_eq} = Arena.mk_eq(arena, rem1, rem2)

      new_clause =
        parent
        |> MapSet.delete({:pos, eq1_id})
        |> MapSet.put({:neg, neg_eq})

      {:ok, arena, id, new_clause}
    else
      _ -> {:error, {:invalid_eq_fact, id, parent_id}}
    end
  end

  defp check_step(%Arena{} = arena, derived, {:avatar_split, id, parent_id, guard_atoms})
       when is_list(guard_atoms) do
    with {:ok, _parent} <- fetch_clause(derived, parent_id),
         true <- length(guard_atoms) >= 2,
         true <- Enum.all?(guard_atoms, &valid_guard_atom?(arena, &1)) do
      split_clause = MapSet.new(guard_atoms, &{:pos, &1})
      {:ok, arena, id, split_clause}
    else
      _ -> {:error, {:invalid_avatar_split, id, parent_id}}
    end
  end

  defp check_step(%Arena{} = arena, derived, {:avatar_comp, id, parent_id, guard_atom, comp_lits}) do
    with {:ok, parent} <- fetch_clause(derived, parent_id),
         true <- MapSet.subset?(comp_lits, parent),
         true <- MapSet.size(comp_lits) > 0,
         true <- valid_guard_atom?(arena, guard_atom),
         remainder = MapSet.difference(parent, comp_lits),
         true <- disjoint_free_vars?(arena, comp_lits, remainder) do
      comp_clause = MapSet.put(comp_lits, {:neg, guard_atom})
      {:ok, arena, id, comp_clause}
    else
      _ -> {:error, {:invalid_avatar_comp, id, parent_id}}
    end
  end

  defp valid_guard_atom?(%Arena{} = arena, atom_id) do
    Arena.type_of(arena, atom_id) == Arena.ty_o() and
      MapSet.size(Arena.free_vars(arena, atom_id)) == 0
  end

  defp disjoint_free_vars?(%Arena{} = arena, comp_lits, remainder) do
    comp_fvs =
      Enum.reduce(comp_lits, MapSet.new(), fn {_pol, atom_id}, acc ->
        MapSet.union(acc, Arena.free_vars(arena, atom_id))
      end)

    rem_fvs =
      Enum.reduce(remainder, MapSet.new(), fn {_pol, atom_id}, acc ->
        MapSet.union(acc, Arena.free_vars(arena, atom_id))
      end)

    MapSet.disjoint?(comp_fvs, rem_fvs)
  end

  @doc """
  Checks if any side of equation 1 matches any side of equation 2 modulo symmetry.
  Returns `{common, remainder1, remainder2}` or `nil`.
  """
  @spec match_eq_sides(Arena.term_id(), Arena.term_id(), Arena.term_id(), Arena.term_id()) ::
          {Arena.term_id(), Arena.term_id(), Arena.term_id()} | nil
  def match_eq_sides(l1, r1, l2, r2) do
    cond do
      l1 == l2 -> {l1, r1, r2}
      l1 == r2 -> {l1, r1, l2}
      r1 == l2 -> {r1, l1, r2}
      r1 == r2 -> {r1, l1, l2}
      true -> nil
    end
  end

  @doc """
  Premise step ids of `step` (for proof extraction and compression).
  """
  @spec step_parents(step()) :: [non_neg_integer()]
  def step_parents({:cnf, _id, p, _lit, _rule}), do: [p]
  def step_parents({:choice, _id, _pred, _fv}), do: []
  def step_parents({:arith_eval, _id, p, _clause}), do: [p]
  def step_parents({:eval, _id, p, _clause}), do: [p]
  def step_parents({:eq_fact, _id, p, _eq1, _eq2}), do: [p]
  def step_parents({:axiom, _id, _c}), do: []
  def step_parents({:refl, _id, _t}), do: []
  def step_parents({:symm, _id, p}), do: [p]
  def step_parents({:trans, _id, p1, p2}), do: [p1, p2]
  def step_parents({:subst, _id, p, _s}), do: [p]
  def step_parents({:cong, _id, p, _eq, _arg}), do: [p]
  def step_parents({:func_ext, _id, p, _fv, _ty}), do: [p]
  def step_parents({:paramod, _id, p1, p2, _eq, _tl, _rl}), do: [p1, p2]
  def step_parents({:resolve, _id, p1, p2, _lit}), do: [p1, p2]
  def step_parents({:avatar_split, _id, p, _guards}), do: [p]
  def step_parents({:avatar_comp, _id, p, _guard, _comp_lits}), do: [p]

  @doc """
  Renames the premise ids of a calculus step (`:cnf`, `:choice`, `:arith_eval`, `:eval`) through `remap`.
  """
  @spec rewire_parents(step(), %{non_neg_integer() => non_neg_integer()}) :: step()
  def rewire_parents({:cnf, id, p, lit, rule}, remap),
    do: {:cnf, id, Map.get(remap, p, p), lit, rule}

  def rewire_parents({:choice, _id, _pred, _fv} = step, _remap), do: step

  def rewire_parents({:arith_eval, id, p, clause}, remap),
    do: {:arith_eval, id, Map.get(remap, p, p), clause}

  def rewire_parents({:eval, id, p, clause}, remap),
    do: {:eval, id, Map.get(remap, p, p), clause}

  def rewire_parents({:eq_fact, id, p, eq1, eq2}, remap),
    do: {:eq_fact, id, Map.get(remap, p, p), eq1, eq2}

  def rewire_parents({:avatar_split, id, p, guards}, remap),
    do: {:avatar_split, id, Map.get(remap, p, p), guards}

  def rewire_parents({:avatar_comp, id, p, guard, comp_lits}, remap),
    do: {:avatar_comp, id, Map.get(remap, p, p), guard, comp_lits}

  @doc """
  One-step clausal expansion of a non-atomic literal under `rule` (the `:cnf` kernel
  rule). Returns the literals replacing `lit`, or `:error` if `rule` does not apply.
  """
  @spec expand_literal(Arena.t(), literal(), cnf_rule()) ::
          {:ok, Arena.t(), [literal()]} | :error
  def expand_literal(%Arena{} = arena, {pol, atom}, rule) do
    expand(arena, pol, Arena.get_node(arena, atom), atom, rule)
  end

  defp expand(arena, pol, {@tag_not, _, _, a, _}, _atom, :not),
    do: {:ok, arena, [{flip(pol), a}]}

  defp expand(arena, :pos, {@tag_or, _, _, l, r}, _atom, :or),
    do: {:ok, arena, [{:pos, l}, {:pos, r}]}

  defp expand(arena, :neg, {@tag_or, _, _, l, _r}, _atom, {:or, :left}),
    do: {:ok, arena, [{:neg, l}]}

  defp expand(arena, :neg, {@tag_or, _, _, _l, r}, _atom, {:or, :right}),
    do: {:ok, arena, [{:neg, r}]}

  defp expand(arena, :pos, {@tag_forall, _, _, dom, body}, _atom, {:forall, fvar_id})
       when is_integer(fvar_id) and fvar_id >= 0 do
    {arena, x} = Arena.mk_fvar(arena, fvar_id, dom)
    {arena, inst} = instantiate_binder(arena, body, x)
    {:ok, arena, [{:pos, inst}]}
  end

  defp expand(arena, :neg, {@tag_forall, _, _, dom, body}, atom, :skolem) do
    params = arena |> Arena.free_vars(atom) |> Enum.sort()

    {arena, sk_ty} =
      params
      |> Enum.reverse()
      |> Enum.reduce({arena, dom}, fn {_id, ty}, {ar, acc} ->
        Arena.intern_type(ar, {:arrow, ty, acc})
      end)

    {arena, sk} = Arena.mk_skolem(arena, atom, sk_ty)

    {arena, witness} =
      Enum.reduce(params, {arena, sk}, fn {id, ty}, {ar, acc} ->
        {ar, y} = Arena.mk_fvar(ar, id, ty)
        Arena.mk_app(ar, acc, y)
      end)

    {arena, inst} = instantiate_binder(arena, body, witness)
    {:ok, arena, [{:neg, inst}]}
  end

  defp expand(arena, pol, {@tag_eq, _, _, l, r}, _atom, {:bool_eq, side})
       when side in [:left, :right] do
    if Arena.type_of(arena, l) == Arena.ty_o() do
      lits =
        case {pol, side} do
          {:pos, :left} -> [{:neg, l}, {:pos, r}]
          {:pos, :right} -> [{:pos, l}, {:neg, r}]
          {:neg, :left} -> [{:pos, l}, {:pos, r}]
          {:neg, :right} -> [{:neg, l}, {:neg, r}]
        end

      {:ok, arena, lits}
    else
      :error
    end
  end

  defp expand(arena, pol, {@tag_eq, _, _, l, r}, _atom, :ext) do
    case Map.fetch!(arena.type_table, Arena.type_of(arena, l)) do
      {:arrow, dom, _cod} ->
        {arena, x} = Arena.mk_bvar(arena, 0, dom)
        {arena, l1} = Arena.shift(arena, l, 1, 0)
        {arena, r1} = Arena.shift(arena, r, 1, 0)
        {arena, lx} = Arena.mk_app(arena, l1, x)
        {arena, rx} = Arena.mk_app(arena, r1, x)
        {arena, eq} = Arena.mk_eq(arena, lx, rx)
        {arena, all} = Arena.mk_forall(arena, dom, eq)
        {arena, norm} = Arena.beta_eta_norm(arena, all)
        {:ok, arena, [{pol, norm}]}

      _ ->
        :error
    end
  end

  defp expand(arena, pol, {_tag, _, _, _, _}, atom, :truth) do
    falsum = if pol == :pos, do: "$false", else: "$true"

    if truth_const?(arena, atom, falsum), do: {:ok, arena, []}, else: :error
  end

  defp expand(arena, :pos, node, atom, :lift_bool) do
    if Arena.type_of(arena, atom) == Arena.ty_o() and elem(node, 0) != @tag_eq do
      {arena, true_const} = Arena.mk_const(arena, "$true", :o)
      {arena, eq} = Arena.mk_eq(arena, atom, true_const)
      {:ok, arena, [{:pos, eq}]}
    else
      :error
    end
  end

  defp expand(arena, :neg, node, atom, :lift_bool) do
    if Arena.type_of(arena, atom) == Arena.ty_o() and elem(node, 0) != @tag_eq do
      {arena, false_const} = Arena.mk_const(arena, "$false", :o)
      {arena, eq} = Arena.mk_eq(arena, atom, false_const)
      {:ok, arena, [{:pos, eq}]}
    else
      :error
    end
  end

  defp expand(_arena, _pol, _node, _atom, _rule), do: :error

  defp instantiate_binder(arena, body, replacement) do
    {arena, inst} = Arena.subst_bvar(arena, body, 0, replacement)
    Arena.beta_eta_norm(arena, inst)
  end

  defp truth_const?(arena, atom, name) do
    case Arena.get_node(arena, atom) do
      {@tag_const, _, _, sym, _} -> Map.get(arena.symbol_names, sym) == name
      _ -> false
    end
  end

  defp flip(:pos), do: :neg
  defp flip(:neg), do: :pos

  @doc """
  The Hilbert choice instance `~(P @ X) | P @ ($choice @ P)` for a closed predicate
  `P: T > $o` and the variable `X: T` with id `fvar_id`.
  """
  @spec choice_instance(Arena.t(), Arena.term_id(), non_neg_integer()) ::
          {:ok, Arena.t(), clause()} | :error
  def choice_instance(%Arena{} = arena, pred_id, fvar_id)
      when is_integer(fvar_id) and fvar_id >= 0 do
    p_ty = Arena.type_of(arena, pred_id)

    with {:arrow, t, o} <- Map.fetch!(arena.type_table, p_ty),
         true <- o == Arena.ty_o(),
         false <- Arena.has_loose_bvar?(arena, pred_id, 0) do
      {arena, eps} = Arena.mk_const(arena, "$choice", {:arrow, p_ty, t})
      {arena, x} = Arena.mk_fvar(arena, fvar_id, t)
      {arena, eps_p} = Arena.mk_app(arena, eps, pred_id)
      {arena, px} = Arena.mk_app(arena, pred_id, x)
      {arena, p_eps} = Arena.mk_app(arena, pred_id, eps_p)
      {arena, px} = Arena.beta_eta_norm(arena, px)
      {arena, p_eps} = Arena.beta_eta_norm(arena, p_eps)
      {:ok, arena, MapSet.new([{:neg, px}, {:pos, p_eps}])}
    else
      _ -> :error
    end
  end

  def choice_instance(_arena, _pred_id, _fvar_id), do: :error

  # A replacement must be closed under binders and have the type of every occurrence
  # of its variable, in the parent or in another replacement (`Arena.subst_fvar/3`
  # also instantiates inside replacements). Variables are keyed by id only, so an
  # ill-typed replacement would otherwise build a well-formed-looking but
  # meaningless instance.
  defp validate_subst_types(%Arena{} = arena, subst_map, parent) do
    occurrences =
      Enum.reduce(parent, MapSet.new(), fn {_pol, atom}, acc ->
        MapSet.union(acc, Arena.free_vars(arena, atom))
      end)

    occurrences =
      Enum.reduce(subst_map, occurrences, fn {_v, rep}, acc ->
        MapSet.union(acc, Arena.free_vars(arena, rep))
      end)

    cond do
      Enum.any?(subst_map, fn {_v, rep} -> Arena.has_loose_bvar?(arena, rep, 0) end) ->
        {:error, :escaping_bvar_in_subst}

      Enum.any?(occurrences, fn {var_id, ty} ->
        case Map.fetch(subst_map, var_id) do
          {:ok, rep} -> Arena.type_of(arena, rep) != ty
          :error -> false
        end
      end) ->
        {:error, :ill_typed_subst}

      true ->
        {:ok, arena}
    end
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
