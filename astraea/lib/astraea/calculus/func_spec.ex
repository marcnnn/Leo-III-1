defmodule Astraea.Calculus.FuncSpec do
  @moduledoc """
  Function Synthesis via Choice (Leo-III `SolveFuncSpec` and `Control.ChoiceControl.guessFuncSpec`).

  Given a clause with negative equality literals involving flexible function applications:
      F(s_11, ..., s_1J) != t_1  | ... | F(s_N1, ..., s_NJ) != t_N
  where F is a free variable of function type tau_1 -> ... -> tau_J -> tau_res.

  Synthesizes the choice term:
      ^ [x_1, ..., x_J]: eps @ (^ [y]: (x_1 = s_11 & ... & x_J = s_1J => y = t_1) & ... & (x_1 = s_N1 & ... & x_J = s_NJ => y = t_N))
  where eps is the Hilbert choice operator of type (tau_res > $o) > tau_res ("$choice" or registered choice operator).
  """

  alias Astraea.Arena
  alias Astraea.Calculus.Terms

  @tag_fvar 3
  @tag_eq 6

  @doc """
  Detects function specification candidates in a clause item.
  Returns `{arena, [{var_id, synthesized_term}]}`.
  """
  @spec candidates(Arena.t(), map(), [Arena.term_id()]) ::
          {Arena.t(), [{non_neg_integer(), Arena.term_id()}]}
  def candidates(%Arena{} = arena, clause_item, choice_heads \\ []) do
    grouped = detect_specs(arena, clause_item.lits)

    Enum.reduce(grouped, {arena, []}, fn {var_id, {_fvar_ty, param_types, res_ty, specs}},
                                          {ar, acc} ->
      {ar, term} = synthesize(ar, param_types, res_ty, specs, choice_heads)
      {ar, [{var_id, term} | acc]}
    end)
  end

  @doc """
  Detects flexible function specifications from a clause literal set.
  Returns a map of `var_id => {fvar_ty, param_types, res_ty, specs}`.
  """
  @spec detect_specs(Arena.t(), Enumerable.t()) ::
          %{non_neg_integer() => {Arena.type_id(), [Arena.type_id()], Arena.type_id(), [{[Arena.term_id()], Arena.term_id()}]}}
  def detect_specs(%Arena{} = arena, lits) do
    specs_list =
      Enum.flat_map(lits, fn
        {:neg, eq_atom} ->
          case Arena.get_node(arena, eq_atom) do
            {@tag_eq, _, _, lhs, rhs} ->
              check_sides(arena, lhs, rhs)

            _ ->
              []
          end

        _ ->
          []
      end)

    specs_list
    |> Enum.group_by(&elem(&1, 0), fn {_var_id, fvar_ty, args, other} ->
      {fvar_ty, args, other}
    end)
    |> Enum.reduce(%{}, fn {var_id, entries}, acc ->
      {fvar_ty, _, _} = hd(entries)
      {param_types, res_ty} = split_fun_ty(arena, fvar_ty)
      param_count = length(param_types)

      specs =
        entries
        |> Enum.map(fn {_ty, args, other} -> {args, other} end)
        |> Enum.uniq()

      if param_count > 0 and Enum.all?(specs, fn {args, _other} -> length(args) == param_count end) do
        Map.put(acc, var_id, {fvar_ty, param_types, res_ty, specs})
      else
        acc
      end
    end)
  end

  defp check_sides(arena, lhs, rhs) do
    case {flex_app(arena, lhs), flex_app(arena, rhs)} do
      {{:ok, var_id, fvar_ty, args}, _} ->
        [{var_id, fvar_ty, args, rhs}]

      {_, {:ok, var_id, fvar_ty, args}} ->
        [{var_id, fvar_ty, args, lhs}]

      _ ->
        []
    end
  end

  defp flex_app(arena, term) do
    case Terms.spine(arena, term) do
      {head, [_ | _] = args} ->
        case Arena.get_node(arena, head) do
          {@tag_fvar, _, fvar_ty, var_id, _} ->
            {:ok, var_id, fvar_ty, args}

          _ ->
            :none
        end

      _ ->
        :none
    end
  end

  @doc """
  Splits an arrow type into parameter types and result type.
  """
  @spec split_fun_ty(Arena.t(), Arena.type_id()) :: {[Arena.type_id()], Arena.type_id()}
  def split_fun_ty(%Arena{} = arena, ty_id) do
    case Map.get(arena.type_table, ty_id) do
      {:arrow, dom, cod} ->
        {doms, res} = split_fun_ty(arena, cod)
        {[dom | doms], res}

      _ ->
        {[], ty_id}
    end
  end

  @doc """
  Synthesizes a choice term representing a function specification.
  """
  @spec synthesize(Arena.t(), [Arena.type_id()], Arena.type_id(), [{[Arena.term_id()], Arena.term_id()}], [Arena.term_id()]) ::
          {Arena.t(), Arena.term_id()}
  def synthesize(%Arena{} = arena, param_types, res_ty, specs, choice_heads \\ []) do
    param_count = length(param_types)

    # In de Bruijn indexing:
    # Outer: lambda x_0 ... lambda x_{J-1} (param_count lambdas)
    # Inner: lambda y (1 lambda)
    # Inside lambda y:
    # y is index 0.
    # x_j is index param_count - j (for j = 0..param_count-1).
    {arena, y_bvar} = Arena.mk_bvar(arena, 0, res_ty)

    {param_bvars, arena} =
      param_types
      |> Enum.with_index()
      |> Enum.map_reduce(arena, fn {pty, j}, ar ->
        {ar, bv} = Arena.mk_bvar(ar, param_count - j, pty)
        {bv, ar}
      end)

    # Build each specification clause: (x_0 = s_0 & ... & x_{J-1} = s_{J-1}) => y = t
    {case_terms, arena} =
      Enum.map_reduce(specs, arena, fn {args, res}, ar ->
        # Shift args and res under the (param_count + 1) binders
        {shifted_args, ar} =
          Enum.map_reduce(args, ar, fn arg, a ->
            {a2, s_arg} = Arena.shift(a, arg, param_count + 1, 0)
            {s_arg, a2}
          end)

        {ar, shifted_res} = Arena.shift(ar, res, param_count + 1, 0)

        # Antecedent: conjunction of x_j = s_ij
        {eqs, ar} =
          Enum.zip(param_bvars, shifted_args)
          |> Enum.map_reduce(ar, fn {x_bv, s_arg}, a ->
            {a2, eq} = Arena.mk_eq(a, x_bv, s_arg)
            {eq, a2}
          end)

        {ar, antecedent} = conjoin(ar, eqs)
        {ar, consequent} = Arena.mk_eq(ar, y_bvar, shifted_res)
        {ar, case_term} = Arena.mk_imp(ar, antecedent, consequent)
        {case_term, ar}
      end)

    {arena, spec_conjunction} = conjoin(arena, case_terms)
    {arena, y_lam} = Arena.mk_lam(arena, res_ty, spec_conjunction)

    # Choice operator: (res_ty > $o) > res_ty
    {arena, pred_ty} = Arena.intern_type(arena, {:arrow, res_ty, Arena.ty_o()})
    {arena, choice_ty} = Arena.intern_type(arena, {:arrow, pred_ty, res_ty})

    choice_op =
      Enum.find(choice_heads, fn head ->
        Arena.type_of(arena, head) == choice_ty
      end)

    {arena, eps} =
      if choice_op do
        {arena, choice_op}
      else
        Arena.mk_const(arena, "$choice", choice_ty)
      end

    {arena, eps_app} = Arena.mk_app(arena, eps, y_lam)

    # Wrap with outer parameter lambdas: lambda x_{J-1} ... lambda x_0
    {arena, result_lam} =
      Enum.reduce(Enum.reverse(param_types), {arena, eps_app}, fn pty, {ar, acc} ->
        Arena.mk_lam(ar, pty, acc)
      end)

    Arena.beta_eta_norm(arena, result_lam)
  end

  defp conjoin(arena, []), do: Arena.lookup_const(arena, "$true", Arena.ty_o())

  defp conjoin(arena, [single]), do: {arena, single}

  defp conjoin(arena, [first | rest]) do
    Enum.reduce(rest, {arena, first}, fn term, {ar, acc} ->
      Arena.mk_and(ar, acc, term)
    end)
  end
end
