defmodule Astraea.TptpLower do
  @moduledoc """
  Lowers TPTP THF0 problems (parsed with `{:tptp, "~> 0.3.0"}`) into the flat
  12-byte `Astraea.Arena` IR, resolving transitive `include('Axioms/...')` directives,
  interning user `$tType` base types and constant signatures, and converting
  quantifiers and lambda abstractions to de Bruijn indices.
  """

  alias Astraea.Arena
  alias Tptp.Node
  alias Tptp.Statement.Annotated

  defstruct arena: Arena.new(),
            base_types: %{
              "$o" => Arena.ty_o(),
              "$oType" => Arena.ty_o(),
              "$i" => Arena.ty_i(),
              "$iType" => Arena.ty_i()
            },
            const_types: %{},
            axioms: [],
            conjectures: [],
            definitions: []

  @type t :: %__MODULE__{
          arena: Arena.t(),
          base_types: %{String.t() => Arena.type_id()},
          const_types: %{String.t() => Arena.type_id()},
          axioms: [{String.t(), String.t(), Arena.term_id()}],
          conjectures: [{String.t(), Arena.term_id()}],
          definitions: [{String.t(), Arena.term_id()}]
        }

  @doc """
  Loads a TPTP THF0 file (expanding `include`s from `tptp_root`) and lowers all
  statements into an `Astraea.Arena`.
  """
  @spec from_file(Path.t(), keyword()) :: {:ok, t()} | {:error, term()}
  def from_file(path, opts \\ []) do
    tptp_root = Keyword.get(opts, :tptp_root, Astraea.TptpCorpus.default_tptp_root())
    resolver = {Tptp.Resolver.Fs, root: tptp_root}

    case Tptp.Unit.from_file(path, resolver: resolver, max_concurrency: 1) do
      {:ok, unit, _diagnostics} ->
        lower_unit(unit)

      {:error, _} = err ->
        err
    end
  end

  @spec from_string(String.t(), keyword()) :: {:ok, t()} | {:error, term()}
  def from_string(source, opts \\ []) do
    tptp_root = Keyword.get(opts, :tptp_root, Astraea.TptpCorpus.default_tptp_root())
    resolver = {Tptp.Resolver.Fs, root: tptp_root}

    {:ok, unit, _diagnostics} =
      Tptp.Unit.from_string(source, resolver: resolver, max_concurrency: 1)

    lower_unit(unit)
  end

  @spec lower_unit(Tptp.Unit.t()) :: {:ok, t()} | {:error, term()}
  def lower_unit(%Tptp.Unit{} = unit) do
    state = seed_builtins(%__MODULE__{})

    try do
      state =
        unit
        |> Tptp.Unit.statements()
        |> Enum.reduce(state, fn {_file_id, stmt}, acc ->
          lower_statement(acc, stmt)
        end)

      {:ok,
       %{
         state
         | axioms: Enum.reverse(state.axioms),
           conjectures: Enum.reverse(state.conjectures),
           definitions: Enum.reverse(state.definitions)
       }}
    rescue
      e in [ArgumentError, RuntimeError, KeyError, MatchError] ->
        {:error, Exception.message(e)}
    end
  end

  defp seed_builtins(%__MODULE__{arena: arena} = state) do
    {arena, _true_id} = Arena.mk_const(arena, "$true", :o)
    {arena, _false_id} = Arena.mk_const(arena, "$false", :o)

    %{
      state
      | arena: arena,
        const_types: %{
          "$true" => Arena.ty_o(),
          "$false" => Arena.ty_o()
        }
    }
  end

  defp lower_statement(%__MODULE__{} = state, %Annotated{language: :thf} = stmt) do
    name = Node.value(stmt.name)
    role = Node.value(stmt.role)

    case role do
      "type" ->
        lower_type_decl(state, stmt.formula)

      r when r in ["axiom", "hypothesis", "assumption", "lemma", "theorem", "corollary", "plain"] ->
        {state, term_id} = lower_term(state, stmt.formula, [])
        %{state | axioms: [{name, r, term_id} | state.axioms]}

      "definition" ->
        {state, term_id} = lower_term(state, stmt.formula, [])
        %{state | definitions: [{name, term_id} | state.definitions], axioms: [{name, "definition", term_id} | state.axioms]}

      r when r in ["conjecture", "negated_conjecture"] ->
        {state, term_id} = lower_term(state, stmt.formula, [])
        %{state | conjectures: [{name, term_id} | state.conjectures]}

      _ ->
        state
    end
  end

  defp lower_statement(%__MODULE__{} = state, _other), do: state

  # ---------------------------------------------------------------------------
  # Type Declarations (`thf(name, type, sym: ty).`)
  # ---------------------------------------------------------------------------

  defp lower_type_decl(%__MODULE__{} = state, %Node{kind: :thf_atom_typing, children: [inner]}) do
    lower_type_decl(state, inner)
  end

  defp lower_type_decl(%__MODULE__{} = state, %Node{kind: :thf_unitary_formula, children: [inner]}) do
    lower_type_decl(state, inner)
  end

  defp lower_type_decl(
         %__MODULE__{} = state,
         %Node{kind: :thf_atom_typing, children: [sym_node, type_node]}
       ) do
    sym_name = Node.value(sym_node)

    case unwrap_unitary(type_node) do
      %Node{kind: :defined_constant, text: "$tType"} ->
        {arena, ty_id} = Arena.intern_type(state.arena, {:base, sym_name})

        %{
          state
          | arena: arena,
            base_types: Map.put(state.base_types, sym_name, ty_id)
        }

      other_type_node ->
        {state, ty_id} = lower_type_expr(state, other_type_node)
        {arena, _const_id} = Arena.mk_const(state.arena, sym_name, ty_id)

        %{
          state
          | arena: arena,
            const_types: Map.put(state.const_types, sym_name, ty_id)
        }
    end
  end

  defp lower_type_expr(%__MODULE__{} = state, %Node{} = node) do
    case unwrap_unitary(node) do
      %Node{kind: k} = leaf when k in [:defined_constant, :constant, :type_constant, :system_type, :defined_type] ->
        name = Node.value(leaf)

        case Map.fetch(state.base_types, name) do
          {:ok, ty_id} ->
            {state, ty_id}

          :error ->
            {arena, ty_id} = Arena.intern_type(state.arena, {:base, name})
            {%{state | arena: arena, base_types: Map.put(state.base_types, name, ty_id)}, ty_id}
        end

      %Node{kind: :thf_mapping_type, children: [dom_node, cod_node]} ->
        {state, dom_id} = lower_type_expr(state, dom_node)
        {state, cod_id} = lower_type_expr(state, cod_node)
        {arena, arr_id} = Arena.intern_type(state.arena, {:arrow, dom_id, cod_id})
        {%{state | arena: arena}, arr_id}
    end
  end

  # ---------------------------------------------------------------------------
  # Term & Formula Lowering (`env` is a stack of `{var_name, type_id}` for de Bruijn)
  # ---------------------------------------------------------------------------

  defp lower_term(%__MODULE__{} = state, %Node{} = raw_node, env) do
    node = unwrap_unitary(raw_node)

    case node.kind do
      k when k in [:constant, :defined_constant, :system_constant, :functor, :defined_functor] ->
        name = Node.value(node)
        ty_id = Map.get(state.const_types, name, Arena.ty_o())
        {arena, id} = Arena.mk_const(state.arena, name, ty_id)
        {%{state | arena: arena}, id}

      :variable ->
        var_name = Node.value(node)

        case Enum.find_index(env, fn {v, _ty} -> v == var_name end) do
          nil ->
            # Free variable fallback (rare in closed THF formulas)
            <<fvar_id::32-big, _::binary>> = :crypto.hash(:sha256, var_name)
            {arena, id} = Arena.mk_fvar(state.arena, fvar_id, Arena.ty_i())
            {%{state | arena: arena}, id}

          de_bruijn_idx ->
            {_v, ty_id} = Enum.at(env, de_bruijn_idx)
            {arena, id} = Arena.mk_bvar(state.arena, de_bruijn_idx, ty_id)
            {%{state | arena: arena}, id}
        end

      :thf_defined_atomic ->
        [op_node] = node.children
        lower_ho_connective(state, op_node.kind)

      :thf_apply_formula ->
        [fun_node, arg_node] = node.children
        {state, fun_id} = lower_term(state, fun_node, env)
        {state, arg_id} = lower_term(state, arg_node, env)
        {arena, app_id} = Arena.mk_app(state.arena, fun_id, arg_id)
        {%{state | arena: arena}, app_id}

      :thf_prefix_unary ->
        [op_node, arg_node] = node.children
        {state, arg_id} = lower_term(state, arg_node, env)

        case op_node.kind do
          :tilde ->
            {arena, id} = Arena.mk_not(state.arena, arg_id)
            {%{state | arena: arena}, id}
        end

      :thf_and_formula ->
        [l_node, r_node] = node.children
        {state, l_id} = lower_term(state, l_node, env)
        {state, r_id} = lower_term(state, r_node, env)
        {arena, id} = Arena.mk_and(state.arena, l_id, r_id)
        {%{state | arena: arena}, id}

      :thf_or_formula ->
        [l_node, r_node] = node.children
        {state, l_id} = lower_term(state, l_node, env)
        {state, r_id} = lower_term(state, r_node, env)
        {arena, id} = Arena.mk_or(state.arena, l_id, r_id)
        {%{state | arena: arena}, id}

      k when k in [:thf_defined_infix, :thf_definition] ->
        [l_node, r_node] = node.children
        {state, l_id} = lower_term(state, l_node, env)
        {state, r_id} = lower_term(state, r_node, env)
        {arena, id} = Arena.mk_eq(state.arena, l_id, r_id)
        {%{state | arena: arena}, id}

      :thf_infix_unary ->
        # `s != t`
        [l_node, r_node] = node.children
        {state, l_id} = lower_term(state, l_node, env)
        {state, r_id} = lower_term(state, r_node, env)
        {arena, eq_id} = Arena.mk_eq(state.arena, l_id, r_id)
        {arena, neq_id} = Arena.mk_not(arena, eq_id)
        {%{state | arena: arena}, neq_id}

      :thf_binary_pair ->
        [l_node, op_node, r_node] = node.children
        {state, l_id} = lower_term(state, l_node, env)
        {state, r_id} = lower_term(state, r_node, env)
        {arena, id} = apply_binary_connective(state.arena, op_node.kind, l_id, r_id)
        {%{state | arena: arena}, id}

      :thf_quantified_formula ->
        [quant_node, body_node] = node.children
        [binder_node, vars_node] = quant_node.children
        {state, typed_vars} = collect_typed_vars(state, vars_node)

        # Push variables in left-to-right binder order onto the de Bruijn environment
        inner_env = Enum.reverse(typed_vars) ++ env
        {state, body_id} = lower_term(state, body_node, inner_env)

        # Fold binders from innermost (last in list) to outermost (first in list)
        arena =
          typed_vars
          |> Enum.reverse()
          |> Enum.reduce({state.arena, body_id}, fn {_v_name, var_ty_id}, {ar, acc_body} ->
            case binder_node.kind do
              :lambda -> Arena.mk_lam(ar, var_ty_id, acc_body)
              :forall -> Arena.mk_forall(ar, var_ty_id, acc_body)
              :exists -> Arena.mk_exists(ar, var_ty_id, acc_body)
            end
          end)

        {ar_final, term_final} = arena
        {%{state | arena: ar_final}, term_final}
    end
  end

  defp apply_binary_connective(arena, :implies, l_id, r_id), do: Arena.mk_imp(arena, l_id, r_id)
  defp apply_binary_connective(arena, :impliedby, l_id, r_id), do: Arena.mk_imp(arena, r_id, l_id)
  defp apply_binary_connective(arena, :iff, l_id, r_id), do: Arena.mk_iff(arena, l_id, r_id)

  defp apply_binary_connective(arena, :xor, l_id, r_id) do
    {arena, iff_id} = Arena.mk_iff(arena, l_id, r_id)
    Arena.mk_not(arena, iff_id)
  end

  defp apply_binary_connective(arena, :nor, l_id, r_id) do
    {arena, or_id} = Arena.mk_or(arena, l_id, r_id)
    Arena.mk_not(arena, or_id)
  end

  defp apply_binary_connective(arena, :nand, l_id, r_id) do
    {arena, and_id} = Arena.mk_and(arena, l_id, r_id)
    Arena.mk_not(arena, and_id)
  end

  defp lower_ho_connective(%__MODULE__{arena: arena} = state, :tilde) do
    # ^ [X: $o]: ~ X
    {arena, x0} = Arena.mk_bvar(arena, 0, :o)
    {arena, body} = Arena.mk_not(arena, x0)
    {arena, lam} = Arena.mk_lam(arena, :o, body)
    {%{state | arena: arena}, lam}
  end

  defp lower_ho_connective(%__MODULE__{arena: arena} = state, op_kind)
       when op_kind in [:ampersand, :vline, :implies, :impliedby, :iff, :xor, :nor, :nand] do
    # ^ [X: $o]: ^ [Y: $o]: (X <op> Y)
    # Inside 2 lambdas: X is BVar(1), Y is BVar(0)
    {arena, x} = Arena.mk_bvar(arena, 1, :o)
    {arena, y} = Arena.mk_bvar(arena, 0, :o)

    {arena, body} =
      case op_kind do
        :ampersand -> Arena.mk_and(arena, x, y)
        :vline -> Arena.mk_or(arena, x, y)
        other -> apply_binary_connective(arena, other, x, y)
      end

    {arena, lam1} = Arena.mk_lam(arena, :o, body)
    {arena, lam2} = Arena.mk_lam(arena, :o, lam1)
    {%{state | arena: arena}, lam2}
  end

  defp collect_typed_vars(%__MODULE__{} = state, %Node{kind: :thf_variable_list, children: [head, tail]}) do
    {state, v1} = collect_typed_vars(state, head)
    {state, v2} = collect_typed_vars(state, tail)
    {state, v1 ++ v2}
  end

  defp collect_typed_vars(
         %__MODULE__{} = state,
         %Node{kind: :thf_typed_variable, children: [var_node, type_node]}
       ) do
    var_name = Node.value(var_node)
    {state, ty_id} = lower_type_expr(state, type_node)
    {state, [{var_name, ty_id}]}
  end

  defp unwrap_unitary(%Node{kind: k, children: [child]})
       when k in [:thf_unitary_formula, :thf_unitary_term, :thf_unitary_type, :thf_monotype] do
    unwrap_unitary(child)
  end

  defp unwrap_unitary(%Node{} = node), do: node
end
