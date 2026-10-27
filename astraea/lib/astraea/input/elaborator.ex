defmodule Astraea.Input.Elaborator do
  @moduledoc """
  Type-checking elaboration of `{:tptp, "~> 0.3.0"}` CSTs (THF, TFF, FOF and CNF)
  into `Astraea.Input.IR`.

  Besides plain HOL this covers TH1/TF1 polymorphism (type variables and explicit
  type arguments), arithmetic numerals and the overloaded arithmetic symbols,
  `@+`/`@-` (as `$choice`/`$description`), `$ite`, `$let` (by substitution),
  tuples, `$distinct`, distinct objects and the modal connectives of the TPTP
  non-classical syntax. First-order symbols without a declaration get the TFF
  default types (`$i` arguments, `$i` or `$o` result). Variables of `fof`/`cnf`
  statements that are not bound are closed universally.

  Anything outside this fragment raises `Astraea.Input.IR.Error`, so the problem is
  rejected rather than approximated.
  """

  alias Astraea.Input.{Arith, IR}
  alias Tptp.Node
  alias Tptp.Statement.Annotated

  import IR, only: [reject!: 1]

  @o IR.o()
  @i IR.i()

  defstruct lang: :thf,
            sig: %{},
            next_id: 0,
            tvars: %{},
            vars: %{},
            lets: %{},
            implicit: nil,
            implicit_names: %{},
            features: MapSet.new(),
            skolem_sorts: 0

  @type t :: %__MODULE__{}

  @typedoc "An elaborated statement, in input order."
  @type stmt ::
          {:sort, String.t()}
          | {:decl, String.t(), IR.ty()}
          | {:formula, String.t(), String.t(), [non_neg_integer()], IR.tm()}
          | {:logic, Node.t()}

  @wrappers ~w(thf_unitary_formula thf_unitary_term thf_unitary_type thf_monotype
               tff_unitary_formula tff_unitary_term tff_unitary_type tff_monotype
               fof_unitary_formula cnf_formula)a

  @lists ~w(thf_variable_list tff_variable_list fof_variable_list thf_formula_list
            tff_arguments fof_arguments thf_atom_typing_list tff_atom_typing_list
            thf_let_defn_list txf_let_defn_list tff_type_list tff_type_arguments)a

  @symbols ~w(constant functor system_constant system_functor type_constant type_functor)a
  @defined ~w(defined_constant defined_functor defined_type dollar_word)a
  @spines ~w(thf_apply_formula thf_fof_function fof_plain_term fof_defined_plain_term
             fof_system_term tff_plain_atomic tff_defined_plain tff_system_atomic)a
  @infix_eq ~w(thf_defined_infix tff_defined_infix fof_defined_infix_formula thf_definition)a
  @infix_neq ~w(thf_infix_unary tff_infix_unary fof_infix_unary)a
  @quantified ~w(thf_quantified_formula tff_quantified_formula fof_quantified_formula
                 tf1_quantified_type)a

  @formula_roles ~w(axiom hypothesis assumption lemma theorem corollary plain definition
                    conjecture negated_conjecture)

  @doc """
  Elaborates annotated statements in order. Returns the statements and the final
  context (signature, fresh-id counter and the set of used language features).
  """
  @spec elaborate([Annotated.t()]) :: {[stmt()], t()}
  def elaborate(statements) do
    Enum.flat_map_reduce(statements, %__MODULE__{}, fn
      %Annotated{} = st, ctx -> statement(%{ctx | lang: st.language}, st)
      _other, ctx -> {[], ctx}
    end)
  end

  @doc "The role without a `-local`/`-global` subrole."
  @spec base_role(String.t()) :: String.t()
  def base_role(role), do: role |> String.split("-", parts: 2) |> hd()

  # ---------------------------------------------------------------------------
  # Statements
  # ---------------------------------------------------------------------------

  defp statement(ctx, %Annotated{} = st) do
    name = Node.value(st.name)
    role = Node.value(st.role)

    cond do
      st.language not in [:thf, :tff, :fof, :cnf] ->
        reject!("unsupported language #{st.language}")

      role == "type" ->
        declaration(feature(ctx, st.language), st.formula)

      role == "logic" ->
        if st.language != :thf, do: reject!("logic specification outside thf")
        {[{:logic, st.formula}], feature(ctx, :modal)}

      base_role(role) in @formula_roles ->
        {ctx, tvars, ir} = formula_top(feature(ctx, st.language), st.formula, base_role(role))
        {[{:formula, name, role, tvars, ir}], ctx}

      true ->
        # `unknown`, `question`, `fi_*`, ... carry no assumption; dropping them can
        # only weaken the problem.
        {[], ctx}
    end
  end

  defp declaration(ctx, node) do
    case unwrap(node) do
      %Node{kind: k, children: [s, t]} when k in [:thf_atom_typing, :tff_atom_typing] ->
        declare(ctx, s, t)

      %Node{kind: k, children: [inner]} when k in [:thf_atom_typing, :tff_atom_typing] ->
        declaration(ctx, inner)

      other ->
        reject!("unsupported type declaration #{other.kind}")
    end
  end

  defp declare(ctx, sym_node, ty_node) do
    name = IR.user_name(Node.value(sym_node))

    case {kind_arity(ty_node), unwrap(ty_node)} do
      {{:ok, 0}, _} ->
        {[{:sort, name}], put_sig(ctx, name, {:sort})}

      {{:ok, n}, _} ->
        {[], ctx |> feature(:th1) |> put_sig(name, {:tcon, n})}

      {:error, %Node{kind: k} = q} when k in @quantified ->
        {ctx, tvs, ty} = poly_type(ctx, q)
        {[], ctx |> feature(:th1) |> put_sig(name, {:poly, tvs, ty})}

      {:error, _} ->
        {ctx, ty} = type(ctx, ty_node)
        {[{:decl, name, ty}], put_sig(ctx, name, {:mono, ty})}
    end
  end

  # `$tType`, `$tType > $tType`, `($tType * $tType) > $tType`, ...
  defp kind_arity(node) do
    case kind_leaves(unwrap(node)) do
      :error -> :error
      leaves -> {:ok, length(leaves) - 1}
    end
  end

  defp kind_leaves(%Node{kind: k, text: "$tType"}) when k in [:defined_constant, :defined_type],
    do: ["$tType"]

  defp kind_leaves(%Node{kind: k, children: cs})
       when k in [:thf_mapping_type, :tff_mapping_type, :tff_xprod_type, :thf_xprod_type] do
    Enum.reduce_while(cs, [], fn c, acc ->
      case kind_leaves(unwrap(c)) do
        :error -> {:halt, :error}
        leaves -> {:cont, acc ++ leaves}
      end
    end)
  end

  defp kind_leaves(_), do: :error

  defp poly_type(ctx, node) do
    {binder, var_nodes, body} = quantifier_parts(node)
    if binder != :type_forall, do: reject!("unsupported quantified type")
    saved = ctx.tvars
    {ids, ctx} = Enum.map_reduce(var_nodes, ctx, &bind_type_var(&2, &1))

    {ctx, more, ty} =
      case unwrap(body) do
        %Node{kind: k} = inner when k in @quantified ->
          poly_type(ctx, inner)

        _ ->
          {ctx, ty} = type(ctx, body)
          {ctx, [], ty}
      end

    {%{ctx | tvars: saved}, ids ++ more, ty}
  end

  defp bind_type_var(ctx, v) do
    {name, ty_node} = typed_var(v)
    unless tType?(ty_node), do: reject!("type quantifier over a non-type variable")
    {ctx, id} = fresh(ctx)
    {id, %{ctx | tvars: Map.put(ctx.tvars, name, {:tvar, id})}}
  end

  defp put_sig(ctx, name, entry) do
    case Map.fetch(ctx.sig, name) do
      {:ok, ^entry} ->
        ctx

      {:ok, other} ->
        reject!("conflicting declarations of #{name}: #{inspect(other)} and #{inspect(entry)}")

      :error ->
        %{ctx | sig: Map.put(ctx.sig, name, entry)}
    end
  end

  # ---------------------------------------------------------------------------
  # Formulas at statement level (TH1 type quantifier prefix)
  # ---------------------------------------------------------------------------

  defp formula_top(ctx, node, role) do
    implicit = if ctx.lang in [:fof, :cnf], do: [], else: nil
    ctx = %{ctx | vars: %{}, tvars: %{}, lets: %{}, implicit: implicit, implicit_names: %{}}
    {ctx, tvars, skolems, node} = type_prefix(ctx, unwrap(node), role, [], %{})
    {ctx, ir} = elab(ctx, node, @o)

    ir =
      Enum.reduce(ctx.implicit || [], ir, fn {:var, id, ty}, acc ->
        {:quant, :all, id, ty, acc}
      end)

    ir = if skolems == %{}, do: ir, else: IR.map_types(ir, &IR.subst_ty(&1, skolems))
    {%{ctx | implicit: nil, implicit_names: %{}}, tvars, ir}
  end

  # Peels `![A: $tType, ...]:` (and `?*`) off the top of a formula. In assumptions
  # universal type variables become schematic (monomorphized later) and existential
  # ones fresh sorts; in a conjecture universal ones become fresh sorts and
  # existential ones are rejected.
  defp type_prefix(ctx, %Node{kind: k} = node, role, tvars, skolems) when k in @quantified do
    {binder, var_nodes, body} = quantifier_parts(node)
    {type_vars, term_vars} = Enum.split_while(var_nodes, &type_var?/1)

    cond do
      Enum.any?(term_vars, &type_var?/1) ->
        reject!("type variable after a term variable in a quantifier prefix")

      type_vars == [] or binder not in [:forall, :type_forall, :exists, :type_exists] ->
        {ctx, tvars, skolems, node}

      true ->
        universal? = binder in [:forall, :type_forall]

        if not universal? and role == "conjecture",
          do: reject!("existential type quantifier in a conjecture")

        {ids, ctx} = Enum.map_reduce(type_vars, feature(ctx, :th1), &bind_type_var(&2, &1))

        {ctx, tvars, skolems} =
          if universal? and role != "conjecture" do
            {ctx, tvars ++ ids, skolems}
          else
            Enum.reduce(ids, {ctx, tvars, skolems}, fn id, {ctx, tvs, sk} ->
              n = ctx.skolem_sorts + 1
              {%{ctx | skolem_sorts: n}, tvs, Map.put(sk, id, {:base, "$$tsk#{n}"})}
            end)
          end

        if term_vars == [],
          do: type_prefix(ctx, unwrap(body), role, tvars, skolems),
          else: {ctx, tvars, skolems, {:requantify, binder, term_vars, body}}
    end
  end

  defp type_prefix(ctx, node, _role, tvars, skolems), do: {ctx, tvars, skolems, node}

  defp type_var?(v), do: v |> typed_var() |> elem(1) |> tType?()

  # ---------------------------------------------------------------------------
  # Types
  # ---------------------------------------------------------------------------

  defp type(ctx, node) do
    node = unwrap(node)

    case node.kind do
      k when k in [:defined_constant, :defined_type] ->
        ty = defined_type(node.text)
        {if(ty in Arith.types(), do: feature(ctx, :arith), else: ctx), ty}

      k when k in @symbols ->
        name = IR.user_name(Node.value(node))

        case Map.get(ctx.sig, name) do
          nil -> {put_sig(ctx, name, {:sort}), {:base, name}}
          {:sort} -> {ctx, {:base, name}}
          other -> reject!("#{name} (#{inspect(other)}) used as a sort")
        end

      :variable ->
        case Map.fetch(ctx.tvars, Node.value(node)) do
          {:ok, tv} -> {ctx, tv}
          :error -> reject!("unbound type variable #{Node.value(node)}")
        end

      :thf_apply_formula ->
        {head, args} = spine(node)
        type_app(ctx, head, args)

      :tff_atomic_type ->
        [head | rest] = node.children
        type_app(ctx, head, Enum.flat_map(rest, &flatten/1))

      :thf_mapping_type ->
        [a, b] = node.children
        {ctx, a} = type(ctx, a)
        {ctx, b} = type(ctx, b)
        {ctx, {:fun, a, b}}

      :tff_mapping_type ->
        [dom, cod] = node.children
        {ctx, doms} = types(ctx, xprod(dom))
        {ctx, cod} = type(ctx, cod)
        {ctx, IR.arrows(doms, cod)}

      k when k in [:thf_tuple, :txf_tuple_type] ->
        case Enum.flat_map(node.children, &flatten/1) do
          [] ->
            reject!("empty tuple type")

          elems ->
            {ctx, tys} = types(ctx, elems)
            {feature(ctx, :tuple), {:tuple, tys}}
        end

      other ->
        reject!("unsupported type expression #{other}")
    end
  end

  defp types(ctx, nodes) do
    {tys, ctx} = Enum.map_reduce(nodes, ctx, fn n, ctx -> ctx |> type(n) |> swap() end)
    {ctx, tys}
  end

  defp xprod(node) do
    case unwrap(node) do
      %Node{kind: k, children: cs} when k in [:tff_xprod_type, :thf_xprod_type] ->
        Enum.flat_map(cs, &xprod/1)

      other ->
        [other]
    end
  end

  defp type_app(ctx, head, args) do
    name = IR.user_name(Node.value(unwrap(head)))

    case Map.get(ctx.sig, name) do
      {:tcon, n} when n == length(args) ->
        {ctx, tys} = types(ctx, args)
        {ctx, {:tapp, name, tys}}

      other ->
        reject!("bad type constructor application #{name} (#{inspect(other)})")
    end
  end

  defp defined_type(text) do
    case text do
      t when t in ["$o", "$oType"] -> @o
      t when t in ["$i", "$iType"] -> @i
      t when t in ["$int", "$rat", "$real"] -> {:base, t}
      other -> reject!("unsupported defined type #{other}")
    end
  end

  defp tType?(nil), do: false
  defp tType?(node), do: match?(%Node{text: "$tType"}, unwrap(node))

  # ---------------------------------------------------------------------------
  # Terms and formulas
  # ---------------------------------------------------------------------------

  defp elab(ctx, {:requantify, binder, vars, body}, expected),
    do: quantifier(ctx, binder, vars, body, expected)

  defp elab(ctx, node, expected) do
    node = unwrap(node)

    case node.kind do
      k when k in @quantified ->
        {binder, vars, body} = quantifier_parts(node)
        quantifier(ctx, binder, vars, body, expected)

      k when k in [:thf_prefix_unary, :tff_prefix_unary] ->
        [op, arg] = node.children
        {ctx, a} = elab(ctx, arg, @o)

        case op.kind do
          :tilde -> {ctx, {:not, a}}
          :short_bracket -> {feature(ctx, :modal), {:modal, :box, nil, a}}
          :short_angle -> {feature(ctx, :modal), {:modal, :dia, nil, a}}
          other -> reject!("unsupported unary connective #{other}")
        end

      k when k in [:fof_unary_formula, :cnf_literal] ->
        [arg] = node.children
        {ctx, a} = elab(ctx, arg, @o)
        {ctx, {:not, a}}

      k when k in @infix_eq ->
        [l, r] = node.children
        equation(ctx, l, r)

      k when k in @infix_neq ->
        [l, r] = node.children
        {ctx, eq} = equation(ctx, l, r)
        {ctx, {:not, eq}}

      k when k in [:thf_and_formula, :tff_and_formula, :fof_and_formula] ->
        binary(ctx, node.children, &{:bin, :and, &1, &2})

      k when k in [:thf_or_formula, :tff_or_formula, :fof_or_formula, :cnf_disjunction] ->
        binary(ctx, node.children, &{:bin, :or, &1, &2})

      k when k in [:thf_binary_pair, :tff_binary_pair, :fof_binary_pair] ->
        [l, op, r] = node.children
        binary(ctx, [l, r], &connective(op.kind, &1, &2))

      k when k in [:thf_let, :txf_let] ->
        let(ctx, node, expected)

      k when k in [:thf_tuple, :txf_tuple] ->
        tuple(ctx, Enum.flat_map(node.children, &flatten/1))

      k when k in @spines ->
        {head, args} = spine(node)
        apply_head(ctx, head, args, expected)

      _ ->
        apply_head(ctx, node, [], expected)
    end
  end

  defp binary(ctx, [l, r], build) do
    {ctx, l} = elab(ctx, l, @o)
    {ctx, r} = elab(ctx, r, @o)
    {ctx, build.(l, r)}
  end

  defp connective(:implies, l, r), do: {:bin, :imp, l, r}
  defp connective(:impliedby, l, r), do: {:bin, :imp, r, l}
  defp connective(:iff, l, r), do: {:bin, :iff, l, r}
  defp connective(:xor, l, r), do: {:not, {:bin, :iff, l, r}}
  defp connective(:nor, l, r), do: {:not, {:bin, :or, l, r}}
  defp connective(:nand, l, r), do: {:not, {:bin, :and, l, r}}
  defp connective(:vline, l, r), do: {:bin, :or, l, r}
  defp connective(:ampersand, l, r), do: {:bin, :and, l, r}
  defp connective(other, _, _), do: reject!("unsupported binary connective #{other}")

  defp equation(ctx, l, r) do
    # An undeclared constant takes its type from the other side.
    swap? = undeclared_constant?(ctx, l) and not undeclared_constant?(ctx, r)
    {first, second} = if swap?, do: {r, l}, else: {l, r}
    {ctx, a} = elab(ctx, first, nil)
    {ctx, b} = elab(ctx, second, IR.type_of(a))

    if IR.type_of(a) != IR.type_of(b),
      do: reject!("equation between #{IR.show(IR.type_of(a))} and #{IR.show(IR.type_of(b))}")

    {ctx, if(swap?, do: {:eq, b, a}, else: {:eq, a, b})}
  end

  defp undeclared_constant?(ctx, node) do
    case unwrap(node) do
      %Node{kind: k} = n when k in @symbols ->
        not Map.has_key?(ctx.sig, IR.user_name(Node.value(n))) and
          not Map.has_key?(ctx.lets, Node.value(n))

      _ ->
        false
    end
  end

  defp quantifier(ctx, binder, var_nodes, body, expected) do
    saved = ctx.vars
    {bound, ctx} = Enum.map_reduce(var_nodes, ctx, &bind_var(&2, &1))

    {ctx, result} =
      case binder do
        q when q in [:forall, :exists] ->
          {ctx, b} = elab(ctx, body, @o)
          tag = if q == :forall, do: :all, else: :ex

          {ctx,
           Enum.reduce(Enum.reverse(bound), b, fn {:var, id, ty}, acc ->
             {:quant, tag, id, ty, acc}
           end)}

        :lambda ->
          {ctx, b} = elab(ctx, body, lambda_codomain(expected, length(bound)))
          {ctx, lam(bound, b)}

        q when q in [:choice, :desc] ->
          unless length(bound) == 1, do: reject!("choice binder over several variables")
          [{:var, _, ty} = x] = bound
          {ctx, b} = elab(ctx, body, @o)

          {name, feat} =
            if q == :choice, do: {"$choice", :choice}, else: {"$description", :description}

          op = {:const, name, [], {:fun, {:fun, ty, @o}, ty}}
          {feature(ctx, feat), {:app, op, lam([x], b)}}

        other ->
          reject!("unsupported quantifier #{other}")
      end

    {%{ctx | vars: saved}, result}
  end

  defp bind_var(ctx, v) do
    {name, ty_node} = typed_var(v)
    if tType?(ty_node), do: reject!("type quantifier below the top level")

    {ctx, ty} =
      cond do
        ty_node != nil -> type(ctx, ty_node)
        ctx.lang == :thf -> reject!("untyped variable #{name} in thf")
        true -> {ctx, @i}
      end

    {ctx, var} = fresh_var(ctx, ty)
    {var, %{ctx | vars: Map.put(ctx.vars, name, var)}}
  end

  defp lambda_codomain(nil, _), do: nil
  defp lambda_codomain(ty, 0), do: ty
  defp lambda_codomain({:fun, _, cod}, n), do: lambda_codomain(cod, n - 1)
  defp lambda_codomain(_, _), do: nil

  # ---------------------------------------------------------------------------
  # Application spines
  # ---------------------------------------------------------------------------

  defp apply_head(ctx, head, args, expected) do
    head = unwrap(head)

    case head.kind do
      k when k in @symbols ->
        symbol(ctx, head, args, expected)

      :variable ->
        variable(ctx, head, args)

      k when k in @defined ->
        defined(ctx, head.text, args, expected)

      k when k in [:integer, :rational, :real] ->
        no_args(args, numeral(ctx, k, head.text))

      :distinct_object ->
        no_args(args, {feature(ctx, :distinct), {:const, head.text, [], @i}})

      :thf_defined_atomic ->
        defined_atomic(ctx, hd(head.children), args, expected)

      k when k in [:big_forall, :big_exists, :big_choice, :big_desc, :big_equal] ->
        big(ctx, k, args, expected)

      :nhf_long_connective ->
        long_connective(ctx, head, args)

      k when args == [] ->
        reject!("unsupported construct #{k}")

      _ ->
        {ctx, f} = elab(ctx, head, nil)
        apply_args(ctx, f, args)
    end
  end

  defp no_args([], result), do: result
  defp no_args(_, _), do: reject!("constant applied to arguments")

  defp symbol(ctx, node, args, expected) do
    raw = Node.value(node)
    name = IR.user_name(raw)

    case {Map.fetch(ctx.lets, raw), Map.get(ctx.sig, name)} do
      {{:ok, term}, _} ->
        apply_args(ctx, term, args)

      {:error, {:mono, ty}} ->
        apply_args(ctx, {:const, name, [], ty}, args)

      {:error, {:poly, tvs, ty}} ->
        if length(args) < length(tvs), do: reject!("missing type arguments of #{name}")
        {ty_args, rest} = Enum.split(args, length(tvs))
        {ctx, tys} = types(ctx, ty_args)
        s = Map.new(Enum.zip(tvs, tys))
        apply_args(ctx, {:const, name, tys, IR.subst_ty(ty, s)}, rest)

      {:error, nil} ->
        {ctx, terms} = elab_all(ctx, args, @i)
        ty = IR.arrows(Enum.map(terms, &IR.type_of/1), expected || @i)
        {put_sig(ctx, name, {:mono, ty}), IR.app({:const, name, [], ty}, terms)}

      {:error, other} ->
        reject!("#{name} (#{inspect(other)}) used as a term")
    end
  end

  defp variable(ctx, node, args) do
    name = Node.value(node)

    {ctx, var} =
      case {Map.fetch(ctx.vars, name), ctx.implicit} do
        {{:ok, var}, _} -> {ctx, var}
        {:error, vars} when is_list(vars) -> implicit_var(ctx, name)
        {:error, nil} -> reject!("free variable #{name}")
      end

    apply_args(ctx, var, args)
  end

  defp implicit_var(ctx, name) do
    case Map.fetch(ctx.implicit_names, name) do
      {:ok, var} ->
        {ctx, var}

      :error ->
        {ctx, var} = fresh_var(ctx, @i)
        names = Map.put(ctx.implicit_names, name, var)
        {%{ctx | implicit: [var | ctx.implicit], implicit_names: names}, var}
    end
  end

  defp apply_args(ctx, f, []), do: {ctx, f}

  defp apply_args(ctx, f, [a | rest]) do
    case IR.type_of(f) do
      {:fun, dom, _} ->
        {ctx, arg} = elab(ctx, a, dom)
        {ctx, f} = beta(ctx, f, arg)
        apply_args(ctx, f, rest)

      other ->
        reject!("cannot apply a term of type #{IR.show(other)}")
    end
  end

  # Applies a (let-bound or eta-expanded) term, reducing a leading lambda.
  defp beta(ctx, {:lam, id, ty, body}, arg) do
    if IR.type_of(arg) != ty,
      do: reject!("argument of type #{IR.show(IR.type_of(arg))} where #{IR.show(ty)} is expected")

    {t, next_id} = IR.subst(body, %{id => arg}, ctx.next_id)
    {%{ctx | next_id: next_id}, t}
  end

  defp beta(ctx, f, arg), do: {ctx, IR.apply_checked(f, arg)}

  defp beta_all(ctx, f, args),
    do: Enum.reduce(args, {ctx, f}, fn a, {ctx, f} -> beta(ctx, f, a) end)

  defp elab_all(ctx, nodes, expected) do
    {terms, ctx} =
      Enum.map_reduce(nodes, ctx, fn n, ctx -> ctx |> elab(n, expected) |> swap() end)

    {ctx, terms}
  end

  # ---------------------------------------------------------------------------
  # Interpreted symbols
  # ---------------------------------------------------------------------------

  defp defined(ctx, text, args, expected) do
    cond do
      text in ["$true", "$false"] -> no_args(args, {ctx, {:const, text, [], @o}})
      Arith.operator?(text) -> arithmetic(ctx, text, args)
      text == "$ite" -> ite(ctx, args, expected)
      text == "$distinct" -> distinct(ctx, args)
      true -> reject!("unsupported interpreted symbol #{text}")
    end
  end

  defp arithmetic(_ctx, op, []), do: reject!("unapplied arithmetic symbol #{op}")

  defp arithmetic(ctx, op, args) do
    {ctx, [first | _] = terms} = elab_all(ctx, args, nil)
    {arity, op_ty} = Arith.signature!(op, IR.type_of(first))
    if length(terms) > arity, do: reject!("#{op} applied to too many arguments")
    {feature(ctx, :arith), Enum.reduce(terms, {:const, op, [], op_ty}, &IR.apply_checked(&2, &1))}
  end

  defp numeral(ctx, kind, text) do
    if ctx.lang in [:fof, :cnf], do: reject!("numbers in #{ctx.lang}")
    {ty, name} = Arith.parse_numeral!(kind, text)
    {feature(ctx, :arith), {:const, name, [], ty}}
  end

  defp ite(ctx, [c, a, b | rest], expected) do
    {ctx, c} = elab(ctx, c, @o)
    {ctx, a} = elab(ctx, a, if(rest == [], do: expected))
    ty = IR.type_of(a)
    {ctx, b} = elab(ctx, b, ty)
    if IR.type_of(b) != ty, do: reject!("$ite branches of different types")

    term =
      if ty == @o,
        do: {:bin, :and, {:bin, :imp, c, a}, {:bin, :imp, {:not, c}, b}},
        else: IR.app({:const, "$$ite", [], IR.arrows([@o, ty, ty], ty)}, [c, a, b])

    apply_args(feature(ctx, :ite), term, rest)
  end

  defp ite(_ctx, _args, _expected), do: reject!("$ite needs three arguments")

  defp distinct(ctx, args) do
    {ctx, terms} = elab_all(ctx, args, nil)
    if length(terms) < 2, do: reject!("$distinct needs at least two arguments")

    if terms |> Enum.map(&IR.type_of/1) |> Enum.uniq() |> length() > 1,
      do: reject!("$distinct over different types")

    pairs =
      for {a, i} <- Enum.with_index(terms),
          {b, j} <- Enum.with_index(terms),
          i < j,
          do: {:not, {:eq, a, b}}

    {ctx, IR.conj(pairs)}
  end

  # `(&)`, `(=)`, `(~)`, ... as terms: eta-expanded, then applied.
  defp defined_atomic(ctx, %Node{kind: op}, args, expected) do
    case op do
      :tilde ->
        {ctx, x} = fresh_var(ctx, @o)
        apply_args(ctx, lam([x], {:not, x}), args)

      o when o in [:equal, :not_equal] ->
        {ctx, ty, pre, rest} = operand(ctx, args, expected, & &1)
        {ctx, x} = fresh_var(ctx, ty)
        {ctx, y} = fresh_var(ctx, ty)
        body = if o == :equal, do: {:eq, x, y}, else: {:not, {:eq, x, y}}
        {ctx, t} = beta_all(ctx, lam([x, y], body), pre)
        apply_args(ctx, t, rest)

      o ->
        {ctx, x} = fresh_var(ctx, @o)
        {ctx, y} = fresh_var(ctx, @o)
        apply_args(ctx, lam([x, y], connective(o, x, y)), args)
    end
  end

  # Determines the operand type of a polymorphic builtin from its first argument
  # (elaborated here and returned in `pre`) or from the expected type.
  defp operand(ctx, [first | rest], _expected, extract) do
    {ctx, t} = elab(ctx, first, nil)
    {ctx, extract.(IR.type_of(t)), [t], rest}
  end

  defp operand(ctx, [], {:fun, ty, _}, _extract), do: {ctx, ty, [], []}

  defp operand(_ctx, [], _, _),
    do: reject!("cannot infer the type of an unapplied polymorphic builtin")

  # `!!`, `??`, `@@+`, `@@-` and `@=`, with an explicit (TH1) or inferred type.
  defp big(ctx, kind, args, expected) do
    {ctx, ty, pre, rest} =
      cond do
        args != [] and type_node?(ctx, hd(args)) ->
          {ctx, ty} = type(ctx, hd(args))
          {ctx, ty, [], tl(args)}

        kind == :big_equal ->
          operand(ctx, args, expected, & &1)

        true ->
          operand(ctx, args, predicate_expectation(expected), fn
            {:fun, t, @o} -> t
            other -> reject!("#{kind} applied to a term of type #{IR.show(other)}")
          end)
      end

    pred_ty = {:fun, ty, @o}

    {ctx, term} =
      case kind do
        q when q in [:big_forall, :big_exists] ->
          {ctx, p} = fresh_var(ctx, pred_ty)
          {ctx, {:var, xid, _} = x} = fresh_var(ctx, ty)
          tag = if q == :big_forall, do: :all, else: :ex
          {ctx, lam([p], {:quant, tag, xid, ty, {:app, p, x}})}

        :big_choice ->
          {feature(ctx, :choice), {:const, "$choice", [], {:fun, pred_ty, ty}}}

        :big_desc ->
          {feature(ctx, :description), {:const, "$description", [], {:fun, pred_ty, ty}}}

        :big_equal ->
          {ctx, x} = fresh_var(ctx, ty)
          {ctx, y} = fresh_var(ctx, ty)
          {ctx, lam([x, y], {:eq, x, y})}
      end

    {ctx, term} = beta_all(ctx, term, pre)
    apply_args(ctx, term, rest)
  end

  # An unapplied `!!`, `??`, `@@+` or `@@-` is expected at `(T > $o) > _`.
  defp predicate_expectation({:fun, {:fun, t, @o}, _}), do: {:fun, t, nil}
  defp predicate_expectation(_), do: nil

  defp type_node?(ctx, node) do
    case unwrap(node) do
      %Node{kind: k, text: t} when k in [:defined_constant, :defined_type] ->
        t in ~w($o $i $oType $iType $int $rat $real)

      %Node{kind: :variable} = v ->
        Map.has_key?(ctx.tvars, Node.value(v))

      %Node{kind: k} = s when k in @symbols ->
        match?({tag} when tag == :sort, ctx.sig[IR.user_name(Node.value(s))]) or
          match?({:tcon, _}, ctx.sig[IR.user_name(Node.value(s))])

      %Node{kind: k} when k in [:thf_mapping_type, :tff_mapping_type] ->
        true

      %Node{kind: :thf_apply_formula} = n ->
        {head, _} = spine(n)

        match?(%Node{kind: k} when k in @symbols, unwrap(head)) and
          match?({:tcon, _}, ctx.sig[IR.user_name(Node.value(unwrap(head)))])

      _ ->
        false
    end
  end

  defp long_connective(ctx, %Node{children: [name_node | params]}, args) do
    op =
      case name_node.text do
        b when b in ["$box", "$necessary"] -> :box
        d when d in ["$dia", "$possible"] -> :dia
        other -> reject!("unsupported non-classical connective #{other}")
      end

    index =
      case params do
        [] -> nil
        [%Node{kind: :ntf_index, children: [ix]}] -> "#" <> Node.value(unwrap(ix))
        _ -> reject!("unsupported connective parameters")
      end

    {ctx, x} = fresh_var(ctx, @o)
    apply_args(feature(ctx, :modal), lam([x], {:modal, op, index, x}), args)
  end

  # ---------------------------------------------------------------------------
  # $let and tuples
  # ---------------------------------------------------------------------------

  defp let(ctx, %Node{children: [types, defns, body]}, expected) do
    {ctx, local} =
      Enum.reduce(flatten_let(types), {ctx, %{}}, fn typing, {ctx, acc} ->
        case unwrap(typing) do
          %Node{kind: k, children: [sym, ty]} when k in [:thf_atom_typing, :tff_atom_typing] ->
            {ctx, ty} = type(ctx, ty)
            {ctx, Map.put(acc, Node.value(sym), ty)}

          other ->
            reject!("unsupported $let typing #{other.kind}")
        end
      end)

    {ctx, bindings} =
      Enum.reduce(flatten_let(defns), {ctx, %{}}, fn defn, {ctx, acc} ->
        %Node{children: [lhs, rhs]} = unwrap(defn)
        {head, params} = spine(unwrap(lhs))
        sym = Node.value(unwrap(head))
        ty = Map.get(local, sym) || reject!("$let definition of undeclared #{inspect(sym)}")
        if Map.has_key?(acc, sym), do: reject!("$let defines #{sym} twice")
        {ctx, term} = let_definition(ctx, ty, params, rhs)
        {ctx, Map.put(acc, sym, term)}
      end)

    if map_size(bindings) != map_size(local), do: reject!("$let symbol without definition")
    saved = ctx.lets
    {ctx, b} = elab(%{ctx | lets: Map.merge(ctx.lets, bindings)}, body, expected)
    {feature(%{ctx | lets: saved}, :let), b}
  end

  # The definitions of one `$let` are simultaneous: right-hand sides are elaborated
  # in the outer scope, with the left-hand side variables bound.
  defp let_definition(ctx, ty, params, rhs) do
    saved = ctx.vars

    {vars, {ctx, cod}} =
      Enum.map_reduce(params, {ctx, ty}, fn p, {ctx, ty} ->
        case {unwrap(p), ty} do
          {%Node{kind: :variable} = v, {:fun, dom, cod}} ->
            {ctx, var} = fresh_var(ctx, dom)
            {var, {%{ctx | vars: Map.put(ctx.vars, Node.value(v), var)}, cod}}

          _ ->
            reject!("unsupported $let left-hand side")
        end
      end)

    {ctx, body} = elab(ctx, rhs, cod)
    if IR.type_of(body) != cod, do: reject!("$let definition of the wrong type")
    {%{ctx | vars: saved}, lam(vars, body)}
  end

  defp tuple(_ctx, []), do: reject!("empty tuple")

  defp tuple(ctx, elems) do
    {ctx, terms} = elab_all(ctx, elems, nil)
    tys = Enum.map(terms, &IR.type_of/1)
    con = {:const, "$$tuple", [], IR.arrows(tys, {:tuple, tys})}
    {feature(ctx, :tuple), IR.app(con, terms)}
  end

  # ---------------------------------------------------------------------------
  # CST helpers
  # ---------------------------------------------------------------------------

  defp quantifier_parts(%Node{kind: :thf_quantified_formula, children: [q, body]}) do
    [binder, vars] = q.children
    {binder.kind, flatten(vars), body}
  end

  defp quantifier_parts(%Node{children: [binder, vars, body]}),
    do: {binder.kind, flatten(vars), body}

  defp typed_var(node) do
    case unwrap(node) do
      %Node{kind: k, children: [v, ty]} when k in [:thf_typed_variable, :tff_typed_variable] ->
        {Node.value(v), ty}

      %Node{kind: :variable} = v ->
        {Node.value(v), nil}

      other ->
        reject!("unsupported variable binding #{other.kind}")
    end
  end

  defp spine(%Node{kind: :thf_apply_formula, children: [f, a]}) do
    case unwrap(f) do
      %Node{kind: :thf_apply_formula} = inner ->
        {head, args} = spine(inner)
        {head, args ++ [a]}

      head ->
        {head, [a]}
    end
  end

  defp spine(%Node{children: [head | args]}), do: {head, Enum.flat_map(args, &flatten/1)}
  defp spine(%Node{} = leaf), do: {leaf, []}

  defp flatten(%Node{kind: k, children: cs}) when k in @lists, do: Enum.flat_map(cs, &flatten/1)
  defp flatten(node), do: [node]

  defp flatten_let(node) do
    case unwrap(node) do
      %Node{kind: k, children: cs}
      when k in [:thf_let_types, :txf_let_types, :thf_let_defns, :txf_let_defns] ->
        Enum.flat_map(cs, &flatten/1)

      other ->
        flatten(other)
    end
  end

  defp unwrap(%Node{kind: k, children: [child]}) when k in @wrappers, do: unwrap(child)
  defp unwrap(node), do: node

  defp lam(vars, body),
    do: Enum.reduce(Enum.reverse(vars), body, fn {:var, id, ty}, acc -> {:lam, id, ty, acc} end)

  defp fresh(ctx), do: {%{ctx | next_id: ctx.next_id + 1}, ctx.next_id}

  defp fresh_var(ctx, ty) do
    {ctx, id} = fresh(ctx)
    {ctx, {:var, id, ty}}
  end

  defp feature(ctx, f), do: %{ctx | features: MapSet.put(ctx.features, f)}

  defp swap({a, b}), do: {b, a}
end
