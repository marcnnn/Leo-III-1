defmodule Astraea.External.FolEncoding do
  @moduledoc """
  First-order encodings of `Astraea.Arena` clause sets for first-order provers,
  ported from Leo-III's `leo.modules.encoding` (`Encoding`, `TypedFOLEncoding`,
  `LambdaElimination`, `TypeEncoding`, `Monotonicity`).

  An encoding is a keyword list (or the preset `:default` / `:leo3`) with four
  independent dimensions:

    * `:lambda` - lambda elimination (`Astraea.External.LambdaElimination`)
      * `:lambda_lifting` (default) - each maximal lambda prefix becomes a fresh
        symbol over its free variables with a defining axiom `d<k>`
        (Leo-III `--lambda-elim lambda-lifting`, `LambdaElimStrategy_LambdaLifting`)
      * `:ski` - bracket abstraction into typed `S, K, I, B, C` combinator
        constants with their defining equations (Leo-III `--lambda-elim ski`,
        `LambdaElimStrategy_SKI`, Leo-III's default)
    * `:arity` - how symbols are applied
      * `:applicative` (default) - every symbol is a constant and application is
        the binary `astraea_app_<type>` (lifted symbols take their free variables
        directly)
      * `:min_arity` - each symbol takes as many arguments directly as its least
        applied occurrence has; the remaining arguments go through
        `astraea_app_<type>`, and `$o`-valued symbols that never occur in
        argument positions become predicates (Leo-III's `EncodingAnalyzer` and
        `foTransformType`, always on in Leo-III)
    * `:booleans` - formulas in term positions
      * `:lift` (default) - each one becomes a fresh symbol defined by
        `astraea_holds(sym(fvs)) <=> formula`
      * `:proxies` - connectives become proxy symbols (`astraea_not`,
        `astraea_or`, `astraea_eq_<type>`, `astraea_forall_<type>`,
        `astraea_true`, `astraea_false`) with Leo-III's proxy axioms
        (`TypedFOLEncodingSignature.proxyAxiomOf`)
    * `:types` - the type encoding, which also fixes the output dialect
      * `:mono_native` (default) - many-sorted TFF0 (Leo-III `MonoNative`)
      * `:mono_guards` - untyped FOF where every variable is relativized by a
        sort guard `astraea_is_<type>(X)` and every function symbol has a typing
        axiom (Leo-III `MonoGuards`, unimplemented there)
      * `:mono_guards_light` - untyped FOF where only sorts that the BBPS
        monotonicity calculus (`Astraea.External.Monotonicity`) cannot show
        monotonic are guarded (Leo-III `MonoGuardsLight`, unimplemented there;
        Blanchette et al.'s `g?`)

  `:leo3` is `[lambda: :ski, arity: :min_arity, booleans: :proxies, types: :mono_native]`,
  the configuration Leo-III uses for monomorphic TFF provers. Leo-III has no
  command-line flags for `:arity`, `:booleans` and `:types`; they mirror its
  internal choices (`EncodingAnalyzer`, proxies, `TypeEncoding` case objects).
  The polymorphic variants (`PolyNative`, `PolyGuards`, `PolyTags`) and type tags
  (`MonoTags`, `MonoTagsLight`) are not ported: Astraea's arena is monomorphic,
  and tags are unimplemented in Leo-III as well.

  ## Soundness and completeness

  Every variant is sound for refutations: each Henkin model of the clause set
  induces a model of the encoding (sorts are interpreted by the type domains,
  `astraea_bool` by the truth values with `astraea_holds` as identity, application
  by function application, fresh symbols by the values they are defined as), so
  an unsatisfiable encoding implies an unsatisfiable clause set. Guards preserve
  this: a typed model yields an untyped one over the union of the (for
  `:mono_guards_light`, monotonically extended) sort domains.

  No variant is complete for higher-order clause sets: there are no
  extensionality, Boolean exhaustiveness or comprehension axioms, so
  `Satisfiable` answers of first-order provers carry no meaning for them. For
  clause sets that are first-order already (`first_order?/2`), every variant is
  equisatisfiable with the input (the type encodings are complete, and the
  applicative and minimal-arity encodings of first-order clauses are), so
  `complete?/3` reports when a `Satisfiable` answer may be trusted.

  ## Differences from Leo-III

    * `:applicative` and `booleans: :lift` are Astraea's historical encoding and
      have no Leo-III counterpart; Leo-III always uses minimal arities and proxies.
    * The arity analysis runs after lambda elimination, so it sees exactly the
      applications that are printed (Leo-III approximates SKI's eta contractions
      with its `safeArity` analysis inside lambdas).
    * Function types are monomorphic sorts `astraea_fun_<type_id>` and `app`,
      combinators and proxies are instantiated per type, which is what Leo-III's
      `MonoNative` gets from monomorphizing its polymorphic `fun`/`hApp`.
    * Proxy axioms are added for the proxies in use only (Leo-III always adds
      `$true`/`$false` proxies once `bool` occurs), and the `=` proxy at `$o` is
      defined with `<=>` rather than equality on `astraea_bool`.
    * Lambda lifting contracts eta redexes before lifting.

  Clause `i` is named `c<i>` (or `<name_prefix><i>`); auxiliary axioms are named
  `d<k>` (definitions, combinator and proxy axioms) and `ty<k>` (guard axioms),
  which `Astraea.External.Reconstruct.clause_indices/1` drops.
  """

  alias Astraea.{Arena, ProofChecker}
  alias Astraea.External.LambdaElimination, as: LE

  @tag_const 1
  @tag_bvar 2
  @tag_fvar 3
  @tag_app 4
  @tag_lam 5
  @tag_eq 6
  @tag_not 7
  @tag_or 8
  @tag_forall 9
  @tag_skolem 10
  @tag_comb 11

  @combinators %{1 => :s, 2 => :k, 3 => :i, 4 => :b, 5 => :c}

  @lower_word ~r/^[a-z][A-Za-z0-9_]*$/

  @default [lambda: :lambda_lifting, arity: :applicative, booleans: :lift, types: :mono_native]
  @leo3 [lambda: :ski, arity: :min_arity, booleans: :proxies, types: :mono_native]
  @values [
    lambda: [:lambda_lifting, :ski],
    arity: [:applicative, :min_arity],
    booleans: [:lift, :proxies],
    types: [:mono_native, :mono_guards, :mono_guards_light]
  ]

  @typedoc "Normalized encoding, see the moduledoc."
  @type t :: [
          lambda: :lambda_lifting | :ski,
          arity: :applicative | :min_arity,
          booleans: :lift | :proxies,
          types: :mono_native | :mono_guards | :mono_guards_light
        ]

  @typedoc "First-order term: a sorted variable or a function application."
  @type fo_term :: {:var, String.t(), Arena.type_id()} | {:fn, String.t(), [fo_term()]}

  @typedoc "First-order formula over `fo_term/0`."
  @type fo_formula ::
          true
          | false
          | {:pred, String.t(), [fo_term()]}
          | {:eq, fo_term(), fo_term()}
          | {:not, fo_formula()}
          | {:or, fo_formula(), fo_formula()}
          | {:iff, fo_formula(), fo_formula()}
          | {:all, [{String.t(), Arena.type_id()}], fo_formula()}
          | {:exists, [{String.t(), Arena.type_id()}], fo_formula()}

  @typedoc """
  Symbol declarations: functions with argument and result type ids, predicates
  with argument type ids. Type `$o` as an argument or result is the sort
  `astraea_bool`.
  """
  @type signature :: %{
          String.t() => {:fun, [Arena.type_id()], Arena.type_id()} | {:pred, [Arena.type_id()]}
        }

  defmodule Problem do
    @moduledoc """
    An encoded first-order problem: named formulas over a signature. The arena
    may extend the input arena by the function types of fresh symbols.
    """
    defstruct arena: nil, encoding: [], formulas: [], signature: %{}

    @type t :: %__MODULE__{
            arena: Astraea.Arena.t(),
            encoding: Astraea.External.FolEncoding.t(),
            formulas: [
              %{
                name: String.t(),
                role: String.t(),
                formula: Astraea.External.FolEncoding.fo_formula()
              }
            ],
            signature: Astraea.External.FolEncoding.signature()
          }
  end

  @doc "The default encoding (the historical `Astraea.External.TffPrinter` one)."
  @spec default() :: t()
  def default, do: @default

  @doc "The encoding Leo-III uses for monomorphic TFF provers."
  @spec leo3() :: t()
  def leo3, do: @leo3

  @doc """
  Normalizes an encoding: `nil`, `:default`, `:leo3` or a keyword list whose
  missing keys take the defaults (`:leo3` may also be given as `base: :leo3`).
  Raises `ArgumentError` on unknown keys or values.
  """
  @spec normalize!(nil | atom() | keyword()) :: t()
  def normalize!(nil), do: @default
  def normalize!(:default), do: @default
  def normalize!(:leo3), do: @leo3

  def normalize!(opts) when is_list(opts) do
    {base, opts} = Keyword.pop(opts, :base, :default)
    base = normalize!(base)

    Enum.each(opts, fn {key, value} ->
      case Keyword.fetch(@values, key) do
        {:ok, allowed} ->
          unless value in allowed do
            raise ArgumentError,
                  "invalid encoding #{key}: #{inspect(value)}, expected one of #{inspect(allowed)}"
          end

        :error ->
          raise ArgumentError, "unknown encoding option #{inspect(key)}"
      end
    end)

    Enum.map(base, fn {key, default} -> {key, Keyword.get(opts, key, default)} end)
  end

  def normalize!(other), do: raise(ArgumentError, "invalid encoding #{inspect(other)}")

  @doc "Like `normalize!/1`, returning `{:ok, encoding}` or `{:error, {:invalid_encoding, message}}`."
  @spec normalize(term()) :: {:ok, t()} | {:error, {:invalid_encoding, String.t()}}
  def normalize(opts) do
    {:ok, normalize!(opts)}
  rescue
    e in ArgumentError -> {:error, {:invalid_encoding, Exception.message(e)}}
  end

  @doc "Returns `true` if `encoding` prints untyped FOF (a guard type encoding)."
  @spec untyped?(nil | atom() | keyword()) :: boolean()
  def untyped?(encoding), do: normalize!(encoding)[:types] != :mono_native

  @doc """
  Returns `true` if a `Satisfiable` answer for the encoding of `clauses` implies
  that `clauses` is satisfiable, i.e. if the clause set is first-order (see the
  moduledoc). The encoding itself does not matter for this.
  """
  @spec complete?(Arena.t(), [ProofChecker.clause()], nil | atom() | keyword()) :: boolean()
  def complete?(%Arena{} = arena, clauses, encoding \\ nil) do
    _ = normalize!(encoding)
    first_order?(arena, clauses)
  end

  @doc """
  Returns `true` if `clauses` lie in the first-order fragment: no lambdas or
  combinators, variables and quantifiers only over non-functional, non-Boolean
  types, every atom and argument an application of a constant to such terms, and
  no formulas in argument positions.
  """
  @spec first_order?(Arena.t(), [ProofChecker.clause()]) :: boolean()
  def first_order?(%Arena{} = arena, clauses) do
    Enum.all?(clauses, fn clause ->
      Enum.all?(clause, fn {_pol, atom} -> fo_formula?(arena, atom) end)
    end)
  end

  defp fo_formula?(arena, id) do
    {tag, _flags, _ty, left, right} = Arena.get_node(arena, id)

    case tag do
      @tag_not ->
        fo_formula?(arena, left)

      @tag_or ->
        fo_formula?(arena, left) and fo_formula?(arena, right)

      @tag_eq ->
        if Arena.type_of(arena, left) == Arena.ty_o(),
          do: fo_formula?(arena, left) and fo_formula?(arena, right),
          else:
            fo_sort?(arena, Arena.type_of(arena, left)) and fo_term?(arena, left) and
              fo_term?(arena, right)

      @tag_forall ->
        fo_sort?(arena, left) and fo_formula?(arena, right)

      _ ->
        fo_spine?(arena, id)
    end
  end

  defp fo_term?(arena, id), do: fo_sort?(arena, Arena.type_of(arena, id)) and fo_spine?(arena, id)

  defp fo_spine?(arena, id) do
    {tag, _flags, _ty, left, right} = Arena.get_node(arena, id)

    # `$true`/`$false` in argument positions are excluded by `fo_sort?/2` (type `$o`).
    case tag do
      @tag_app -> fo_term?(arena, right) and fo_spine?(arena, left)
      t when t in [@tag_const, @tag_skolem] -> true
      t when t in [@tag_fvar, @tag_bvar] -> fo_sort?(arena, Arena.type_of(arena, id))
      _ -> false
    end
  end

  defp fo_sort?(arena, ty) do
    case Map.fetch!(arena.type_table, ty) do
      {:arrow, _, _} -> false
      :o -> false
      _ -> true
    end
  end

  # ---------------------------------------------------------------------------
  # Encoding
  # ---------------------------------------------------------------------------

  @doc """
  Encodes `clauses` into a first-order `Problem`. Options:
    * `:encoding` - see the moduledoc (default `default/0`)
    * `:role` - formula role for every clause (default `"axiom"`)
    * `:name_prefix` - prefix for clause formula names (default `"c"`)

  The `:types` dimension is not applied here (guards are added when printing FOF,
  see `Astraea.External.FofPrinter`).
  """
  @spec encode(Arena.t(), [ProofChecker.clause()], keyword()) :: Problem.t()
  def encode(%Arena{} = arena, clauses, opts \\ []) do
    enc = normalize!(Keyword.get(opts, :encoding))
    role = Keyword.get(opts, :role, "axiom")
    prefix = Keyword.get(opts, :name_prefix, "c")
    st = LE.new(arena, enc)

    # 1. clauses to intermediate formulas (lambdas and Boolean terms still inside)
    {clause_fs, st} =
      Enum.map_reduce(clauses, st, fn clause, st -> clause_formula(st, clause) end)

    # 2. lambda and Boolean elimination
    {clause_fs, st} = Enum.map_reduce(clause_fs, st, &LE.eliminate_formula(&2, &1))
    {defs, st} = LE.definitions(st)

    # 3. combinator and proxy axioms for the symbols in use
    {axioms, st} = LE.symbol_axioms(st, clause_fs ++ defs)
    aux = defs ++ axioms

    # 4. arity analysis and first-order emission
    es = %{
      arena: st.arena,
      enc: enc,
      arity: arity_table(enc, st, clause_fs ++ aux),
      signature: %{}
    }

    {clause_fos, es} = Enum.map_reduce(clause_fs, es, &emit_formula(&2, &1))
    {aux_fos, es} = Enum.map_reduce(aux, es, &emit_formula(&2, &1))

    formulas =
      Enum.with_index(clause_fos, fn f, i ->
        %{name: prefix <> to_string(i), role: role, formula: f}
      end) ++
        Enum.with_index(aux_fos, fn f, k -> %{name: "d#{k}", role: "axiom", formula: f} end)

    %Problem{arena: es.arena, encoding: enc, formulas: formulas, signature: es.signature}
  end

  # A clause as the universal closure of the disjunction of its literals.
  defp clause_formula(st, clause) do
    lits = Enum.sort(clause)

    vars =
      lits
      |> Enum.reduce(MapSet.new(), fn {_pol, atom}, acc ->
        MapSet.union(acc, Arena.free_vars(st.arena, atom))
      end)
      |> Enum.sort()

    {fs, st} =
      Enum.map_reduce(lits, st, fn {pol, atom}, st ->
        {f, st} = formula(st, atom, [])
        {if(pol == :neg, do: {:not, f}, else: f), st}
      end)

    disj =
      case fs do
        [] -> false
        [f | rest] -> Enum.reduce(rest, f, &{:or, &2, &1})
      end

    {List.foldr(vars, disj, fn {id, ty}, body -> {:forall, {:v, id}, ty, body} end), st}
  end

  # ---------------------------------------------------------------------------
  # Arena to intermediate higher-order terms (see `Astraea.External.LambdaElimination`)
  # ---------------------------------------------------------------------------

  defp formula(st, id, ctx) do
    {tag, _flags, _ty, left, right} = Arena.get_node(st.arena, id)

    case tag do
      @tag_not ->
        {f, st} = formula(st, left, ctx)
        {{:not, f}, st}

      @tag_or ->
        {l, st} = formula(st, left, ctx)
        {r, st} = formula(st, right, ctx)
        {{:or, l, r}, st}

      @tag_eq ->
        if Arena.type_of(st.arena, left) == Arena.ty_o() do
          {l, st} = formula(st, left, ctx)
          {r, st} = formula(st, right, ctx)
          {{:iff, l, r}, st}
        else
          {l, st} = term(st, left, ctx)
          {r, st} = term(st, right, ctx)
          {{:eq, l, r}, st}
        end

      @tag_forall ->
        x = {:b, length(ctx)}
        {b, st} = formula(st, right, [{x, left} | ctx])
        {{:forall, x, left, b}, st}

      @tag_const ->
        case Map.fetch!(st.arena.symbol_names, left) do
          "$true" -> {true, st}
          "$false" -> {false, st}
          _ -> atom(st, id, ctx)
        end

      _ ->
        atom(st, id, ctx)
    end
  end

  defp atom(st, id, ctx) do
    {t, st} = term(st, id, ctx)
    {{:atom, t}, st}
  end

  defp term(st, id, ctx) do
    {tag, _flags, ty, left, right} = Arena.get_node(st.arena, id)

    case tag do
      @tag_const ->
        case Map.fetch!(st.arena.symbol_names, left) do
          "$true" -> boolean_term(st, id, ctx, {:proxy, true})
          "$false" -> boolean_term(st, id, ctx, {:proxy, false})
          name -> {{:sym, {:user, name}, ty}, st}
        end

      @tag_skolem ->
        {{:sym, {:skolem, left}, ty}, st}

      @tag_fvar ->
        {{:var, {:v, left}, ty}, st}

      @tag_bvar ->
        {x, x_ty} = Enum.at(ctx, left)
        {{:var, x, x_ty}, st}

      @tag_app ->
        {f, st} = term(st, left, ctx)
        {a, st} = term(st, right, ctx)
        {{:app, f, a, ty}, st}

      @tag_lam ->
        x = {:b, length(ctx)}
        {body, st} = term(st, right, [{x, left} | ctx])
        {{:lam, x, left, body, ty}, st}

      @tag_comb ->
        {{:sym, {:comb, Map.fetch!(@combinators, left)}, ty}, st}

      _connective ->
        boolean_term(st, id, ctx, nil)
    end
  end

  # A formula in term position: a `{:bool, formula}` leaf to be lifted, or (with
  # proxies) the application of proxy symbols to the translated arguments.
  defp boolean_term(%{enc: enc} = st, id, ctx, const) do
    if enc[:booleans] == :lift do
      {f, st} = formula(st, id, ctx)
      {{:bool, f}, st}
    else
      proxy_term(st, id, ctx, const)
    end
  end

  defp proxy_term(st, _id, _ctx, {:proxy, _} = key), do: {{:sym, key, Arena.ty_o()}, st}

  defp proxy_term(st, id, ctx, nil) do
    o = Arena.ty_o()
    {tag, _flags, _ty, left, right} = Arena.get_node(st.arena, id)

    case tag do
      @tag_not ->
        {a, st} = term(st, left, ctx)
        {sym, st} = LE.proxy(st, :not)
        LE.apply_args(st, sym, [a])

      @tag_or ->
        {l, st} = term(st, left, ctx)
        {r, st} = term(st, right, ctx)
        {sym, st} = LE.proxy(st, :or)
        LE.apply_args(st, sym, [l, r])

      @tag_eq ->
        {l, st} = term(st, left, ctx)
        {r, st} = term(st, right, ctx)
        {sym, st} = LE.proxy(st, {:eq, LE.type_of(l)})
        LE.apply_args(st, sym, [l, r])

      @tag_forall ->
        x = {:b, length(ctx)}
        {body, st} = term(st, right, [{x, left} | ctx])
        {lam_ty, st} = LE.arrow(st, [left], o)
        {sym, st} = LE.proxy(st, {:forall, left})
        LE.apply_args(st, sym, [{:lam, x, left, body, lam_ty}])
    end
  end

  # ---------------------------------------------------------------------------
  # Arity analysis (Leo-III `EncodingAnalyzer`)
  # ---------------------------------------------------------------------------

  # `{key, type} => {direct_args, argument_position?}`; missing entries mean `{0, true}`.
  # Applicative: lifted symbols take their free variables directly, unless SKI's eta
  # contraction left a shorter occurrence. Combinators are always constants (Leo-III).
  defp arity_table(enc, st, formulas) do
    table = Enum.reduce(formulas, %{}, &analyze_formula/2)

    case enc[:arity] do
      :applicative ->
        Map.new(st.lift_arity, fn {key, {ty, m}} ->
          {n, _pos?} = Map.get(table, {key, ty}, {m, true})
          {{key, ty}, {min(n, m), true}}
        end)

      :min_arity ->
        Map.reject(table, fn {{key, _ty}, _} -> match?({:comb, _}, key) end)
    end
  end

  defp analyze_formula(f, table) do
    case f do
      {:atom, t} -> analyze_spine(t, false, table)
      {:eq, l, r} -> analyze_spine(r, true, analyze_spine(l, true, table))
      {:not, g} -> analyze_formula(g, table)
      {:forall, _x, _ty, g} -> analyze_formula(g, table)
      {op, l, r} when op in [:or, :iff] -> analyze_formula(r, analyze_formula(l, table))
      _ -> table
    end
  end

  defp analyze_spine(t, arg_pos?, table) do
    {head, args} = LE.spine(t)
    table = Enum.reduce(args, table, &analyze_spine(&1, true, &2))

    case head do
      {:sym, key, ty} ->
        entry = {length(args), arg_pos?}

        Map.update(table, {key, ty}, entry, fn {n, pos?} ->
          {min(n, length(args)), pos? or arg_pos?}
        end)

      _ ->
        table
    end
  end

  # ---------------------------------------------------------------------------
  # First-order emission
  # ---------------------------------------------------------------------------

  defp emit_formula(es, f) do
    case f do
      bool when is_boolean(bool) ->
        {bool, es}

      {:atom, t} ->
        emit_atom(es, t)

      {:eq, l, r} ->
        {l, es} = emit_term(es, l)
        {r, es} = emit_term(es, r)
        {{:eq, l, r}, es}

      {:not, g} ->
        {g, es} = emit_formula(es, g)
        {{:not, g}, es}

      {op, l, r} when op in [:or, :iff] ->
        {l, es} = emit_formula(es, l)
        {r, es} = emit_formula(es, r)
        {{op, l, r}, es}

      {:forall, x, ty, g} ->
        {g, es} = emit_formula(es, g)

        case g do
          {:all, vars, body} -> {{:all, [{var_name(x), ty} | vars], body}, es}
          _ -> {{:all, [{var_name(x), ty}], g}, es}
        end
    end
  end

  defp emit_atom(es, t) do
    {head, args} = LE.spine(t)

    with {:sym, key, ty} <- head,
         {n, false} when n == length(args) <- arity(es, key, ty) do
      {fo_args, es} = Enum.map_reduce(args, es, &emit_term(&2, &1))
      name = symbol_name(key, ty)
      es = declare(es, name, {:pred, Enum.map(args, &LE.type_of/1)})
      {{:pred, name, fo_args}, es}
    else
      _ ->
        {fo, es} = emit_term(es, t)
        {{:pred, "astraea_holds", [fo]}, declare(es, "astraea_holds", {:pred, [Arena.ty_o()]})}
    end
  end

  defp emit_term(es, t) do
    {head, args} = LE.spine(t)

    case head do
      {:var, x, ty} ->
        apply_rest(es, {:var, var_name(x), ty}, ty, args)

      {:sym, key, ty} ->
        {k, _pos?} = arity(es, key, ty)
        {direct, rest} = Enum.split(args, k)
        {fo_args, es} = Enum.map_reduce(direct, es, &emit_term(&2, &1))
        name = symbol_name(key, ty)
        res_ty = peel(es.arena, ty, k)
        es = declare(es, name, {:fun, Enum.map(direct, &LE.type_of/1), res_ty})
        apply_rest(es, {:fn, name, fo_args}, res_ty, rest)
    end
  end

  defp apply_rest(es, fo, _ty, []), do: {fo, es}

  defp apply_rest(es, fo, ty, [arg | rest]) do
    {:arrow, dom, cod} = Map.fetch!(es.arena.type_table, ty)
    {a, es} = emit_term(es, arg)
    name = "astraea_app_" <> Integer.to_string(ty)
    es = declare(es, name, {:fun, [ty, dom], cod})
    apply_rest(es, {:fn, name, [fo, a]}, cod, rest)
  end

  defp arity(es, key, ty), do: Map.get(es.arity, {key, ty}, {0, true})

  defp peel(_arena, ty, 0), do: ty

  defp peel(arena, ty, k) do
    {:arrow, _dom, cod} = Map.fetch!(arena.type_table, ty)
    peel(arena, cod, k - 1)
  end

  defp declare(es, name, decl), do: %{es | signature: Map.put_new(es.signature, name, decl)}

  # ---------------------------------------------------------------------------
  # Rendering (shared by `TffPrinter` and `FofPrinter`)
  # ---------------------------------------------------------------------------

  @doc false
  # `binder.(quantifier, vars, body_iodata)` renders `{:all, ...}` / `{:exists, ...}`.
  def render_formula(f, binder) do
    case f do
      true -> "$true"
      false -> "$false"
      {:pred, name, []} -> name
      {:pred, name, args} -> [name, "(", Enum.map_intersperse(args, ", ", &render_term/1), ")"]
      {:eq, l, r} -> ["(", render_term(l), " = ", render_term(r), ")"]
      {:not, g} -> ["(~ ", render_formula(g, binder), ")"]
      {:or, l, r} -> ["(", render_formula(l, binder), " | ", render_formula(r, binder), ")"]
      {:iff, l, r} -> ["(", render_formula(l, binder), " <=> ", render_formula(r, binder), ")"]
      {q, vars, g} when q in [:all, :exists] -> binder.(q, vars, render_formula(g, binder))
    end
  end

  @doc false
  def render_term({:var, name, _ty}), do: name
  def render_term({:fn, name, []}), do: name

  def render_term({:fn, name, args}),
    do: [name, "(", Enum.map_intersperse(args, ", ", &render_term/1), ")"]

  # ---------------------------------------------------------------------------
  # Names
  # ---------------------------------------------------------------------------

  @doc false
  def var_name({:v, id}), do: "V" <> Integer.to_string(id)
  def var_name({:b, depth}), do: "B" <> Integer.to_string(depth)
  def var_name({:a, n}), do: "A" <> Integer.to_string(n)

  @doc false
  def symbol_name({:user, name}, _ty), do: const_name(name)
  def symbol_name({:skolem, hash}, _ty), do: skolem_name(hash)
  def symbol_name({:lift, k}, _ty), do: "astraea_lift_" <> Integer.to_string(k)
  def symbol_name({:comb, c}, ty), do: "astraea_comb_#{c}_#{ty}"
  def symbol_name({:proxy, {op, arg_ty}}, _ty), do: "astraea_#{op}_#{arg_ty}"
  def symbol_name({:proxy, op}, _ty), do: "astraea_#{op}"

  @doc """
  The TPTP sort name of an arena type in the first-order encoding.
  """
  @spec sort(Arena.t(), Arena.type_id()) :: String.t()
  def sort(arena, ty_id) do
    case Map.fetch!(arena.type_table, ty_id) do
      :i -> "$i"
      :o -> "astraea_bool"
      {:base, name} -> if Regex.match?(@lower_word, name), do: name, else: quote_atom(name)
      {:arrow, _dom, _cod} -> "astraea_fun_" <> Integer.to_string(ty_id)
    end
  end

  # User symbols never start with `astraea_`, so generated names cannot collide.
  defp const_name(name) do
    if Regex.match?(@lower_word, name) and not String.starts_with?(name, "astraea_"),
      do: name,
      else: quote_atom("u_" <> name)
  end

  defp skolem_name(hash) do
    "sk_" <> String.downcase(String.pad_leading(Integer.to_string(hash, 16), 8, "0"))
  end

  defp quote_atom(name) do
    "'" <> (name |> String.replace("\\", "\\\\") |> String.replace("'", "\\'")) <> "'"
  end
end
