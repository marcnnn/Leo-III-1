defmodule Astraea.Calculus.ArgumentExtraction do
  @moduledoc """
  Argument extraction, after Leo-III's `ArgumentExtraction`
  (`leo.modules.calculus.ArgumentExtraction`): logical arguments of uninterpreted
  symbols are replaced by fresh constants with defining equations, so that
  first-order style reasoning (and external provers) see atoms instead of formulas
  in argument positions.

      p @ (^ [Y: $o]: (X & Y))   ~>   p @ (xarg_... @ X)
      ! [X, Y]: (xarg_... @ X @ Y) = (X & Y)

  An argument is extracted when the head of its application is applicable (an
  uninterpreted constant, a Skolem symbol or a variable) and the argument is
  logical according to `:type` (Leo-III's `xType`):

    * `:boolean` (0) - arguments of type `$o` whose head is a connective
      (`~`, `|`, `=`, `!`) or an interpreted `$`-symbol of function type
    * `:predicate` (1, the default) - the same for arguments of predicate type
      `T1 > ... > Tn > $o`, looking below their lambda prefix
    * `:function` (2) - additionally every lambda abstraction (beta-eta normal,
      so never an eta-expanded symbol); Leo-III leaves this case unimplemented

  The extracted term `t` is abstracted over its free variables (clause variables)
  and, with `local: true` (Leo-III's `xLocal`), over the variables bound around it
  (by quantifiers or lambdas); without it, terms that mention such variables are not
  extracted but searched for extractable subterms. Extraction is shallow: the
  definitions themselves are not processed further, callers do that.

  Symbols are content-addressed: the constant for `t` is named
  `xarg_<hash>` after the SHA-256 of the canonical bytes
  (`Astraea.Arena.canonical_bytes/2`) of the closed, beta-eta normal
  `^ [X1, ..., Xn]: t`. Equal terms get equal symbols, which replaces Leo-III's
  global extraction cache, and the result does not depend on processing order.
  The name also fixes the type. `definition_symbol/4` is shared with the formula
  renaming of `Astraea.Calculus.RenameCnf`.

  Soundness: for a fresh `c`, `! [X]: c @ X = t` is a conservative extension (every
  model interprets `c` as `^ [X]: t`), and under it replacing `t` by `c @ X` is an
  equivalence. Two occurrences of the same `t` share the same definition, so the
  extension stays consistent; callers must ensure that the names do not occur in
  the input (`Astraea.Normalization` checks this).
  """

  import Bitwise

  alias Astraea.{Arena, ProofChecker}
  alias Astraea.Calculus.Terms

  # Node tags (u8) matching `Astraea.Arena`
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

  @flag_has_bvar 0x01

  @typedoc "Extraction mode, as atom or as Leo-III's `xType` integer."
  @type mode :: :boolean | :predicate | :function | 0 | 1 | 2

  @typedoc "A defined constant together with its closed defining formula."
  @type definition :: {Arena.term_id(), Arena.term_id()}

  @doc """
  Extracts the arguments of `term_id` (any term; loose de Bruijn indices are
  allowed when `:binders` lists their types, innermost first). Options: `:type`
  (default `:predicate`), `:local` (default `false`). Returns the rewritten term
  and the definitions `{constant, ! [X]: c @ X = t}` it introduced, without
  duplicates.
  """
  @spec apply(Arena.t(), Arena.term_id(), keyword()) ::
          {Arena.t(), Arena.term_id(), [definition()]}
  def apply(%Arena{} = arena, term_id, opts \\ []) do
    ctx = %{
      mode: mode(Keyword.get(opts, :type, :predicate)),
      local: Keyword.get(opts, :local, false),
      defs: %{}
    }

    {arena, ctx, new} = walk(arena, ctx, term_id, Keyword.get(opts, :binders, []))
    {arena, new, definitions(ctx)}
  end

  @doc """
  Extracts the arguments of every literal of `clause` (see `apply/3`).
  """
  @spec apply_clause(Arena.t(), ProofChecker.clause(), keyword()) ::
          {Arena.t(), ProofChecker.clause(), [definition()]}
  def apply_clause(%Arena{} = arena, clause, opts \\ []) do
    {lits, {arena, defs}} =
      clause
      |> Enum.sort()
      |> Enum.map_reduce({arena, []}, fn {pol, atom}, {ar, acc} ->
        {ar, atom, defs} = __MODULE__.apply(ar, atom, opts)
        {{pol, atom}, {ar, acc ++ defs}}
      end)

    {arena, MapSet.new(lits), defs |> Enum.uniq() |> Enum.sort()}
  end

  @doc """
  Content-addressed constant `<prefix><hash>` defined as `term_id` abstracted over
  `vars` (fvar nodes, in argument order). The hash covers the closed, beta-eta
  normal abstraction and `prefix`. Returns the constant and its application to
  `vars`.
  """
  @spec definition_symbol(Arena.t(), String.t(), [Arena.term_id()], Arena.term_id()) ::
          {Arena.t(), Arena.term_id(), Arena.term_id()}
  def definition_symbol(%Arena{} = arena, prefix, vars, term_id) do
    {arena, closed} = abstract(arena, vars, term_id, &Arena.mk_lam/3)
    {arena, closed} = Arena.beta_eta_norm(arena, closed)
    digest = :crypto.hash(:sha256, [prefix, Arena.canonical_bytes(arena, closed)])
    name = prefix <> Base.encode16(binary_part(digest, 0, 8), case: :lower)

    {arena, ty} =
      vars
      |> Enum.reverse()
      |> Enum.reduce({arena, Arena.type_of(arena, term_id)}, fn v, {ar, acc} ->
        Arena.intern_type(ar, {:arrow, Arena.type_of(ar, v), acc})
      end)

    {arena, const} = Arena.mk_const(arena, name, ty)

    {arena, applied} =
      Enum.reduce(vars, {arena, const}, fn v, {ar, f} -> Arena.mk_app(ar, f, v) end)

    {arena, const, applied}
  end

  @doc """
  Universally closes `term_id` over `vars` (fvar nodes, outermost first).
  """
  @spec close(Arena.t(), [Arena.term_id()], Arena.term_id()) :: {Arena.t(), Arena.term_id()}
  def close(%Arena{} = arena, vars, term_id),
    do: abstract(arena, vars, term_id, &Arena.mk_forall/3)

  defp abstract(arena, vars, term_id, binder) do
    vars
    |> Enum.reverse()
    |> Enum.reduce({arena, term_id}, fn v, {ar, body} ->
      {ar, abstracted} = Arena.abstract_subterm(ar, body, v, 0)
      binder.(ar, Arena.type_of(ar, v), abstracted)
    end)
  end

  defp definitions(ctx) do
    ctx.defs |> Map.values() |> Enum.sort()
  end

  defp mode(m) when m in [:boolean, 0], do: :boolean
  defp mode(m) when m in [:predicate, 1], do: :predicate
  defp mode(m) when m in [:function, 2], do: :function

  # ---------------------------------------------------------------------------
  # Traversal
  # ---------------------------------------------------------------------------

  defp walk(arena, ctx, id, binders) do
    {tag, _flags, _ty, left, right} = Arena.get_node(arena, id)

    case tag do
      @tag_app ->
        {head, args} = Terms.spine(arena, id)
        applicable = applicable?(arena, head)

        {args, {arena, ctx}} =
          Enum.map_reduce(args, {arena, ctx}, fn arg, {ar, cx} ->
            if applicable and extractable?(ar, cx, arg) do
              {ar, cx, new} = extract(ar, cx, arg, binders)
              {new, {ar, cx}}
            else
              {ar, cx, new} = walk(ar, cx, arg, binders)
              {new, {ar, cx}}
            end
          end)

        {arena, new} =
          Enum.reduce(args, {arena, head}, fn a, {ar, f} -> Arena.mk_app(ar, f, a) end)

        {arena, ctx, new}

      @tag_lam ->
        {arena, ctx, body} = walk(arena, ctx, right, [left | binders])
        {arena, new} = Arena.mk_lam(arena, left, body)
        {arena, ctx, new}

      @tag_forall ->
        {arena, ctx, body} = walk(arena, ctx, right, [left | binders])
        {arena, new} = Arena.mk_forall(arena, left, body)
        {arena, ctx, new}

      @tag_not ->
        {arena, ctx, a} = walk(arena, ctx, left, binders)
        {arena, new} = Arena.mk_not(arena, a)
        {arena, ctx, new}

      t when t in [@tag_or, @tag_eq] ->
        {arena, ctx, l} = walk(arena, ctx, left, binders)
        {arena, ctx, r} = walk(arena, ctx, right, binders)

        {arena, new} =
          if t == @tag_or, do: Arena.mk_or(arena, l, r), else: Arena.mk_eq(arena, l, r)

        {arena, ctx, new}

      _ ->
        {arena, ctx, id}
    end
  end

  # Uninterpreted heads (Leo-III: variables and user constants).
  defp applicable?(arena, head) do
    case Arena.get_node(arena, head) do
      {@tag_const, _, _, sym, _} ->
        not String.starts_with?(Map.fetch!(arena.symbol_names, sym), "$")

      {tag, _, _, _, _} ->
        tag in [@tag_fvar, @tag_bvar, @tag_skolem]
    end
  end

  defp extractable?(arena, ctx, arg) do
    logical?(arena, ctx.mode, arg) and (ctx.local or not Arena.has_loose_bvar?(arena, arg, 0))
  end

  defp logical?(arena, :boolean, arg) do
    Arena.type_of(arena, arg) == Arena.ty_o() and connective_head?(arena, arg)
  end

  defp logical?(arena, :predicate, arg) do
    result_type(arena, Arena.type_of(arena, arg)) == Arena.ty_o() and
      connective_head?(arena, strip_lambdas(arena, arg))
  end

  defp logical?(arena, :function, arg) do
    logical?(arena, :predicate, arg) or Terms.tag(arena, arg) == @tag_lam
  end

  defp connective_head?(arena, id) do
    case Arena.get_node(arena, id) do
      {tag, _, _, _, _} when tag in [@tag_not, @tag_or, @tag_eq, @tag_forall] ->
        true

      {@tag_app, _, _, _, _} ->
        {head, _args} = Terms.spine(arena, id)
        interpreted_function?(arena, head)

      _ ->
        false
    end
  end

  # Leo-III: a system constant that is not of base type.
  defp interpreted_function?(arena, head) do
    case Arena.get_node(arena, head) do
      {@tag_const, _, ty, sym, _} ->
        String.starts_with?(Map.fetch!(arena.symbol_names, sym), "$") and
          match?({:arrow, _, _}, Map.fetch!(arena.type_table, ty))

      _ ->
        false
    end
  end

  defp strip_lambdas(arena, id) do
    case Arena.get_node(arena, id) do
      {@tag_lam, _, _, _, body} -> strip_lambdas(arena, body)
      _ -> id
    end
  end

  defp result_type(arena, ty) do
    case Map.fetch!(arena.type_table, ty) do
      {:arrow, _dom, cod} -> result_type(arena, cod)
      _ -> ty
    end
  end

  # ---------------------------------------------------------------------------
  # Extraction
  # ---------------------------------------------------------------------------

  # Replaces `arg` by `c @ X1 ... @ Xn @ B1 ... @ Bm` where the `Xi` are its free
  # variables (by id) and the `Bj` its loose bound variables (outermost first).
  defp extract(arena, ctx, arg, binders) do
    fvars = arena |> Arena.free_vars(arg) |> Enum.sort()
    loose = arena |> loose_indices(arg, 0, MapSet.new()) |> Enum.sort(:desc)
    base = Enum.reduce(fvars, 0, fn {id, _ty}, acc -> max(acc, id) end) + 1

    # Loose bound variables are opened to temporary free variables above `base`.
    {opened_vars, arena} =
      Enum.map_reduce(loose, arena, fn idx, ar ->
        ty = Enum.at(binders, idx)
        {ar, fv} = Arena.mk_fvar(ar, base + idx, ty)
        {{idx, fv, ty}, ar}
      end)

    {arena, opened} =
      open_loose(arena, arg, 0, Map.new(opened_vars, fn {i, fv, _} -> {i, fv} end))

    {fvar_nodes, arena} =
      Enum.map_reduce(fvars, arena, fn {id, ty}, ar ->
        {ar, fv} = Arena.mk_fvar(ar, id, ty)
        {fv, ar}
      end)

    vars = fvar_nodes ++ Enum.map(opened_vars, fn {_i, fv, _ty} -> fv end)
    {arena, const, applied_open} = definition_symbol(arena, "xarg_", vars, opened)
    {arena, eq} = Arena.mk_eq(arena, applied_open, opened)
    {arena, def_formula} = close(arena, vars, eq)

    # At the occurrence, the opened variables are the original bound variables.
    {arena, applied} =
      Enum.reduce(fvar_nodes, {arena, const}, fn v, {ar, f} -> Arena.mk_app(ar, f, v) end)

    {arena, applied} =
      Enum.reduce(opened_vars, {arena, applied}, fn {idx, _fv, ty}, {ar, f} ->
        {ar, bv} = Arena.mk_bvar(ar, idx, ty)
        Arena.mk_app(ar, f, bv)
      end)

    {arena, %{ctx | defs: Map.put(ctx.defs, const, {const, def_formula})}, applied}
  end

  defp loose_indices(arena, id, depth, acc) do
    {tag, flags, _ty, left, right} = Arena.get_node(arena, id)

    if band(flags, @flag_has_bvar) == 0 do
      acc
    else
      case tag do
        @tag_bvar -> if left >= depth, do: MapSet.put(acc, left - depth), else: acc
        @tag_not -> loose_indices(arena, left, depth, acc)
        t when t in [@tag_lam, @tag_forall] -> loose_indices(arena, right, depth + 1, acc)
        _ -> loose_indices(arena, right, depth, loose_indices(arena, left, depth, acc))
      end
    end
  end

  # Replaces the loose bound variable `depth + i` by the closed term `map[i]`.
  defp open_loose(arena, id, depth, map) do
    {tag, flags, _ty, left, right} = Arena.get_node(arena, id)

    if band(flags, @flag_has_bvar) == 0 or map_size(map) == 0 do
      {arena, id}
    else
      case tag do
        @tag_bvar ->
          case Map.fetch(map, left - depth) do
            {:ok, fv} when left >= depth -> {arena, fv}
            _ -> {arena, id}
          end

        @tag_not ->
          {arena, a} = open_loose(arena, left, depth, map)
          Arena.mk_not(arena, a)

        @tag_lam ->
          {arena, b} = open_loose(arena, right, depth + 1, map)
          Arena.mk_lam(arena, left, b)

        @tag_forall ->
          {arena, b} = open_loose(arena, right, depth + 1, map)
          Arena.mk_forall(arena, left, b)

        @tag_app ->
          {arena, l} = open_loose(arena, left, depth, map)
          {arena, r} = open_loose(arena, right, depth, map)
          Arena.mk_app(arena, l, r)

        @tag_eq ->
          {arena, l} = open_loose(arena, left, depth, map)
          {arena, r} = open_loose(arena, right, depth, map)
          Arena.mk_eq(arena, l, r)

        @tag_or ->
          {arena, l} = open_loose(arena, left, depth, map)
          {arena, r} = open_loose(arena, right, depth, map)
          Arena.mk_or(arena, l, r)

        _ ->
          {arena, id}
      end
    end
  end
end
