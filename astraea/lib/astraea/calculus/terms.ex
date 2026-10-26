defmodule Astraea.Calculus.Terms do
  @moduledoc """
  Spine view of `Astraea.Arena` terms shared by the higher-order calculus
  (`Astraea.Calculus.Unify`, `Astraea.Calculus.FingerprintIndex`, primitive
  substitution and search-time clausification).

  A beta-eta normal term of base type is either *flexible* (a free variable applied
  to arguments) or *rigid* (a constant, Skolem, combinator or bound variable applied
  to arguments, or one of the logical connectives `=`, `~`, `|`, `!`). `view/2`
  returns that head/argument decomposition; binders are exposed as a binder shift of
  the child so that callers can track de Bruijn depth without closures.
  """

  import Bitwise

  alias Astraea.Arena

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

  @flag_has_fvar 0x02

  @typedoc "Rigid head: a symbol node (constant, Skolem, combinator, bound variable) or a connective."
  @type head ::
          {:sym, Arena.term_id()}
          | {:eq, Arena.type_id()}
          | :not
          | :or
          | {:forall, Arena.type_id()}

  @typedoc "A child term together with the number of binders crossed to reach it."
  @type child :: {Arena.term_id(), 0 | 1}

  @type view ::
          {:flex, Arena.term_id(), [Arena.term_id()]}
          | {:rigid, head(), [child()]}
          | {:lam, Arena.type_id(), Arena.term_id()}

  @doc """
  Decomposes `term_id` into its flexible or rigid head and arguments.
  """
  @spec view(Arena.t(), Arena.term_id()) :: view()
  def view(%Arena{} = arena, term_id) do
    case Arena.get_node(arena, term_id) do
      {@tag_eq, _, _, l, r} -> {:rigid, {:eq, Arena.type_of(arena, l)}, [{l, 0}, {r, 0}]}
      {@tag_not, _, _, a, _} -> {:rigid, :not, [{a, 0}]}
      {@tag_or, _, _, l, r} -> {:rigid, :or, [{l, 0}, {r, 0}]}
      {@tag_forall, _, _, dom, body} -> {:rigid, {:forall, dom}, [{body, 1}]}
      {@tag_lam, _, _, dom, body} -> {:lam, dom, body}
      _ -> spine_view(arena, term_id)
    end
  end

  defp spine_view(arena, term_id) do
    {head, args} = spine(arena, term_id)

    case Arena.get_node(arena, head) do
      {@tag_fvar, _, _, _, _} -> {:flex, head, args}
      _ -> {:rigid, {:sym, head}, Enum.map(args, &{&1, 0})}
    end
  end

  @doc """
  Splits an application spine `h @ a1 @ ... @ an` into `{h, [a1, ..., an]}`.
  """
  @spec spine(Arena.t(), Arena.term_id()) :: {Arena.term_id(), [Arena.term_id()]}
  def spine(%Arena{} = arena, term_id), do: spine(arena, term_id, [])

  defp spine(arena, term_id, args) do
    case Arena.get_node(arena, term_id) do
      {@tag_app, _, _, fun, arg} -> spine(arena, fun, [arg | args])
      _ -> {term_id, args}
    end
  end

  @doc "Returns true iff `term_id` is a free variable, possibly applied to arguments."
  @spec flex?(Arena.t(), Arena.term_id()) :: boolean()
  def flex?(%Arena{} = arena, term_id) do
    {head, _args} = spine(arena, term_id)
    fvar?(arena, head)
  end

  @doc "Returns true iff `term_id` is a free-variable node."
  @spec fvar?(Arena.t(), Arena.term_id()) :: boolean()
  def fvar?(%Arena{} = arena, term_id), do: tag(arena, term_id) == @tag_fvar

  @doc "Returns true iff `term_id` is a bound-variable node."
  @spec bvar?(Arena.t(), Arena.term_id()) :: boolean()
  def bvar?(%Arena{} = arena, term_id), do: tag(arena, term_id) == @tag_bvar

  @doc "Returns true iff a free variable occurs in `term_id` (O(1) flag test)."
  @spec has_fvar?(Arena.t(), Arena.term_id()) :: boolean()
  def has_fvar?(%Arena{} = arena, term_id) do
    {_tag, flags, _ty, _l, _r} = Arena.get_node(arena, term_id)
    band(flags, @flag_has_fvar) != 0
  end

  @doc "Node tag of `term_id`."
  @spec tag(Arena.t(), Arena.term_id()) :: non_neg_integer()
  def tag(%Arena{} = arena, term_id), do: elem(Arena.get_node(arena, term_id), 0)

  @doc "The de Bruijn index of a bound-variable node."
  @spec bvar_index(Arena.t(), Arena.term_id()) :: non_neg_integer()
  def bvar_index(%Arena{} = arena, term_id) do
    {@tag_bvar, _, _, idx, _} = Arena.get_node(arena, term_id)
    idx
  end

  @doc "Returns true iff `term_id` is a symbol node (constant, Skolem or combinator)."
  @spec symbol?(Arena.t(), Arena.term_id()) :: boolean()
  def symbol?(%Arena{} = arena, term_id),
    do: tag(arena, term_id) in [@tag_const, @tag_skolem, @tag_comb]

  @doc "Returns true iff `term_id` is the constant named `name`."
  @spec const_named?(Arena.t(), Arena.term_id(), String.t()) :: boolean()
  def const_named?(%Arena{} = arena, term_id, name) do
    case Arena.get_node(arena, term_id) do
      {@tag_const, _, _, sym, _} -> Map.get(arena.symbol_names, sym) == name
      _ -> false
    end
  end

  @doc "Returns true iff `sub` occurs in `term_id` (outside of binders that capture it)."
  @spec subterm?(Arena.t(), Arena.term_id(), Arena.term_id()) :: boolean()
  def subterm?(%Arena{} = _arena, term_id, term_id), do: true

  def subterm?(%Arena{} = arena, term_id, sub) do
    case Arena.get_node(arena, term_id) do
      {tag, _, _, l, r} when tag in [@tag_app, @tag_eq, @tag_or] ->
        subterm?(arena, l, sub) or subterm?(arena, r, sub)

      {@tag_not, _, _, a, _} ->
        subterm?(arena, a, sub)

      _ ->
        false
    end
  end

  # ---------------------------------------------------------------------------
  # Types
  # ---------------------------------------------------------------------------

  @doc """
  Flattens `t1 > ... > tn > b` into `{[t1, ..., tn], b}` with `b` a base type.
  """
  @spec arrow_types(Arena.t(), Arena.type_id()) :: {[Arena.type_id()], Arena.type_id()}
  def arrow_types(%Arena{} = arena, ty) do
    case Map.fetch!(arena.type_table, ty) do
      {:arrow, dom, cod} ->
        {doms, base} = arrow_types(arena, cod)
        {[dom | doms], base}

      _ ->
        {[], ty}
    end
  end

  @doc "Interns `t1 > ... > tn > result`."
  @spec mk_arrows(Arena.t(), [Arena.type_id()], Arena.type_id()) :: {Arena.t(), Arena.type_id()}
  def mk_arrows(%Arena{} = arena, doms, result) do
    doms
    |> Enum.reverse()
    |> Enum.reduce({arena, result}, fn dom, {ar, cod} ->
      Arena.intern_type(ar, {:arrow, dom, cod})
    end)
  end

  @doc "Returns the domain type if `ty` is an arrow type, `nil` otherwise."
  @spec arrow_domain(Arena.t(), Arena.type_id()) :: Arena.type_id() | nil
  def arrow_domain(%Arena{} = arena, ty) do
    case Map.fetch!(arena.type_table, ty) do
      {:arrow, dom, _cod} -> dom
      _ -> nil
    end
  end

  # ---------------------------------------------------------------------------
  # Term construction
  # ---------------------------------------------------------------------------

  @doc "Builds `head @ a1 @ ... @ an`."
  @spec mk_apps(Arena.t(), Arena.term_id(), [Arena.term_id()]) :: {Arena.t(), Arena.term_id()}
  def mk_apps(%Arena{} = arena, head, args) do
    Enum.reduce(args, {arena, head}, fn arg, {ar, acc} -> Arena.mk_app(ar, acc, arg) end)
  end

  @doc "Builds `^ [X1: t1, ..., Xn: tn]: body` (binder types outermost first)."
  @spec mk_lams(Arena.t(), [Arena.type_id()], Arena.term_id()) :: {Arena.t(), Arena.term_id()}
  def mk_lams(%Arena{} = arena, doms, body) do
    doms
    |> Enum.reverse()
    |> Enum.reduce({arena, body}, fn dom, {ar, acc} -> Arena.mk_lam(ar, dom, acc) end)
  end

  @doc """
  The bound variables `X1, ..., Xn` of an `n`-ary binder prefix with types `doms`
  (outermost first), seen from `shift` further binders below the prefix.
  """
  @spec bound_args(Arena.t(), [Arena.type_id()], non_neg_integer()) ::
          {Arena.t(), [Arena.term_id()]}
  def bound_args(%Arena{} = arena, doms, shift \\ 0) do
    n = length(doms)

    doms
    |> Enum.with_index()
    |> Enum.map_reduce(arena, fn {dom, j}, ar ->
      {ar, bv} = Arena.mk_bvar(ar, n - 1 - j + shift, dom)
      {bv, ar}
    end)
    |> then(fn {bvs, ar} -> {ar, bvs} end)
  end

  @doc """
  The body of the eta-expansion of a term of arrow type: `body` for `^ [X]: body`,
  otherwise `t' @ X0` with `t'` shifted under the new binder.
  """
  @spec eta_body(Arena.t(), Arena.term_id()) :: {Arena.t(), Arena.term_id()}
  def eta_body(%Arena{} = arena, term_id) do
    case Arena.get_node(arena, term_id) do
      {@tag_lam, _, _, _dom, body} ->
        {arena, body}

      {_, _, ty, _, _} ->
        dom = arrow_domain(arena, ty)
        {arena, shifted} = Arena.shift(arena, term_id, 1, 0)
        {arena, x0} = Arena.mk_bvar(arena, 0, dom)
        Arena.mk_app(arena, shifted, x0)
    end
  end

  @doc """
  Renames the loose bound variables of `term_id`: index `i` (counted from the top of
  `term_id`) becomes `Map.fetch!(renaming, i)`. Returns `:error` if a loose bound
  variable has no image, so the result is the body of a pattern binding.
  """
  @spec rename_loose(Arena.t(), Arena.term_id(), %{non_neg_integer() => non_neg_integer()}) ::
          {:ok, Arena.t(), Arena.term_id()} | :error
  def rename_loose(%Arena{} = arena, term_id, renaming) do
    {arena, renamed} = rename_loose!(arena, term_id, renaming, 0)
    {:ok, arena, renamed}
  catch
    :unbound_loose -> :error
  end

  defp rename_loose!(arena, term_id, renaming, depth) do
    if Arena.has_loose_bvar?(arena, term_id, depth) do
      case Arena.get_node(arena, term_id) do
        {@tag_bvar, _, ty, idx, _} ->
          case Map.fetch(renaming, idx - depth) do
            {:ok, new_idx} -> Arena.mk_bvar(arena, new_idx + depth, ty)
            :error -> throw(:unbound_loose)
          end

        {tag, _, _, l, r} when tag in [@tag_app, @tag_eq, @tag_or] ->
          {arena, l2} = rename_loose!(arena, l, renaming, depth)
          {arena, r2} = rename_loose!(arena, r, renaming, depth)
          rebuild2(arena, tag, l2, r2)

        {@tag_not, _, _, a, _} ->
          {arena, a2} = rename_loose!(arena, a, renaming, depth)
          Arena.mk_not(arena, a2)

        {@tag_lam, _, _, dom, body} ->
          {arena, b2} = rename_loose!(arena, body, renaming, depth + 1)
          Arena.mk_lam(arena, dom, b2)

        {@tag_forall, _, _, dom, body} ->
          {arena, b2} = rename_loose!(arena, body, renaming, depth + 1)
          Arena.mk_forall(arena, dom, b2)
      end
    else
      {arena, term_id}
    end
  end

  defp rebuild2(arena, @tag_app, l, r), do: Arena.mk_app(arena, l, r)
  defp rebuild2(arena, @tag_eq, l, r), do: Arena.mk_eq(arena, l, r)
  defp rebuild2(arena, @tag_or, l, r), do: Arena.mk_or(arena, l, r)

  @doc """
  Instantiates `term_id` with `subst`, skipping the beta-eta pass when nothing can change.
  """
  @spec instantiate(Arena.t(), Arena.term_id(), Arena.subst()) :: {Arena.t(), Arena.term_id()}
  def instantiate(%Arena{} = arena, term_id, subst) do
    if map_size(subst) == 0 or not has_fvar?(arena, term_id) do
      {arena, term_id}
    else
      Arena.subst_fvar(arena, term_id, subst)
    end
  end
end
