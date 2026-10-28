defmodule Astraea.Calculus.Cpo do
  @moduledoc """
  Computability path ordering (core CPO of Blanqui, Jouannaud and Rubio) as
  implemented by Leo-III's `TO_CPO_Naive`, the term ordering of most Leo-III
  strategies. `compare/4` returns `:gt | :lt | :eq | :inc` like
  `Astraea.Arena.kbo_compare/3`.

  Terms are compared in Leo-III's spine view. The logical connectives of the arena
  are read as applications of Leo-III's fixed symbols: `~ a` as `~(a)`, `a | b` as
  `|(a, b)`, `a = b` as `=(a, b)` and `! [X: t]: p` as `!(^ [X: t]: p)`. Symbols are
  compared by a precedence (`t:precedence/0`, Leo-III's `Precedence.arity` by
  default). A symbol compared with itself uses its status: multiset for the fixed
  symbols, lexicographic for declared symbols and Skolem constants (Leo-III's
  `HOLSignature` and `addUninterpreted` defaults). Base types are ordered by their
  arena id (`$o < $i <` declared types, as Leo-III orders type keys).

  Binders are opened by instantiating the bound variable with a reserved free
  variable instead of tracking de Bruijn depths. A binder of the right-hand term
  that CPO opens with a fresh *small* variable (the set `X` of the paper, Leo-III's
  indices `<= depth`) gets a variable that every non-variable term dominates; all
  other opened binders get ordinary fresh variables. Every comparison therefore
  works on terms without loose bound variables, so the subterm test is a plain
  occurrence test. Inputs are expected to be closed with respect to bound variables
  (loose de Bruijn indices are treated like free variables). Leo-III does not lift
  the indices of the right-hand term when it descends into a binder of the left one.

  Deviations from `TO_CPO_Naive`, each found by the property tests
  (`test/astraea/calculus/cpo_test.exs`) as a violation of transitivity or of
  stability under substitution, and each closer to the CPO of the paper:

    * a head comparison that fails by precedence falls through to the subterm
      cases instead of answering `false` (F-subterm rule),
    * the subterm cases (`f(t) > v if t_i >= v`, `@(s, t) > v if s >= v or
      t >= v`, `^ [x]: u > v if u >= v`) have no type condition, like the
      untyped occurrence test that already precedes them,
    * the F@ case `f(t) > @(u, v)` checks the type condition of `f(t) > u`,
    * the application cases 7 and 8 (`@(s, t)` on the left) apply only to terms
      whose head is not a symbol; Leo-III also treats the prefix `f(t1 .. tn-1)`
      of `f(t1 .. tn)` as an application subterm,
    * the lexicographic extension compares arguments up to the first difference
      also when the left term has more arguments (Leo-III's `alleq`).

  Stability holds for substitutions that create no beta-redex. On beta-normal
  forms no ordering is stable for every higher-order binding: `F x > x`, while
  `F := ^ [x]: a` turns both sides into `a`. Orientation of rewrite rules is a
  search heuristic here; the kernel does not depend on the ordering.

  As in Leo-III, `gt0` results are memoized for one call of `compare/4`; the
  rules re-examine the same pairs of subterms many times.
  """

  alias Astraea.Arena
  alias Astraea.Calculus.Terms

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

  # Leo-III `HOLSignature` keys of the fixed symbols (below every declared symbol).
  @key_true {0, 6}
  @key_false {0, 7}
  @key_not {0, 8}
  @key_forall {0, 9}
  @key_or {0, 10}
  @key_eq {0, 11}

  # Free-variable ids from here on are reserved for opened binders.
  @marker_base 0xC000_0000

  @typedoc "A symbol as seen by the precedence: its key and the arity of its type."
  @type symbol :: {key :: tuple(), arity :: non_neg_integer()}

  @typedoc """
  `:arity` (Leo-III's default `Precedence.arity`: higher arity first, then later
  declaration), `:inv_arity`, `:arity_unary_first`, `:sig_induced` (declaration
  order only), or a function comparing two `t:symbol/0`.
  """
  @type precedence ::
          :arity
          | :inv_arity
          | :arity_unary_first
          | :sig_induced
          | (symbol(), symbol() -> :gt | :lt | :eq | :inc)

  @doc "Leo-III's default precedence (`Configuration.PRECEDENCE`)."
  @spec precedence() :: precedence()
  def precedence, do: :arity

  @doc """
  Compares `s` and `t` by CPO: `:gt` if `s > t`, `:lt` if `t > s`, `:eq` if they
  are identical and `:inc` otherwise.
  """
  @spec compare(Arena.t(), Arena.term_id(), Arena.term_id(), precedence()) ::
          :gt | :lt | :eq | :inc
  def compare(arena, s, t, precedence \\ :arity)
  def compare(%Arena{}, s, s, _precedence), do: :eq

  def compare(%Arena{} = arena, s, t, precedence) do
    st = %{
      arena: arena,
      prec: precedence,
      memo: %{},
      reserved: %{},
      opened: %{},
      small: MapSet.new(),
      next_marker: @marker_base
    }

    case gt(st, s, t) do
      {_st, true} ->
        :gt

      {st, false} ->
        case gt(st, t, s) do
          {_st, true} -> :lt
          {_st, false} -> :inc
        end
    end
  end

  @doc "Returns true iff `s > t` in CPO."
  @spec greater?(Arena.t(), Arena.term_id(), Arena.term_id(), precedence()) :: boolean()
  def greater?(%Arena{} = arena, s, t, precedence \\ :arity),
    do: compare(arena, s, t, precedence) == :gt

  # ---------------------------------------------------------------------------
  # Type ordering (Leo-III `gt0(Type, Type)` / `ge0(Type, Type)`)
  # ---------------------------------------------------------------------------

  defp ty_gt(_arena, a, a), do: false

  defp ty_gt(arena, a, b) do
    case {ty_node(arena, a), ty_node(arena, b)} do
      {:base, :base} -> a > b
      {:base, {:arrow, bi, bo}} -> ty_gt(arena, a, bi) and ty_gt(arena, a, bo)
      {{:arrow, ai, ao}, {:arrow, ai, bo}} -> ty_ge(arena, ao, b) or ty_gt(arena, ao, bo)
      {{:arrow, _ai, ao}, _} -> ty_ge(arena, ao, b)
    end
  end

  defp ty_ge(_arena, a, a), do: true

  defp ty_ge(arena, a, b) do
    case {ty_node(arena, a), ty_node(arena, b)} do
      {:base, :base} -> a > b
      {:base, {:arrow, bi, bo}} -> ty_gt(arena, a, bi) and ty_gt(arena, a, bo)
      {{:arrow, ai, ao}, {:arrow, ai, bo}} -> ty_ge(arena, ao, b) or ty_ge(arena, ao, bo)
      {{:arrow, _ai, ao}, _} -> ty_ge(arena, ao, b)
    end
  end

  defp ty_node(arena, ty) do
    case Map.fetch!(arena.type_table, ty) do
      {:arrow, dom, cod} -> {:arrow, dom, cod}
      _ -> :base
    end
  end

  # ---------------------------------------------------------------------------
  # Term ordering (Leo-III `gt`, `gteq`, `gt0`)
  # ---------------------------------------------------------------------------

  # `gt` and `gteq` check the type condition; `gt0` and `ge0` do not.
  defp gt(st, s, t) do
    if ty_ge(st.arena, Arena.type_of(st.arena, s), Arena.type_of(st.arena, t)),
      do: gt0(st, s, t),
      else: {st, false}
  end

  defp ge(st, s, t) do
    if ty_ge(st.arena, Arena.type_of(st.arena, s), Arena.type_of(st.arena, t)),
      do: ge0(st, s, t),
      else: {st, false}
  end

  defp ge0(st, s, s), do: {st, true}
  defp ge0(st, s, t), do: gt0(st, s, t)

  defp gt0(st, s, s), do: {st, false}

  defp gt0(st, s, t) do
    case Map.fetch(st.memo, {s, t}) do
      {:ok, known} ->
        {st, known}

      :error ->
        {st, result} = gt0_impl(st, s, t)
        {%{st | memo: Map.put(st.memo, {s, t}, result)}, result}
    end
  end

  defp gt0_impl(st, s, t) do
    {st, vs} = classify(st, s)

    cond do
      match?({:var, _}, vs) ->
        {st, false}

      occurs?(st.arena, s, t) ->
        {st, true}

      true ->
        {st, vt} = classify(st, t)

        case vs do
          {:lam, dom, _body} -> gt_lam(st, s, dom, t, vt)
          {:sym, f} -> gt_sym(st, s, f, t, vt)
          {:app, fh, f, fargs} -> gt_app(st, s, fh, f, fargs, t, vt)
        end
    end
  end

  # All lambda rules (\>, \=, \!=, \X) without eta.
  defp gt_lam(st, s, dom, t, vt) do
    {st, s_body} = open(st, :left, s)

    either(st, [
      &ge0(&1, s_body, t),
      fn st ->
        case vt do
          {:lam, ^dom, _} ->
            {st, s_body, t_body} = open_pair(st, s, t)
            gt0(st, s_body, t_body)

          {:lam, _other, _} ->
            {st, t_body} = open(st, :right, t)
            gt0(st, s, t_body)

          {:var, _} ->
            {st, small?(st, t)}

          _ ->
            {st, false}
        end
      end
    ])
  end

  # `s` is a symbol without arguments.
  defp gt_sym(st, s, f, t, vt) do
    case vt do
      {:var, _} ->
        {st, small?(st, t)}

      {:lam, _dom, _body} ->
        # case 5: f > ^ [y]: v if f > v with y small
        {st, t_body} = open(st, :small, t)
        gt0(st, s, t_body)

      {:sym, g} ->
        {st, prec(st, f, g) == :gt}

      {:app, gh, g, gargs} ->
        by_head =
          case g && prec(st, f, g) do
            nil -> :cont
            :eq -> :cont
            :gt -> :all_args
            _ -> :fail
          end

        case by_head do
          :fail ->
            {st, false}

          _ ->
            either(st, [
              fn st ->
                if by_head == :all_args, do: every(st, gargs, &gt0(&1, s, &2)), else: {st, false}
              end,
              fn st ->
                {st, t_prefix} = prefix(st, gh, gargs)
                both(st, &gt(&1, s, t_prefix), &gt0(&1, s, List.last(gargs)))
              end
            ])
        end
    end
  end

  # `s` is an application `f @ fargs` (`fargs` non-empty).
  defp gt_app(st, s, fh, f, fargs, t, vt) do
    if match?({:var, _}, vt) and small?(st, t) do
      # cases 6 and 10: f(t) > y, @(s, t) > y for small y
      {st, true}
    else
      case app_vs(st, s, fh, f, fargs, t, vt) do
        {st, :cont} ->
          {st, s_prefix} = prefix(st, fh, fargs)

          if f do
            # case 1: f(t) > v if some t_i >= v
            some(st, fargs, &ge0(&1, &2, t))
          else
            # case 7: @(s, t) > v if s >= v or t >= v
            either(st, [&ge0(&1, s_prefix, t), &ge0(&1, List.last(fargs), t)])
          end

        decided ->
          decided
      end
    end
  end

  # The cases of `gt_app` that depend on the shape of `t`: `{st, boolean}` decides,
  # `{st, :cont}` falls through to the subterm cases.
  defp app_vs(st, s, _fh, f, _fargs, t, {:lam, _dom, _body}) do
    either(st, [
      # case 5: f(t) > ^ [y]: v if f(t) > v with y small
      fn st ->
        if f do
          {st, t_body} = open(st, :small, t)
          gt0(st, s, t_body)
        else
          {st, false}
        end
      end,
      # case 9: @(s, t) > ^ [y]: v if @(s, t) > v
      fn st ->
        {st, t_body} = open(st, :right, t)
        gt0(st, s, t_body)
      end
    ])
    |> continue_unless_true()
  end

  # Leo-III returns the precedence verdict in the next two clauses; here a failed
  # head comparison falls through to the subterm cases (CPO's F-subterm rule), which
  # is needed for stability under substitution: `f(F a) > F b` holds by the
  # subterm `F a > F b`, so `f(g a a) > g a b` must hold as well.
  defp app_vs(st, _s, _fh, f, _fargs, _t, {:sym, g}) do
    if f && prec(st, f, g) in [:gt, :eq], do: {st, true}, else: {st, :cont}
  end

  defp app_vs(st, s, fh, f, fargs, _t, {:app, gh, g, gargs}) do
    if f && g do
      # cases 2 and 3: f(t) > g(u)
      case prec(st, f, g) do
        :eq -> status(st, s, f, fargs, gargs)
        :gt -> every(st, gargs, &gt0(&1, s, &2))
        _ -> {st, false}
      end
      |> continue_unless_true()
    else
      {st, t_prefix} = prefix(st, gh, gargs)
      {st, s_prefix} = prefix(st, fh, fargs)
      t_last = List.last(gargs)
      s_last = List.last(fargs)

      if f do
        # case 4: f(t) > @(u, v), with the type condition on f(t) > u
        both(st, &gt(&1, s, t_prefix), &gt0(&1, s, t_last))
      else
        # case 8: @(s, t) > @(u, v), only for application heads (see the moduledoc)
        either(st, [
          fn st -> if s_prefix == t_prefix, do: gt0(st, s_last, t_last), else: {st, false} end,
          fn st ->
            both(st, &app_dominates(&1, s, s_prefix, s_last, t_prefix), fn st ->
              app_dominates(st, s, s_prefix, s_last, t_last)
            end)
          end
        ])
      end
      |> continue_unless_true()
    end
  end

  defp app_vs(st, _s, _fh, _f, _fargs, _t, {:var, _}), do: {st, :cont}

  # One half of case 8: `w` is dominated by the prefix or last argument of `s`, or
  # by `s` itself.
  defp app_dominates(st, s, s_prefix, s_last, w) do
    either(st, [&gt(&1, s_prefix, w), &ge(&1, s_last, w), &gt(&1, s, w)])
  end

  defp continue_unless_true({st, true}), do: {st, true}
  defp continue_unless_true({st, false}), do: {st, :cont}

  # Equal heads (Leo-III `gt0Stat`): the fixed symbols have multiset status, declared
  # symbols and Skolem constants lexicographic status.
  defp status(st, _s, {{0, _}, _}, ss, ts), do: mult(st, ss, ts)
  defp status(st, s, _f, ss, ts), do: lex(st, s, ss, ts)

  # Lexicographic extension (Leo-III `gt0Lex`): the first differing arguments decide,
  # and `s` must dominate the remaining arguments of `t`. If `s` has more arguments
  # and the arguments of `t` are a prefix, `s > t`. (Leo-III's `alleq` also answers
  # `false` when `s` has more arguments and the first difference is decreasing,
  # which breaks transitivity: `g (f a) a > g a a > h (g a)` but not
  # `g (f a) a > g a`.)
  defp lex(st, s, [x | ss], [x | ts]), do: lex(st, s, ss, ts)
  defp lex(st, _s, [_ | _], []), do: {st, true}

  defp lex(st, s, [x | _], [y | ts]),
    do: both(st, &gt(&1, x, y), &every(&1, ts, fn st, t -> gt0(st, s, t) end))

  defp lex(st, _s, _ss, _ts), do: {st, false}

  # Multiset extension (Leo-III `gt0Mult`).
  defp mult(st, [_ | _], []), do: {st, true}

  defp mult(st, [_ | _] = ss, [_ | _] = ts) do
    same = ss -- (ss -- ts)

    case {ss -- same, ts -- same} do
      {[], []} -> {st, false}
      {rest_s, rest_t} -> mult0(st, rest_s, rest_t)
    end
  end

  defp mult(st, _ss, _ts), do: {st, false}

  defp mult0(st, _ss, []), do: {st, true}
  defp mult0(st, [], _ts), do: {st, false}

  defp mult0(st, [sn | rest], ts) do
    {st, keep} =
      Enum.reduce(ts, {st, []}, fn tn, {st, keep} ->
        case gt(st, sn, tn) do
          {st, true} -> {st, keep}
          {st, false} -> {st, [tn | keep]}
        end
      end)

    mult0(st, rest, Enum.reverse(keep))
  end

  # ---------------------------------------------------------------------------
  # Precedence (Leo-III `Precedences`)
  # ---------------------------------------------------------------------------

  defp prec(%{prec: fun}, f, g) when is_function(fun, 2), do: fun.(f, g)
  defp prec(%{prec: :sig_induced}, {kf, _}, {kg, _}), do: cmp(kf, kg)
  defp prec(%{prec: :arity}, {kf, a}, {kg, a}), do: cmp(kf, kg)
  defp prec(%{prec: :arity}, {_, af}, {_, ag}), do: cmp(af, ag)
  defp prec(%{prec: :inv_arity}, {kf, a}, {kg, a}), do: cmp(kf, kg)
  defp prec(%{prec: :inv_arity}, {_, af}, {_, ag}), do: cmp(ag, af)
  defp prec(%{prec: :arity_unary_first}, {kf, a}, {kg, a}), do: cmp(kf, kg)
  defp prec(%{prec: :arity_unary_first}, {_, 1}, _g), do: :gt
  defp prec(%{prec: :arity_unary_first}, _f, {_, 1}), do: :lt
  defp prec(%{prec: :arity_unary_first}, {_, af}, {_, ag}), do: cmp(af, ag)

  defp cmp(x, x), do: :eq
  defp cmp(x, y) when x > y, do: :gt
  defp cmp(_x, _y), do: :lt

  # ---------------------------------------------------------------------------
  # Spine view
  # ---------------------------------------------------------------------------

  # `{:var, id}`, `{:lam, dom, body}`, `{:sym, symbol}` (a symbol without
  # arguments) or `{:app, head, symbol | nil, args}` (`nil` for variable heads).
  defp classify(st, t) do
    case Arena.get_node(st.arena, t) do
      {tag, _, _, _, _} when tag in [@tag_fvar, @tag_bvar] ->
        {st, {:var, t}}

      {@tag_lam, _, _, dom, body} ->
        {st, {:lam, dom, body}}

      {@tag_eq, _, _, l, r} ->
        ty = Arena.type_of(st.arena, l)
        {st, head} = reserved(st, {:eq, ty}, {:arrow, ty, {:arrow, ty, :o}}, {@key_eq, 0})
        {st, {:app, head, {@key_eq, 0}, [l, r]}}

      {@tag_or, _, _, l, r} ->
        {st, head} = reserved(st, :or, {:arrow, :o, {:arrow, :o, :o}}, {@key_or, 2})
        {st, {:app, head, {@key_or, 2}, [l, r]}}

      {@tag_not, _, _, a, _} ->
        {st, head} = reserved(st, :not, {:arrow, :o, :o}, {@key_not, 1})
        {st, {:app, head, {@key_not, 1}, [a]}}

      {@tag_forall, _, _, dom, body} ->
        {arena, pred} = Arena.mk_lam(st.arena, dom, body)
        st = %{st | arena: arena}
        pred_ty = Arena.type_of(arena, pred)
        {st, head} = reserved(st, {:forall, dom}, {:arrow, pred_ty, :o}, {@key_forall, 0})
        {st, {:app, head, {@key_forall, 0}, [pred]}}

      {@tag_app, _, _, _, _} ->
        {head, args} = Terms.spine(st.arena, t)
        {st, {:app, head, symbol(st, head), args}}

      _ ->
        {st, {:sym, symbol(st, t)}}
    end
  end

  # The precedence view of a symbol node, `nil` for other heads.
  defp symbol(st, id) do
    case Map.fetch(st.reserved, id) do
      {:ok, sym} ->
        sym

      :error ->
        case Arena.get_node(st.arena, id) do
          {@tag_const, _, ty, sym, _} ->
            case Map.get(st.arena.symbol_names, sym) do
              "$true" -> {@key_true, 0}
              "$false" -> {@key_false, 0}
              _ -> {{1, sym}, arity(st.arena, ty)}
            end

          {@tag_skolem, _, ty, _, _} ->
            {{2, id}, arity(st.arena, ty)}

          {@tag_comb, _, ty, comb, _} ->
            {{0, 11 + comb}, arity(st.arena, ty)}

          _ ->
            nil
        end
    end
  end

  defp arity(arena, ty), do: length(elem(Terms.arrow_types(arena, ty), 0))

  # A constant standing for a connective, so that partial applications such as
  # `= a` (the prefix of `a = b`) are ordinary arena terms.
  defp reserved(st, which, ty, sym) do
    {arena, head} = Arena.mk_const(st.arena, "$$cpo_#{inspect(which)}", ty)
    {%{st | arena: arena, reserved: Map.put(st.reserved, head, sym)}, head}
  end

  # `head @ a1 @ ... @ a(n-1)` for the arguments `a1 ... an`.
  defp prefix(st, head, args) do
    {arena, p} = Terms.mk_apps(st.arena, head, Enum.drop(args, -1))
    {%{st | arena: arena}, p}
  end

  # ---------------------------------------------------------------------------
  # Opening binders
  # ---------------------------------------------------------------------------

  # The body of the abstraction (or `forall`) `lam`, its bound variable replaced by
  # a reserved free variable. `kind` is `:left` (binder of the left-hand term),
  # `:right` (binder of the right-hand term, ordinary variable) or `:small` (binder
  # of the right-hand term, variable in `X`). The same binder opened the same way
  # always gets the same variable, which keeps the memo effective; variables of
  # different kinds never meet on the same side of a comparison.
  defp open(st, kind, lam) do
    key = {kind, lam}

    case Map.fetch(st.opened, key) do
      {:ok, body} ->
        {st, body}

      :error ->
        {@tag_lam, _, _, dom, body} = Arena.get_node(st.arena, lam)
        {st, marker} = fresh(st, dom, kind == :small)
        {arena, opened} = Arena.subst_bvar(st.arena, body, 0, marker)
        {%{st | arena: arena, opened: Map.put(st.opened, key, opened)}, opened}
    end
  end

  # Both bodies of `^ [x]: u` and `^ [x]: v` with the same fresh variable for `x`.
  defp open_pair(st, s, t) do
    key = {:pair, s, t}

    case Map.fetch(st.opened, key) do
      {:ok, {s_body, t_body}} ->
        {st, s_body, t_body}

      :error ->
        {@tag_lam, _, _, dom, s_raw} = Arena.get_node(st.arena, s)
        {@tag_lam, _, _, _, t_raw} = Arena.get_node(st.arena, t)
        {st, marker} = fresh(st, dom, false)
        {arena, s_body} = Arena.subst_bvar(st.arena, s_raw, 0, marker)
        {arena, t_body} = Arena.subst_bvar(arena, t_raw, 0, marker)
        opened = Map.put(st.opened, key, {s_body, t_body})
        {%{st | arena: arena, opened: opened}, s_body, t_body}
    end
  end

  defp fresh(st, dom, small?) do
    {arena, marker} = Arena.mk_fvar(st.arena, st.next_marker, dom)
    small = if small?, do: MapSet.put(st.small, marker), else: st.small
    {%{st | arena: arena, small: small, next_marker: st.next_marker + 1}, marker}
  end

  defp small?(st, t), do: MapSet.member?(st.small, t)

  # ---------------------------------------------------------------------------
  # Subterms
  # ---------------------------------------------------------------------------

  # `t` occurs in `s` at an argument position (Leo-III `feasibleOccurrences`; heads
  # and partial applications are not occurrences). Both terms have no loose bound
  # variables, so every occurrence below a binder is feasible.
  defp occurs?(_arena, s, s), do: true

  defp occurs?(arena, s, t) do
    case Arena.get_node(arena, s) do
      {@tag_app, _, _, _, _} ->
        {_head, args} = Terms.spine(arena, s)
        Enum.any?(args, &occurs?(arena, &1, t))

      {tag, _, _, l, r} when tag in [@tag_eq, @tag_or] ->
        occurs?(arena, l, t) or occurs?(arena, r, t)

      {@tag_not, _, _, a, _} ->
        occurs?(arena, a, t)

      {@tag_forall, _, _, dom, body} ->
        match?({@tag_lam, _, _, ^dom, ^body}, Arena.get_node(arena, t)) or
          occurs?(arena, body, t)

      {@tag_lam, _, _, _, body} ->
        occurs?(arena, body, t)

      _ ->
        false
    end
  end

  # ---------------------------------------------------------------------------
  # Short-circuit combinators over `{state, boolean}`
  # ---------------------------------------------------------------------------

  defp either(st, []), do: {st, false}

  defp either(st, [alt | rest]) do
    case alt.(st) do
      {st, true} -> {st, true}
      {st, false} -> either(st, rest)
    end
  end

  defp both(st, first, second) do
    case first.(st) do
      {st, true} -> second.(st)
      no -> no
    end
  end

  defp every(st, list, fun) do
    Enum.reduce_while(list, {st, true}, fn x, {st, true} ->
      case fun.(st, x) do
        {st, true} -> {:cont, {st, true}}
        no -> {:halt, no}
      end
    end)
  end

  defp some(st, list, fun) do
    Enum.reduce_while(list, {st, false}, fn x, {st, false} ->
      case fun.(st, x) do
        {st, false} -> {:cont, {st, false}}
        yes -> {:halt, yes}
      end
    end)
  end
end
