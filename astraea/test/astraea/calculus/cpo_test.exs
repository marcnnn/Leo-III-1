defmodule Astraea.Calculus.CpoTest do
  use ExUnit.Case, async: true
  use ExUnitProperties

  alias Astraea.Arena
  alias Astraea.Calculus.{Cpo, Ordering, Terms}

  # ---------------------------------------------------------------------------
  # Random terms over a small higher-order signature (declaration order matters
  # for the default precedence: arity first, then later declaration):
  #   a, b : $i   f : $i > $i   g : $i > $i > $i   h : ($i > $i) > $i   p : $i > $o
  #   X, Y : $i   F : $i > $i   (free variables)
  # `{:h, body}` is `h (^ [x]: body)`, where `:bv` is the innermost bound variable.
  # ---------------------------------------------------------------------------

  defp signature do
    arena = Arena.new()
    {arena, ii} = Arena.intern_type(arena, {:arrow, :i, :i})
    {arena, iii} = Arena.intern_type(arena, {:arrow, :i, ii})
    {arena, ii_i} = Arena.intern_type(arena, {:arrow, ii, :i})
    {arena, io} = Arena.intern_type(arena, {:arrow, :i, :o})
    {arena, a} = Arena.mk_const(arena, "a", :i)
    {arena, b} = Arena.mk_const(arena, "b", :i)
    {arena, f} = Arena.mk_const(arena, "f", ii)
    {arena, g} = Arena.mk_const(arena, "g", iii)
    {arena, h} = Arena.mk_const(arena, "h", ii_i)
    {arena, p} = Arena.mk_const(arena, "p", io)
    {arena, x} = Arena.mk_fvar(arena, 1, :i)
    {arena, y} = Arena.mk_fvar(arena, 2, :i)
    {arena, ff} = Arena.mk_fvar(arena, 3, ii)
    {arena, %{a: a, b: b, f: f, g: g, h: h, p: p, x: x, y: y, F: ff, ii: ii}}
  end

  defp term_spec do
    tree(member_of([:a, :b, :x, :y, :bv]), fn child ->
      one_of([
        tuple({constant(:f), child}),
        tuple({constant(:g), child, child}),
        tuple({constant(:F), child}),
        tuple({constant(:h), child})
      ])
    end)
  end

  defp atom_spec do
    term = term_spec()

    tree(
      one_of([tuple({constant(:p), term}), tuple({constant(:eq), term, term})]),
      fn child ->
        one_of([
          tuple({constant(:not), child}),
          tuple({constant(:or), child, child}),
          tuple({constant(:all), child})
        ])
      end
    )
  end

  defp build(arena, sig, spec) do
    {arena, t} = build(arena, sig, spec, [])
    Arena.beta_eta_norm(arena, t)
  end

  # `bound` lists the types of the enclosing binders, innermost first.
  defp build(arena, _sig, :bv, [ty | _]), do: Arena.mk_bvar(arena, 0, ty)
  defp build(arena, sig, :bv, []), do: {arena, sig.a}
  defp build(arena, sig, leaf, _bound) when is_atom(leaf), do: {arena, Map.fetch!(sig, leaf)}

  defp build(arena, sig, {:g, l, r}, bound) do
    {arena, tl} = build(arena, sig, l, bound)
    {arena, tr} = build(arena, sig, r, bound)
    Terms.mk_apps(arena, sig.g, [tl, tr])
  end

  defp build(arena, sig, {:h, body}, bound) do
    {arena, tb} = build(arena, sig, body, [Arena.ty_i() | bound])
    {arena, lam} = Arena.mk_lam(arena, :i, tb)
    Arena.mk_app(arena, sig.h, lam)
  end

  defp build(arena, sig, {:eq, l, r}, bound) do
    {arena, tl} = build(arena, sig, l, bound)
    {arena, tr} = build(arena, sig, r, bound)
    Arena.mk_eq(arena, tl, tr)
  end

  defp build(arena, sig, {:not, a}, bound) do
    {arena, ta} = build(arena, sig, a, bound)
    Arena.mk_not(arena, ta)
  end

  defp build(arena, sig, {:or, l, r}, bound) do
    {arena, tl} = build(arena, sig, l, bound)
    {arena, tr} = build(arena, sig, r, bound)
    Arena.mk_or(arena, tl, tr)
  end

  defp build(arena, sig, {:all, body}, bound) do
    {arena, tb} = build(arena, sig, body, [Arena.ty_i() | bound])
    Arena.mk_forall(arena, :i, tb)
  end

  defp build(arena, sig, {head, arg}, bound) do
    {arena, t} = build(arena, sig, arg, bound)
    Arena.mk_app(arena, Map.fetch!(sig, head), t)
  end

  # Ground instances for X, Y (terms of type $i) and F (`:f` is `f`, `:ga` is `g a`).
  defp subst_spec do
    ground =
      tree(
        member_of([:a, :b]),
        &one_of([tuple({constant(:f), &1}), tuple({constant(:g), &1, &1})])
      )

    tuple({ground, ground, member_of([:f, :ga])})
  end

  defp build_subst(arena, sig, {x_spec, y_spec, f_spec}) do
    {arena, xt} = build(arena, sig, x_spec)
    {arena, yt} = build(arena, sig, y_spec)

    {arena, ft} =
      case f_spec do
        :f -> {arena, sig.f}
        :ga -> Arena.mk_app(arena, sig.g, sig.a)
      end

    {arena, %{1 => xt, 2 => yt, 3 => ft}}
  end

  # ---------------------------------------------------------------------------
  # Properties
  # ---------------------------------------------------------------------------

  property "identity is :eq and nothing else is" do
    check all(s_spec <- one_of([term_spec(), atom_spec()]), t_spec <- term_spec(), max_runs: 300) do
      {arena, sig} = signature()
      {arena, s} = build(arena, sig, s_spec)
      {arena, t} = build(arena, sig, t_spec)

      assert Cpo.compare(arena, s, s) == :eq
      assert Cpo.compare(arena, s, t) == :eq == (s == t)
    end
  end

  property "duality: s > t iff t < s (so never both s > t and t > s)" do
    check all(
            {s_spec, t_spec} <- one_of([{term_spec(), term_spec()}, {atom_spec(), atom_spec()}]),
            max_runs: 500
          ) do
      {arena, sig} = signature()
      {arena, s} = build(arena, sig, s_spec)
      {arena, t} = build(arena, sig, t_spec)

      st = Cpo.compare(arena, s, t)
      ts = Cpo.compare(arena, t, s)
      assert {st, ts} in [{:gt, :lt}, {:lt, :gt}, {:eq, :eq}, {:inc, :inc}]
    end
  end

  property "transitivity" do
    check all(
            specs <-
              one_of([
                list_of(term_spec(), length: 3),
                list_of(atom_spec(), length: 3)
              ]),
            max_runs: 500
          ) do
      {arena, sig} = signature()

      {arena, [s, t, u]} =
        Enum.reduce(specs, {arena, []}, fn spec, {ar, acc} ->
          {ar, x} = build(ar, sig, spec)
          {ar, acc ++ [x]}
        end)

      for {l, m, r} <- [{s, t, u}, {s, u, t}, {t, s, u}, {t, u, s}, {u, s, t}, {u, t, s}] do
        if Cpo.compare(arena, l, m) == :gt and Cpo.compare(arena, m, r) == :gt do
          assert Cpo.compare(arena, l, r) == :gt
        end
      end
    end
  end

  property "a term is greater than its closed argument subterms of the same type" do
    check all(spec <- one_of([term_spec(), atom_spec()]), max_runs: 300) do
      {arena, sig} = signature()
      {arena, s} = build(arena, sig, spec)
      ty = Arena.type_of(arena, s)

      for u <- arg_subterms(arena, s),
          u != s,
          Arena.type_of(arena, u) == ty,
          not Arena.has_loose_bvar?(arena, u, 0) do
        assert Cpo.compare(arena, s, u) == :gt
      end
    end
  end

  # CPO is stable under substitution; its theory does not cover beta-normalizing the
  # instance, so only bindings that create no beta-redex are tested (`F := f`,
  # `F := g a`). Abstractions are not: `F x > x` (application subterm), but
  # `F := ^ [x]: a` makes both sides `a` (KBO alike, see the unit test below), and
  # `F := ^ [x]: g x x` can reverse comparisons of partial applications.
  property "s > t is stable under substitution without beta-redexes" do
    check all(
            {s_spec, t_spec} <- one_of([{term_spec(), term_spec()}, {atom_spec(), atom_spec()}]),
            theta <- subst_spec(),
            max_runs: 500
          ) do
      {arena, sig} = signature()
      {arena, s} = build(arena, sig, s_spec)
      {arena, t} = build(arena, sig, t_spec)

      if Cpo.compare(arena, s, t) == :gt do
        {arena, subst} = build_subst(arena, sig, theta)
        {arena, s2} = Arena.subst_fvar(arena, s, subst)
        {arena, t2} = Arena.subst_fvar(arena, t, subst)
        assert Cpo.compare(arena, s2, t2) == :gt
      end
    end
  end

  # Subterms at argument positions (not heads, not partial applications).
  defp arg_subterms(arena, s) do
    children =
      case Arena.get_node(arena, s) do
        {4, _, _, _, _} -> elem(Terms.spine(arena, s), 1)
        {tag, _, _, l, r} when tag in [6, 8] -> [l, r]
        {7, _, _, a, _} -> [a]
        {tag, _, _, _, body} when tag in [5, 9] -> [body]
        _ -> []
      end

    [s | Enum.flat_map(children, &arg_subterms(arena, &1))]
  end

  # ---------------------------------------------------------------------------
  # Concrete comparisons (Leo-III `TO_CPO_Naive` with `Precedence.arity`)
  # ---------------------------------------------------------------------------

  defp app(arena, head, args), do: Terms.mk_apps(arena, head, args)

  test "precedence: higher arity first, then later declaration" do
    {arena, sig} = signature()
    {arena, fa} = app(arena, sig.f, [sig.a])
    {arena, gab} = app(arena, sig.g, [sig.a, sig.b])
    {arena, ffa} = app(arena, sig.f, [fa])

    # b was declared after a
    assert Cpo.compare(arena, sig.b, sig.a) == :gt
    # g (arity 2) > f (arity 1): g a b > f a, and even g a b > f (f a)
    assert Cpo.compare(arena, gab, fa) == :gt
    assert Cpo.compare(arena, gab, ffa) == :gt
    # same declared head: lexicographic status (g b a > g a b as b > a and g b a > b)
    {arena, gba} = app(arena, sig.g, [sig.b, sig.a])
    {arena, gbb} = app(arena, sig.g, [sig.b, sig.b])
    assert Cpo.compare(arena, gab, gba) == :lt
    assert Cpo.compare(arena, gbb, gab) == :gt
    # :sig_induced ignores arity: f was declared before g
    assert Cpo.compare(arena, fa, gab, :sig_induced) == :lt
    # :inv_arity puts constants first: b > f a, so g a b > f a by the subterm b
    assert Cpo.compare(arena, sig.b, fa, :inv_arity) == :gt
    assert Cpo.compare(arena, fa, gab, :inv_arity) == :lt
    assert Cpo.compare(arena, fa, sig.b, :inv_arity) == :lt
  end

  test "variables: subterm only, never greater than a non-variable" do
    {arena, sig} = signature()
    {arena, fx} = app(arena, sig.f, [sig.x])
    {arena, fy} = app(arena, sig.f, [sig.y])
    {arena, gxa} = app(arena, sig.g, [sig.x, sig.a])
    {arena, big_fa} = app(arena, sig[:F], [sig.a])

    assert Cpo.compare(arena, fx, sig.x) == :gt
    assert Cpo.compare(arena, fx, sig.y) == :inc
    assert Cpo.compare(arena, fx, fy) == :inc
    assert Cpo.compare(arena, gxa, fx) == :gt
    assert Cpo.compare(arena, sig.x, sig.a) == :inc
    # F a > a by the application subterm case, but not F a > b
    assert Cpo.compare(arena, big_fa, sig.a) == :gt
    assert Cpo.compare(arena, big_fa, sig.b) == :inc

    # F x > x, for KBO too; F := ^ [x]: a and x := a make both sides a
    {arena, big_fx} = app(arena, sig[:F], [sig.x])
    assert Cpo.compare(arena, big_fx, sig.x) == :gt
    assert Arena.kbo_compare(arena, big_fx, sig.x) == :gt
    {arena, ka} = Arena.mk_lam(arena, :i, sig.a)
    {_arena, inst} = Arena.subst_fvar(arena, big_fx, %{1 => sig.a, 3 => ka})
    assert inst == sig.a
  end

  test "binders: f(t) > ^ [y]: v opens y as a small variable; abstractions compare by body" do
    {arena, sig} = signature()
    {arena, x0} = Arena.mk_bvar(arena, 0, :i)
    {arena, gx0x0} = app(arena, sig.g, [x0, x0])
    {arena, lam_gxx} = Arena.mk_lam(arena, :i, gx0x0)
    {arena, h_gxx} = Arena.mk_app(arena, sig.h, lam_gxx)
    {arena, fa} = app(arena, sig.f, [sig.a])
    {arena, lam_fa} = Arena.mk_lam(arena, :i, fa)
    {arena, h_kfa} = Arena.mk_app(arena, sig.h, lam_fa)
    {arena, h_f} = Arena.mk_app(arena, sig.h, sig.f)
    {arena, ka} = Arena.mk_lam(arena, :i, sig.a)
    {arena, h_ka} = Arena.mk_app(arena, sig.h, ka)
    {arena, gb} = app(arena, sig.g, [sig.b])
    {arena, gx0a} = app(arena, sig.g, [x0, sig.a])
    {arena, lam_gxa} = Arena.mk_lam(arena, :i, gx0a)

    # same head h, multiset of {^ [x]: g x x} vs {^ [x]: f a}: g z z > f a (rule \=)
    assert Cpo.compare(arena, h_gxx, h_kfa) == :gt
    # f > ^ [x]: a (case 5: f > a as f has the higher arity), hence h f > h (^ [x]: a)
    assert Cpo.compare(arena, sig.f, ka) == :gt
    assert Cpo.compare(arena, h_f, h_ka) == :gt
    # ^ [x]: g x x > a since g z z > a (rule \>, the bound variable is fresh)
    assert Cpo.compare(arena, lam_gxx, sig.a) == :gt
    # the subterm rules ignore types: ^ [x]: g x x > f as g z z > f (g > f)
    assert Cpo.compare(arena, lam_gxx, sig.f) == :gt
    # g b > ^ [x]: g x a: g b > g y a with y small, b > y and b > a
    assert Cpo.compare(arena, gb, lam_gxa) == :gt
  end

  test "connectives are Leo-III's fixed symbols, below every declared symbol" do
    {arena, sig} = signature()
    {arena, pa} = Arena.mk_app(arena, sig.p, sig.a)
    {arena, pb} = Arena.mk_app(arena, sig.p, sig.b)
    {arena, npa} = Arena.mk_not(arena, pa)
    {arena, eq_ab} = Arena.mk_eq(arena, sig.a, sig.b)
    {arena, or_ab} = Arena.mk_or(arena, pa, pb)
    {arena, all_px} = Arena.mk_bvar(arena, 0, :i)
    {arena, px} = Arena.mk_app(arena, sig.p, all_px)
    {arena, all_p} = Arena.mk_forall(arena, :i, px)

    # p and ~ both have arity 1, p is declared: p b > ~ (p a) as p b > p a
    assert Cpo.compare(arena, pb, npa) == :gt
    # ~ (p a) > p a by the subterm case
    assert Cpo.compare(arena, npa, pa) == :gt
    # | has arity 2: (p a | p b) > ~ (p a)
    assert Cpo.compare(arena, or_ab, npa) == :gt
    # = has arity 0 (polymorphic in Leo-III): p a > (a = b) as p > = and p a > a, b
    assert Cpo.compare(arena, pa, eq_ab) == :gt
    assert Cpo.compare(arena, eq_ab, or_ab) == :lt
    # fixed symbols have multiset status: a = b and b = a are incomparable
    {arena, eq_ba} = Arena.mk_eq(arena, sig.b, sig.a)
    assert Cpo.compare(arena, eq_ab, eq_ba) == :inc
    {arena, eq_bb} = Arena.mk_eq(arena, sig.b, sig.b)
    assert Cpo.compare(arena, eq_bb, eq_ab) == :gt
    # ! [x]: p x is !(^ [x]: p x) and ! has arity 0, so p > !; p a > ^ [x]: p x (case 5,
    # untyped as in Leo-III) holds as p a > p y with y small
    assert Cpo.compare(arena, pa, all_p) == :gt
  end

  test "Ordering dispatches on :term_ordering" do
    {arena, sig} = signature()
    {arena, gab} = app(arena, sig.g, [sig.a, sig.b])
    {arena, fb} = app(arena, sig.f, [sig.b])
    {arena, ffb} = app(arena, sig.f, [fb])
    {arena, fffb} = app(arena, sig.f, [ffb])

    # KBO: weight decides (f (f (f b)) is heavier); CPO: precedence g > f decides
    assert Ordering.compare_terms(arena, fffb, gab, :kbo) == :gt
    assert Ordering.compare_terms(arena, fffb, gab, :cpo) == :lt
    assert Ordering.compare_terms(arena, fffb, gab) == :gt
    assert Ordering.opts([]).term_ordering == :kbo
    cpo = Ordering.opts(term_ordering: :cpo, ordered: true)
    assert Ordering.compare_terms(arena, fffb, gab, cpo) == :lt

    {arena, p_fffb} = Arena.mk_app(arena, sig.p, fffb)
    {arena, p_gab} = Arena.mk_app(arena, sig.p, gab)
    lits = MapSet.new([{:pos, p_fffb}, {:pos, p_gab}])

    assert Ordering.compare(arena, {:pos, p_fffb}, {:pos, p_gab}) == :gt
    assert Ordering.compare(arena, {:pos, p_fffb}, {:pos, p_gab}, :cpo) == :lt

    assert Ordering.eligible(arena, lits, Ordering.opts(ordered: true)) ==
             MapSet.new([{:pos, p_fffb}])

    assert Ordering.eligible(arena, lits, cpo) == MapSet.new([{:pos, p_gab}])
  end
end
