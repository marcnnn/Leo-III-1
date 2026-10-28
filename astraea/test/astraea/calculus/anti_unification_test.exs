defmodule Astraea.Calculus.AntiUnificationTest do
  use ExUnit.Case, async: true
  use ExUnitProperties

  alias Astraea.Arena
  alias Astraea.Calculus.{AntiUnification, Terms}

  # a, b : $i   f : $i > $i > $i   g : $i > $i   u, k : $i > $i > $i
  # h : ($i > $i) > $i   p : $i > $o   X : $i, F : $i > $i (input free variables)
  defp signature do
    arena = Arena.new()
    {arena, ii} = Arena.intern_type(arena, {:arrow, :i, :i})
    {arena, iii} = Arena.intern_type(arena, {:arrow, :i, ii})
    {arena, ii_i} = Arena.intern_type(arena, {:arrow, ii, :i})
    {arena, io} = Arena.intern_type(arena, {:arrow, :i, :o})
    {arena, a} = Arena.mk_const(arena, "a", :i)
    {arena, b} = Arena.mk_const(arena, "b", :i)
    {arena, f} = Arena.mk_const(arena, "f", iii)
    {arena, g} = Arena.mk_const(arena, "g", ii)
    {arena, u} = Arena.mk_const(arena, "u", iii)
    {arena, k} = Arena.mk_const(arena, "k", iii)
    {arena, h} = Arena.mk_const(arena, "h", ii_i)
    {arena, p} = Arena.mk_const(arena, "p", io)
    {arena, x} = Arena.mk_fvar(arena, 1, :i)
    {arena, ff} = Arena.mk_fvar(arena, 2, ii)
    {arena, %{a: a, b: b, f: f, g: g, u: u, k: k, h: h, p: p, x: x, F: ff}}
  end

  defp app(arena, head, args), do: Terms.mk_apps(arena, head, args)

  # Checks `r sigma = s`, `r rho = t`, that both substitutions bind exactly the fresh
  # variables of `r`, and that `r` is a pattern (fresh variables applied to distinct
  # bound variables only).
  defp assert_generalizes(arena, s, t, next) do
    assert {:ok, arena, next2, {r, sigma, rho}} = AntiUnification.generalize(arena, s, t, next)
    assert Arena.type_of(arena, r) == Arena.type_of(arena, s)

    {arena, s2} = Arena.subst_fvar(arena, r, sigma)
    {arena, t2} = Arena.subst_fvar(arena, r, rho)
    assert s2 == s
    assert t2 == t

    fresh = for {id, _ty} <- Arena.free_vars(arena, r), id >= next, into: MapSet.new(), do: id
    assert MapSet.new(Map.keys(sigma)) == fresh
    assert MapSet.new(Map.keys(rho)) == fresh
    assert Enum.all?(fresh, &(&1 < next2))
    assert pattern?(arena, r, next)
    {arena, r, sigma, rho}
  end

  defp pattern?(arena, term, next) do
    case Terms.view(arena, term) do
      {:flex, head, args} ->
        if elem(Arena.get_node(arena, head), 3) >= next,
          do: Enum.all?(args, &Terms.bvar?(arena, &1)) and Enum.uniq(args) == args,
          else: Enum.all?(args, &pattern?(arena, &1, next))

      {:rigid, _head, args} ->
        Enum.all?(args, fn {arg, _} -> pattern?(arena, arg, next) end)

      {:lam, _dom, body} ->
        pattern?(arena, body, next)
    end
  end

  # ---------------------------------------------------------------------------
  # Textbook examples
  # ---------------------------------------------------------------------------

  test "first-order: f(a, g(a)) and f(b, g(b)) generalize to f(Y, g(Y))" do
    {arena, sig} = signature()
    {arena, ga} = app(arena, sig.g, [sig.a])
    {arena, gb} = app(arena, sig.g, [sig.b])
    {arena, s} = app(arena, sig.f, [sig.a, ga])
    {arena, t} = app(arena, sig.f, [sig.b, gb])

    {arena, r, sigma, rho} = assert_generalizes(arena, s, t, 10)
    assert sigma == %{10 => sig.a}
    assert rho == %{10 => sig.b}
    {arena, y} = Arena.mk_fvar(arena, 10, :i)
    {arena, gy} = app(arena, sig.g, [y])
    {arena, expected} = app(arena, sig.f, [y, gy])
    assert r == expected

    # the generalization matches both inputs with exactly these substitutions
    assert Arena.match_pattern(arena, r, s) == {:ok, sigma}
    assert Arena.match_pattern(arena, r, t) == {:ok, rho}
  end

  test "first-order: different disagreement pairs get different variables" do
    {arena, sig} = signature()
    {arena, s} = app(arena, sig.f, [sig.a, sig.b])
    {arena, t} = app(arena, sig.f, [sig.b, sig.a])
    {arena, faa} = app(arena, sig.f, [sig.a, sig.a])
    {arena, fbb} = app(arena, sig.f, [sig.b, sig.b])

    {arena, _r, sigma, rho} = assert_generalizes(arena, s, t, 10)
    assert sigma == %{10 => sig.a, 11 => sig.b}
    assert rho == %{10 => sig.b, 11 => sig.a}

    {arena, r, sigma, _rho} = assert_generalizes(arena, faa, fbb, 10)
    assert map_size(sigma) == 1
    {arena, y} = Arena.mk_fvar(arena, 10, :i)
    assert {_, ^r} = app(arena, sig.f, [y, y])
  end

  test "identical terms and input variables are kept" do
    {arena, sig} = signature()
    {arena, fxa} = app(arena, sig.f, [sig.x, sig.a])
    {arena, fxb} = app(arena, sig.f, [sig.x, sig.b])

    assert {:ok, _arena, 2, {^fxa, sigma, rho}} = AntiUnification.generalize(arena, fxa, fxa)
    assert sigma == %{} and rho == %{}

    # X is decomposed, not generalized; next_fvar defaults past X (id 1)
    {arena, r, sigma, _rho} = assert_generalizes(arena, fxa, fxb, 2)
    assert Map.keys(sigma) == [2]
    {arena, y} = Arena.mk_fvar(arena, 2, :i)
    assert {_, ^r} = app(arena, sig.f, [sig.x, y])
    assert {:ok, _, 3, {^r, _, _}} = AntiUnification.generalize(arena, fxa, fxb)

    assert AntiUnification.generalize(arena, sig.a, sig.g) == :error
  end

  # Baumgartner et al., Example 1: ^[x, y]: f(u(g(x), y), u(g(y), x)) and
  # ^[x, y]: f(k(y, g(x)), k(x, g(y))) generalize to ^[x, y]: f(Y(x, y), Y(y, x)).
  test "higher-order patterns: merge up to a permutation of bound variables" do
    {arena, sig} = signature()
    {arena, x} = Arena.mk_bvar(arena, 1, :i)
    {arena, y} = Arena.mk_bvar(arena, 0, :i)
    {arena, gx} = app(arena, sig.g, [x])
    {arena, gy} = app(arena, sig.g, [y])
    {arena, u1} = app(arena, sig.u, [gx, y])
    {arena, u2} = app(arena, sig.u, [gy, x])
    {arena, k1} = app(arena, sig.k, [y, gx])
    {arena, k2} = app(arena, sig.k, [x, gy])
    {arena, s_body} = app(arena, sig.f, [u1, u2])
    {arena, t_body} = app(arena, sig.f, [k1, k2])
    {arena, s} = Terms.mk_lams(arena, [Arena.ty_i(), Arena.ty_i()], s_body)
    {arena, t} = Terms.mk_lams(arena, [Arena.ty_i(), Arena.ty_i()], t_body)

    {arena, r, sigma, rho} = assert_generalizes(arena, s, t, 10)
    assert Map.keys(sigma) == [10]

    {arena, iii} = Arena.intern_type(arena, {:arrow, :i, {:arrow, :i, :i}})
    {arena, big_y} = Arena.mk_fvar(arena, 10, iii)
    {arena, yxy} = app(arena, big_y, [x, y])
    {arena, yyx} = app(arena, big_y, [y, x])
    {arena, body} = app(arena, sig.f, [yxy, yyx])
    {arena, expected} = Terms.mk_lams(arena, [Arena.ty_i(), Arena.ty_i()], body)
    assert r == expected

    # Y := ^[z1, z2]: u(g(z1), z2) (eta-short: ^[z1]: u(g(z1))) and
    # Y := ^[z1, z2]: k(z2, g(z1))
    {arena, gz1} = app(arena, sig.g, [x])
    {arena, sig_body} = app(arena, sig.u, [gz1, y])
    {arena, rho_body} = app(arena, sig.k, [y, gz1])
    {arena, sig_y} = Terms.mk_lams(arena, [Arena.ty_i(), Arena.ty_i()], sig_body)
    {arena, sig_y} = Arena.beta_eta_norm(arena, sig_y)
    {_arena, rho_y} = Terms.mk_lams(arena, [Arena.ty_i(), Arena.ty_i()], rho_body)
    assert sigma[10] == sig_y
    assert rho[10] == rho_y
  end

  test "bound variables: only those that occur are arguments; eta-short sides" do
    {arena, sig} = signature()
    {arena, x0} = Arena.mk_bvar(arena, 0, :i)
    # ! [x]: p(f(x, a))  and  ! [x]: p(f(x, b))  ~>  ! [x]: p(f(x, Y))
    {arena, fxa} = app(arena, sig.f, [x0, sig.a])
    {arena, fxb} = app(arena, sig.f, [x0, sig.b])
    {arena, pfxa} = app(arena, sig.p, [fxa])
    {arena, pfxb} = app(arena, sig.p, [fxb])
    {arena, s} = Arena.mk_forall(arena, :i, pfxa)
    {arena, t} = Arena.mk_forall(arena, :i, pfxb)
    {arena, _r, sigma, rho} = assert_generalizes(arena, s, t, 10)
    assert sigma == %{10 => sig.a} and rho == %{10 => sig.b}

    # h(g) and h(^[x]: f(x, x)): g is eta-expanded, Y := g resp. ^[z]: f(z, z)
    {arena, hg} = app(arena, sig.h, [sig.g])
    {arena, fxx} = app(arena, sig.f, [x0, x0])
    {arena, lam} = Arena.mk_lam(arena, :i, fxx)
    {arena, hfxx} = app(arena, sig.h, [lam])
    {arena, r, sigma, rho} = assert_generalizes(arena, hg, hfxx, 10)
    assert sigma == %{10 => sig.g} and rho == %{10 => lam}
    {arena, ii} = Arena.intern_type(arena, {:arrow, :i, :i})
    {arena, big_y} = Arena.mk_fvar(arena, 10, ii)
    assert {_, ^r} = app(arena, sig.h, [big_y])
  end

  # ---------------------------------------------------------------------------
  # Random terms
  # ---------------------------------------------------------------------------

  defp term_spec(leaves) do
    tree(member_of(leaves), fn child ->
      one_of([
        tuple({constant(:g), child}),
        tuple({constant(:f), child, child}),
        tuple({constant(:F), child}),
        tuple({constant(:h), child})
      ])
    end)
  end

  defp first_order_spec do
    tree(member_of([:a, :b, :x]), fn child ->
      one_of([tuple({constant(:g), child}), tuple({constant(:f), child, child})])
    end)
  end

  defp atom_spec do
    term = term_spec([:a, :b, :x, :bv])

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

  defp build(arena, _sig, :bv, [ty | _]), do: Arena.mk_bvar(arena, 0, ty)
  defp build(arena, sig, :bv, []), do: {arena, sig.a}
  defp build(arena, sig, leaf, _bound) when is_atom(leaf), do: {arena, Map.fetch!(sig, leaf)}

  defp build(arena, sig, {:f, l, r}, bound),
    do: build2(arena, bound, sig, l, r, &app(&1, sig.f, [&2, &3]))

  defp build(arena, sig, {:eq, l, r}, bound), do: build2(arena, bound, sig, l, r, &Arena.mk_eq/3)
  defp build(arena, sig, {:or, l, r}, bound), do: build2(arena, bound, sig, l, r, &Arena.mk_or/3)

  defp build(arena, sig, {:not, a}, bound) do
    {arena, ta} = build(arena, sig, a, bound)
    Arena.mk_not(arena, ta)
  end

  defp build(arena, sig, {:h, body}, bound) do
    {arena, tb} = build(arena, sig, body, [Arena.ty_i() | bound])
    {arena, lam} = Arena.mk_lam(arena, :i, tb)
    Arena.mk_app(arena, sig.h, lam)
  end

  defp build(arena, sig, {:all, body}, bound) do
    {arena, tb} = build(arena, sig, body, [Arena.ty_i() | bound])
    Arena.mk_forall(arena, :i, tb)
  end

  defp build(arena, sig, {head, arg}, bound) do
    {arena, t} = build(arena, sig, arg, bound)
    Arena.mk_app(arena, Map.fetch!(sig, head), t)
  end

  defp build2(arena, bound, sig, l, r, mk) do
    {arena, tl} = build(arena, sig, l, bound)
    {arena, tr} = build(arena, sig, r, bound)
    mk.(arena, tl, tr)
  end

  property "the generalization is a pattern whose two instances are the inputs" do
    check all(
            {s_spec, t_spec} <-
              one_of([
                {term_spec([:a, :b, :x, :bv]), term_spec([:a, :b, :x, :bv])},
                {atom_spec(), atom_spec()}
              ]),
            max_runs: 400
          ) do
      {arena, sig} = signature()
      {arena, s} = build(arena, sig, s_spec)
      {arena, t} = build(arena, sig, t_spec)
      assert_generalizes(arena, s, t, 10)
    end
  end

  property "first-order terms: matching the generalization recovers the substitutions" do
    check all(s_spec <- first_order_spec(), t_spec <- first_order_spec(), max_runs: 300) do
      {arena, sig} = signature()
      {arena, s} = build(arena, sig, s_spec)
      {arena, t} = build(arena, sig, t_spec)
      {arena, r, sigma, rho} = assert_generalizes(arena, s, t, 10)

      # input variables match themselves; fresh ones exactly as returned
      fixed = %{1 => sig.x}
      assert {:ok, ms} = Arena.match_pattern(arena, r, s)
      assert {:ok, mt} = Arena.match_pattern(arena, r, t)
      assert Map.drop(ms, [1]) == sigma and Map.take(ms, [1]) == Map.take(fixed, Map.keys(ms))
      assert Map.drop(mt, [1]) == rho

      # least general: distinct fresh variables stand for distinct disagreement pairs
      pairs = for id <- Map.keys(sigma), do: {sigma[id], rho[id]}
      assert length(Enum.uniq(pairs)) == length(pairs)
    end
  end
end
