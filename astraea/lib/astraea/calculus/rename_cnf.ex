defmodule Astraea.Calculus.RenameCnf do
  @moduledoc """
  Equisatisfiable clausification of a closed formula with structure-preserving
  formula renaming, after Leo-III's `RenameCNF` and `FormulaRenaming`
  (`leo.modules.calculus`), together with the extensionality expansions `BoolExt`
  and `FuncExt` that Leo-III's normalization mode applies exhaustively.

  Unlike `Astraea.Clausifier`, which serves the prover and may drop clauses
  (SInE, CNF size caps), nothing is approximated here: a formula whose clause set
  would exceed `:max_clauses` is an error. The steps are

    * negation normal form by polarity (`~`, `|`, `!`; `&` and `?` are encoded),
    * `A = B` at type `$o` expands to `(~A | B) & (A | ~B)` (negated:
      `(A | B) & (~A | ~B)`), Leo-III's `BoolExt`,
    * `f = g` at function type becomes `! [X]: f @ X = g @ X` (`FuncExt`),
    * universal quantifiers become clause variables, existential ones Skolem terms
      `Astraea.Arena.mk_skolem(phi, ty)` applied to the free variables of
      `phi = ! [x]: A` by id (the convention of `Astraea.ProofChecker` `:skolem`),
    * a positive disjunction `a | b` whose clause count `|a| * |b|` exceeds
      `|a| + |b| + threshold` (Leo-III's `FormulaRenaming.canApply`) is renamed: `b`
      is replaced by `def_<hash> @ Y` over its free variables `Y` and the clauses of
      `~(def_<hash> @ Y) | b` are added (Plaisted-Greenbaum, one direction only).

  Soundness: NNF, the Boolean and functional extensionality expansions and
  distribution are equivalences in extensional Henkin semantics. Skolemization and
  renaming preserve satisfiability: the output entails the input (Skolem terms are
  witnesses, `def @ Y => b` with `b` in positive position), and every model of the
  input extends to one of the output by interpreting `sk @ Y` as a witness of `phi`
  and `def @ Y` as `b`. Both kinds of symbols are content-addressed (`sk_` by
  `Astraea.Arena.skolem_hash/2`, `def_` by
  `Astraea.Calculus.ArgumentExtraction.definition_symbol/4`), so equal
  subformulas share them and the interpretations above are well defined, also
  across formulas.
  """

  alias Astraea.{Arena, ProofChecker}
  alias Astraea.Calculus.{ArgumentExtraction, Simplification}

  # Node tags (u8) matching `Astraea.Arena`
  @tag_const 1
  @tag_eq 6
  @tag_not 7
  @tag_or 8
  @tag_forall 9

  @default_max_clauses 10_000

  @doc """
  Clausifies the closed formula `term_id` (asserted, i.e. positive). Options:
    * `:renaming` - renaming threshold, or `false` to disable (default `0`, as
      Leo-III without `--renaming`)
    * `:extensionality` - expand Boolean and functional equations (default `true`)
    * `:max_clauses` - error instead of producing more clauses (default 10000)
    * `:next_fvar` - first clause variable id (default 1)
    * `:defined` - `{definition, polarity}` keys whose clauses were already
      produced (for sharing renamings across formulas; default empty)

  Returns `{:ok, arena, clauses, defined}` or `{:error, {:cnf_too_large, n}}`.
  """
  @spec clausify(Arena.t(), Arena.term_id(), keyword()) ::
          {:ok, Arena.t(), [ProofChecker.clause()], MapSet.t()} | {:error, term()}
  def clausify(%Arena{} = arena, term_id, opts \\ []) do
    st = %{
      arena: arena,
      next_fvar: Keyword.get(opts, :next_fvar, 1),
      threshold: Keyword.get(opts, :renaming, 0),
      ext: Keyword.get(opts, :extensionality, true),
      max: Keyword.get(opts, :max_clauses, @default_max_clauses),
      defined: Keyword.get(opts, :defined, MapSet.new()),
      def_clauses: [],
      sizes: %{}
    }

    {st, clauses} = cnf(st, term_id, :pos)
    {arena, clauses} = finalize(st.arena, clauses ++ Enum.reverse(st.def_clauses))
    {:ok, arena, clauses, st.defined}
  catch
    {:cnf_too_large, _n} = reason -> {:error, reason}
  end

  # ---------------------------------------------------------------------------
  # Clause sets: lists of literal lists; `[]` is true, `[[]]` is false.
  # ---------------------------------------------------------------------------

  defp cnf(st, raw, pol) do
    {arena, t} = Arena.beta_eta_norm(st.arena, raw)
    st = %{st | arena: arena}

    case Arena.get_node(arena, t) do
      {@tag_const, _, _, sym, _} ->
        case {Map.fetch!(arena.symbol_names, sym), pol} do
          {"$true", :pos} -> {st, []}
          {"$true", :neg} -> {st, [[]]}
          {"$false", :pos} -> {st, [[]]}
          {"$false", :neg} -> {st, []}
          _ -> {st, [[{pol, t}]]}
        end

      {@tag_not, _, _, a, _} ->
        cnf(st, a, flip(pol))

      {@tag_or, _, _, a, b} when pol == :pos ->
        disjunction(st, a, b)

      {@tag_or, _, _, a, b} ->
        {st, ca} = cnf(st, a, :neg)
        {st, cb} = cnf(st, b, :neg)
        {st, checked(st, ca ++ cb)}

      {@tag_forall, _, _, ty, body} when pol == :pos ->
        {arena, var} = Arena.mk_fvar(st.arena, st.next_fvar, ty)
        {arena, inst} = Arena.subst_bvar(arena, body, 0, var)
        cnf(%{st | arena: arena, next_fvar: st.next_fvar + 1}, inst, :pos)

      {@tag_forall, _, _, ty, body} ->
        {arena, witness} = skolem_term(st.arena, t, ty)
        {arena, inst} = Arena.subst_bvar(arena, body, 0, witness)
        cnf(%{st | arena: arena}, inst, :neg)

      {@tag_eq, _, _, l, r} ->
        equation(st, t, l, r, pol)

      _ ->
        {st, [[{pol, t}]]}
    end
  end

  defp equation(st, t, l, r, pol) do
    case Map.fetch!(st.arena.type_table, Arena.type_of(st.arena, l)) do
      :o when st.ext -> iff(st, l, r, pol)
      {:arrow, dom, _cod} when st.ext -> cnf_ext(st, l, r, dom, pol)
      _ -> {st, [[{pol, t}]]}
    end
  end

  # `l <=> r` is `(~l | r) & (l | ~r)`, its negation `(l | r) & (~l | ~r)`.
  defp iff(st, l, r, pol) do
    arena = st.arena
    {arena, nl} = Simplification.negate(arena, l)
    {arena, nr} = Simplification.negate(arena, r)

    {arena, c1, c2} =
      case pol do
        :pos ->
          {arena, c1} = Arena.mk_or(arena, nl, r)
          {arena, c2} = Arena.mk_or(arena, l, nr)
          {arena, c1, c2}

        :neg ->
          {arena, c1} = Arena.mk_or(arena, l, r)
          {arena, c2} = Arena.mk_or(arena, nl, nr)
          {arena, c1, c2}
      end

    {st, k1} = cnf(%{st | arena: arena}, c1, :pos)
    {st, k2} = cnf(st, c2, :pos)
    {st, checked(st, k1 ++ k2)}
  end

  # `f = g` is `! [X]: f @ X = g @ X`.
  defp cnf_ext(st, l, r, dom, pol) do
    arena = st.arena
    {arena, ls} = Arena.shift(arena, l, 1, 0)
    {arena, rs} = Arena.shift(arena, r, 1, 0)
    {arena, x} = Arena.mk_bvar(arena, 0, dom)
    {arena, lx} = Arena.mk_app(arena, ls, x)
    {arena, rx} = Arena.mk_app(arena, rs, x)
    {arena, eq} = Arena.mk_eq(arena, lx, rx)
    {arena, all} = Arena.mk_forall(arena, dom, eq)
    cnf(%{st | arena: arena}, all, pol)
  end

  defp disjunction(st, a, b) do
    {st, sa} = size(st, a, :pos)
    {st, sb} = size(st, b, :pos)

    if is_integer(st.threshold) and sa * sb > sa + sb + st.threshold do
      {st, lit} = rename(st, b)
      {st, ca} = cnf(st, a, :pos)
      {st, product(st, ca, [[lit]])}
    else
      {st, ca} = cnf(st, a, :pos)
      {st, cb} = cnf(st, b, :pos)
      {st, product(st, ca, cb)}
    end
  end

  # Replaces the positive subformula `b` by `def @ Y` and adds `~(def @ Y) | b`.
  defp rename(st, b) do
    vars = st.arena |> Arena.free_vars(b) |> Enum.sort()

    {nodes, arena} =
      Enum.map_reduce(vars, st.arena, fn {id, ty}, ar ->
        {ar, fv} = Arena.mk_fvar(ar, id, ty)
        {fv, ar}
      end)

    {arena, const, applied} = ArgumentExtraction.definition_symbol(arena, "def_", nodes, b)
    st = %{st | arena: arena}
    key = {const, :pos}

    if MapSet.member?(st.defined, key) do
      {st, {:pos, applied}}
    else
      st = %{st | defined: MapSet.put(st.defined, key)}
      {st, cb} = cnf(st, b, :pos)
      def_clauses = Enum.map(cb, &[{:neg, applied} | &1])
      {%{st | def_clauses: Enum.reverse(def_clauses, st.def_clauses)}, {:pos, applied}}
    end
  end

  defp skolem_term(arena, phi, var_ty) do
    vars = arena |> Arena.free_vars(phi) |> Enum.sort()

    {arena, sk_ty} =
      vars
      |> Enum.reverse()
      |> Enum.reduce({arena, var_ty}, fn {_id, ty}, {ar, acc} ->
        Arena.intern_type(ar, {:arrow, ty, acc})
      end)

    {arena, sk} = Arena.mk_skolem(arena, phi, sk_ty)

    Enum.reduce(vars, {arena, sk}, fn {id, ty}, {ar, acc} ->
      {ar, fv} = Arena.mk_fvar(ar, id, ty)
      Arena.mk_app(ar, acc, fv)
    end)
  end

  # The size is checked before the product is built.
  defp product(st, left, right) do
    check_size(st, length(left) * length(right))
    for c1 <- left, c2 <- right, do: c1 ++ c2
  end

  defp checked(st, clauses) do
    check_size(st, length(clauses))
    clauses
  end

  defp check_size(st, n), do: if(n > st.max, do: throw({:cnf_too_large, n}))

  # Number of clauses of the CNF of `t` at polarity `pol` (Leo-III's
  # `FormulaRenaming.size`, extended by the Boolean equation expansion).
  defp size(st, t, pol) do
    case Map.fetch(st.sizes, {t, pol}) do
      {:ok, n} ->
        {st, n}

      :error ->
        {st, n} = size_uncached(st, t, pol)
        {%{st | sizes: Map.put(st.sizes, {t, pol}, n)}, n}
    end
  end

  defp size_uncached(st, t, pol) do
    case Arena.get_node(st.arena, t) do
      {@tag_not, _, _, a, _} ->
        size(st, a, flip(pol))

      {@tag_or, _, _, a, b} ->
        {st, sa} = size(st, a, pol)
        {st, sb} = size(st, b, pol)
        {st, if(pol == :pos, do: sa * sb, else: sa + sb)}

      {@tag_forall, _, _, _ty, body} ->
        size(st, body, pol)

      {@tag_eq, _, _, l, r} ->
        if st.ext and Arena.type_of(st.arena, l) == Arena.ty_o() do
          {st, pl} = size(st, l, :pos)
          {st, nl} = size(st, l, :neg)
          {st, pr} = size(st, r, :pos)
          {st, nr} = size(st, r, :neg)
          {st, if(pol == :pos, do: nl * pr + pl * nr, else: pl * pr + nl * nr)}
        else
          {st, 1}
        end

      _ ->
        {st, 1}
    end
  end

  # Clause sets as `ProofChecker.clause()`, without tautologies and false literals
  # `~(s = s)`.
  defp finalize(arena, clauses) do
    {arena, out} =
      Enum.reduce(clauses, {arena, []}, fn lits, {ar, acc} ->
        set = MapSet.new(lits)

        taut =
          Enum.any?(set, fn
            {:pos, a} -> MapSet.member?(set, {:neg, a}) or reflexive?(ar, a)
            {:neg, _} -> false
          end)

        if taut do
          {ar, acc}
        else
          {ar, [MapSet.reject(set, fn {pol, a} -> pol == :neg and reflexive?(ar, a) end) | acc]}
        end
      end)

    {arena, out |> Enum.reverse() |> Enum.uniq()}
  end

  defp reflexive?(arena, a), do: match?({@tag_eq, _, _, s, s}, Arena.get_node(arena, a))

  defp flip(:pos), do: :neg
  defp flip(:neg), do: :pos
end
