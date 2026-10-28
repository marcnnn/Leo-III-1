defmodule Astraea.Input.Modal do
  @moduledoc """
  Semantic embedding of higher-order quantified (multi-)modal logic into HOL, as
  Leo-III does via `logic-embedding` [GSB17].

  Propositions become predicates over a sort of possible worlds `$$mworld`: every
  type is lifted by replacing `$o` with `$$mworld > $o`, connectives and
  quantifiers act pointwise, and `{$box(#i)} @ A` holds at `w` iff `A` holds at all
  `v` with `$$mrel#i @ w @ v` (`$$mrel` for the unindexed modality). Semantic
  parameters of the `logic` statement:

    * `$modalities`: a `$modal_system_X` or a list of `$modal_axiom_X`, turned into
      the corresponding frame conditions (T reflexive, B symmetric, D serial,
      4 transitive, 5 euclidean, CD functional, C4 dense, S5U universal);
    * `$domains`: `$constant` (plain quantifiers), or `$varying`, `$cumulative`,
      `$decreasing` (quantifiers over individual sorts are relativised to an
      existence predicate `$$mexists`, non-empty in every world, and monotone or
      anti-monotone along each accessibility relation);
    * `$designation`: only `$rigid` (constants keep their lifted type);
    * `$terms`: `$local`, or `$global` with constant domains (where it holds anyway).

  Following Leo-III, `axiom` and `definition` statements (and lemmas) are global,
  `hypothesis`, `assumption` and conjectures local to an actual world
  `$$mactual`; `-local`/`-global` subroles override this. Equality is rigid at
  types without `$o` and pointwise equivalence at `$o`. Equality at other types
  that contain `$o` is accepted only at the top of global statements, where its
  rigid and pointwise readings coincide. Such equality elsewhere, quantification
  over non-individual types with non-constant domains, interpreted symbols other
  than `$true`/`$false`, and polymorphism are rejected.

  ## Embedding parameters

  `embed/4` takes the parameters of Leo-III's `--embedding-param` (the
  `ModalEmbedding` options of `logic-embedding` 2.2.3), validated by
  `parse_params/1`. Without parameters the output is the semantic embedding
  above. Model answers are disabled for modal input, so every variant only has
  to be sound for proofs: its axioms must hold in every model of the intended
  semantics (equivalent or weaker), never stronger.

    * `MODALITIES_SEMANTICAL` (default): frame conditions on `$$mrel`.
    * `MODALITIES_SYNTACTICAL`: the frame conditions are replaced by global axiom
      schemas over `Phi: $$mworld > $o` (T `[]P => P`, B `P => []<>P`,
      D `[]P => <>P`, 4 `[]P => [][]P`, 5 `<>P => []<>P`, CD `<>P => []P`,
      C4 `[][]P => []P`). Each schema is valid on every frame with the matching
      property, so it holds in every intended model; with standard semantics it
      is even equivalent (instantiate `Phi` with `$$mrel @ w`, `= v` or the
      constant true). S5U has no modal axiom schema; it falls back to the T and 5
      schemas (an equivalence relation), which is weaker. Takes precedence over
      `MODALITIES_SEMANTICAL`, as in Leo-III.
    * `DOMAINS_SEMANTICAL` (default): monotonicity axioms on `$$mexists`.
    * `DOMAINS_SYNTACTICAL`: cumulative domains get the converse Barcan formula
      `[](![X]: P @ X) => ![X]: [](P @ X)`, decreasing domains the Barcan formula
      `(![X]: [](P @ X)) => [](![X]: P @ X)`, per sort and modality, globally for
      every `P` and with the relativised quantifiers. CBF is valid on cumulative,
      BF on decreasing domains; instantiating `P` with `$$mexists` gives back
      the semantic condition. Varying and constant domains are unaffected.
      Takes precedence over `DOMAINS_SEMANTICAL`.
    * `ALLOW_EMPTY_DOMAINS`: drops the non-emptiness axioms of `$$mexists`. Fewer
      axioms are weaker. Constant domains keep Astraea's non-empty HOL sorts.
    * `NO_UNIVERSAL_S5`: S5U is axiomatised as an equivalence relation (T and 5)
      instead of the universal relation, which is weaker. Unlike Leo-III,
      `$modal_system_S5` is an equivalence relation already by default, so the
      parameter only affects `$modal_system_S5U`.
    * `MONOMORPHIC`, `POLYMORPHIC`: Leo-III's choice between per-sort and
      polymorphic existence predicates. Astraea is monomorphic (one
      `$$mexists` per sort); both are accepted without effect.
    * `FORCE_HIGHERORDER`: disables `logic-embedding`'s redirect of first-order
      modal problems to a TFF embedding. Astraea always embeds into HOL; accepted
      without effect.
    * `SILENT`: suppresses the library's diagnostics; accepted without effect.
  """

  alias Astraea.Input.IR
  alias Tptp.Node

  import IR, only: [reject!: 1]

  @o IR.o()
  @w {:base, "$$mworld"}
  @actual {:const, "$$mactual", [], {:base, "$$mworld"}}

  @systems %{
    "K" => [],
    "KB" => [:b],
    "K4" => [:four],
    "K5" => [:five],
    "K45" => [:four, :five],
    "KB5" => [:b, :five],
    "D" => [:d],
    "DB" => [:d, :b],
    "D4" => [:d, :four],
    "D5" => [:d, :five],
    "D45" => [:d, :four, :five],
    "M" => [:t],
    "T" => [:t],
    "B" => [:t, :b],
    "S4" => [:t, :four],
    "S5" => [:t, :five],
    "S5U" => [:universal]
  }

  @axioms %{
    "K" => [],
    "M" => [:t],
    "T" => [:t],
    "B" => [:b],
    "D" => [:d],
    "4" => [:four],
    "5" => [:five],
    "CD" => [:cd],
    "C4" => [:c4]
  }

  @local_roles ~w(hypothesis assumption conjecture negated_conjecture)

  @params ~w(monomorphic polymorphic modalities_semantical modalities_syntactical
             domains_semantical domains_syntactical force_higherorder
             allow_empty_domains silent no_universal_s5)a

  @typedoc "An embedding parameter, the lower-case form of Leo-III's name."
  @type param :: atom()

  @doc """
  Validates embedding parameters given as atoms or strings in any case (Leo-III
  spells them `MODALITIES_SYNTACTICAL`). Returns the normalised lower-case atoms
  without duplicates, or the first unknown name.
  """
  @spec parse_params([atom() | String.t()]) ::
          {:ok, [param()]} | {:error, {:unknown_embedding_param, String.t()}}
  def parse_params(params) do
    params
    |> Enum.reduce_while([], fn p, acc ->
      name = p |> to_string() |> String.downcase()

      case Enum.find(@params, &(Atom.to_string(&1) == name)) do
        nil -> {:halt, {:error, {:unknown_embedding_param, to_string(p)}}}
        atom -> {:cont, [atom | acc]}
      end
    end)
    |> case do
      {:error, _} = err -> err
      acc -> {:ok, acc |> Enum.reverse() |> Enum.uniq()}
    end
  end

  @doc "The accepted embedding parameter names, as Leo-III spells them."
  @spec param_names() :: [String.t()]
  def param_names, do: Enum.map(@params, &(&1 |> Atom.to_string() |> String.upcase()))

  @typedoc "Parsed semantics: domain kind, frame conditions, global terms flag."
  @type spec :: %{domains: atom(), frame: [atom()], terms: :local | :global}

  @doc "Parses the formula of a `thf(_, logic, $modal == [...])` statement."
  @spec parse_spec(Node.t()) :: spec()
  def parse_spec(node) do
    {logic, entries} =
      case unwrap(node) do
        %Node{kind: :thf_definition, children: [name, value]} ->
          {Node.value(unwrap(name)), tuple_entries(value)}

        _ ->
          reject!("unsupported logic specification")
      end

    unless logic in ["$modal", "$alethic_modal"], do: reject!("unsupported logic #{logic}")

    params =
      Map.new(entries, fn entry ->
        case unwrap(entry) do
          %Node{kind: :thf_definition, children: [k, v]} -> {Node.value(unwrap(k)), unwrap(v)}
          _ -> reject!("unsupported logic parameter")
        end
      end)

    known = ~w($domains $quantification $designation $constants $terms $modalities)
    for {k, _} <- params, k not in known, do: reject!("unsupported logic parameter #{k}")

    domains = word(params["$domains"] || params["$quantification"], "$domains")
    designation = word(params["$designation"] || params["$constants"], "$designation")
    terms = if params["$terms"], do: word(params["$terms"], "$terms"), else: "$local"

    unless domains in ~w($constant $varying $cumulative $decreasing),
      do: reject!("unsupported $domains #{domains}")

    if designation != "$rigid", do: reject!("unsupported $designation #{designation}")

    terms =
      case {terms, domains} do
        {"$local", _} -> :local
        {"$global", "$constant"} -> :global
        _ -> reject!("unsupported $terms #{terms} with #{domains} domains")
      end

    %{
      domains: domains |> String.trim_leading("$") |> String.to_atom(),
      frame: modalities(params["$modalities"]),
      terms: terms
    }
  end

  defp word(nil, key), do: reject!("logic specification without #{key}")

  defp word(%Node{kind: :defined_constant} = n, _key), do: Node.value(n)
  defp word(_node, key), do: reject!("unsupported value of #{key}")

  defp modalities(nil), do: reject!("logic specification without $modalities")

  defp modalities(%Node{kind: :defined_constant} = n) do
    case Node.value(n) do
      "$modal_system_" <> s -> Map.get(@systems, s) || reject!("unsupported modal system #{s}")
      "$modal_axiom_" <> a -> axiom!(a)
      other -> reject!("unsupported $modalities #{other}")
    end
  end

  defp modalities(%Node{kind: :thf_tuple} = n) do
    n
    |> tuple_entries()
    |> Enum.flat_map(fn e ->
      case unwrap(e) do
        %Node{kind: :defined_constant} = c ->
          case Node.value(c) do
            "$modal_axiom_" <> a -> axiom!(a)
            other -> reject!("unsupported $modalities entry #{other}")
          end

        _ ->
          reject!("per-modality semantics are not supported")
      end
    end)
    |> Enum.uniq()
  end

  defp modalities(_), do: reject!("unsupported $modalities")

  defp axiom!(a), do: Map.get(@axioms, a) || reject!("unsupported modal axiom #{a}")

  defp tuple_entries(node) do
    case unwrap(node) do
      %Node{kind: :thf_tuple, children: cs} -> Enum.flat_map(cs, &list/1)
      _ -> reject!("expected a list in the logic specification")
    end
  end

  defp list(%Node{kind: :thf_formula_list, children: cs}), do: Enum.flat_map(cs, &list/1)
  defp list(node), do: [node]

  defp unwrap(%Node{kind: k, children: [c]}) when k in [:thf_unitary_formula, :thf_unitary_term],
    do: unwrap(c)

  defp unwrap(node), do: node

  # ---------------------------------------------------------------------------
  # Embedding
  # ---------------------------------------------------------------------------

  @doc """
  Embeds elaborated statements under `spec`. Returns the translated statements
  followed by the frame and domain axioms, and the next free variable id.
  `params` are embedding parameters as returned by `parse_params/1`.
  """
  @spec embed([tuple()], spec(), non_neg_integer(), [param()]) ::
          {[tuple()], non_neg_integer()}
  def embed(stmts, spec, next_id, params \\ []) do
    st = %{
      spec: %{spec | frame: effective_frame(spec.frame, params)},
      params: MapSet.new(params),
      next: next_id,
      rels: MapSet.new([nil]),
      domains: MapSet.new()
    }

    {stmts, st} =
      Enum.map_reduce(stmts, st, fn
        {:sort, _} = s, st ->
          {s, st}

        {:decl, name, ty}, st ->
          {{:decl, name, lift_ty(ty)}, st}

        {:formula, _name, _role, [_ | _], _}, _st ->
          reject!("polymorphic modal formulas are not supported")

        {:formula, name, role, [], ir}, st ->
          {st, ir} = statement(st, role, ir)
          {{:formula, name, role, [], ir}, st}
      end)

    {st, frame} = frame_axioms(st)
    {st, domain} = domain_axioms(st)
    extra = Enum.map(frame ++ domain, fn {n, ir} -> {:formula, n, "axiom", [], ir} end)
    {stmts ++ extra, st.next}
  end

  # S5U has no modal axiom schema, so the syntactical variant (like
  # NO_UNIVERSAL_S5) uses an equivalence relation instead.
  defp effective_frame(frame, params) do
    if :universal in frame and
         (:no_universal_s5 in params or :modalities_syntactical in params) do
      frame |> Enum.flat_map(&if(&1 == :universal, do: [:t, :five], else: [&1])) |> Enum.uniq()
    else
      frame
    end
  end

  defp param?(st, p), do: MapSet.member?(st.params, p)

  defp statement(st, role, ir) do
    [base | sub] = String.split(role, "-", parts: 2)

    local? =
      case sub do
        ["local"] -> true
        ["global"] -> false
        [] -> base in @local_roles
        _ -> reject!("unsupported subrole #{role}")
      end

    if local? do
      at(st, ir, @actual)
    else
      {st, w} = fresh(st, @w)
      {st, body} = global(st, ir, w)
      {:var, id, _} = w
      {st, {:quant, :all, id, @w, body}}
    end
  end

  # A global statement holds at every world `w`. At its top (below conjunctions and,
  # with constant domains, universal quantifiers) an equation between terms whose
  # type contains `$o` (a definition such as `godlike = ^[X]: ...`) may be read as
  # rigid equality of the lifted terms: by extensionality, equality of the
  # extensions at every world is equality of the intensions.
  defp global(st, t, w) do
    case t do
      {:bin, :and, a, b} ->
        {st, a} = global(st, a, w)
        {st, b} = global(st, b, w)
        {st, {:bin, :and, a, b}}

      {:quant, :all, id, ty, body} when st.spec.domains == :constant ->
        {st, body} = global(st, body, w)
        {st, {:quant, :all, id, lift_ty(ty), body}}

      {:eq, a, b} ->
        ty = IR.type_of(a)

        if ty != @o and IR.has_o?(ty) do
          {st, a} = lift(st, a)
          {st, b} = lift(st, b)
          {st, {:eq, a, b}}
        else
          at(st, t, w)
        end

      _ ->
        at(st, t, w)
    end
  end

  # The truth of formula `t` at world `w`.
  defp at(st, t, w) do
    case t do
      {:const, c, [], @o} when c in ["$true", "$false"] ->
        {st, t}

      {:not, a} ->
        {st, a} = at(st, a, w)
        {st, {:not, a}}

      {:bin, op, a, b} ->
        {st, a} = at(st, a, w)
        {st, b} = at(st, b, w)
        {st, {:bin, op, a, b}}

      {:quant, q, id, ty, body} ->
        st = check_domain(st, ty)
        {st, body} = at(st, body, w)
        {st, {:quant, q, id, lift_ty(ty), guard(st, q, {:var, id, lift_ty(ty)}, ty, w, body)}}

      {:eq, a, b} ->
        ty = IR.type_of(a)

        cond do
          ty == @o ->
            {st, a} = at(st, a, w)
            {st, b} = at(st, b, w)
            {st, {:bin, :iff, a, b}}

          IR.has_o?(ty) ->
            reject!("modal equality at #{IR.show(ty)}")

          true ->
            {st, a} = lift(st, a)
            {st, b} = lift(st, b)
            {st, {:eq, a, b}}
        end

      {:modal, m, ix, a} ->
        {st, {:var, vid, _} = v} = fresh(st, @w)
        {st, body} = at(%{st | rels: MapSet.put(st.rels, ix)}, a, v)
        r = IR.app(rel(ix), [w, v])

        {st,
         case m do
           :box -> {:quant, :all, vid, @w, {:bin, :imp, r, body}}
           :dia -> {:quant, :ex, vid, @w, {:bin, :and, r, body}}
         end}

      _atomic ->
        {st, lt} = lift(st, t)
        {st, {:app, lt, w}}
    end
  end

  # The lifted (world-dependent where it has type `$o`) counterpart of a term.
  defp lift(st, t) do
    case t do
      {:const, name, [], ty} ->
        cond do
          name in ["$true", "$false"] ->
            {st, {:var, v, _}} = fresh(st, @w)
            {st, {:lam, v, @w, t}}

          String.starts_with?(name, "$") ->
            reject!("interpreted symbol #{name} in a modal problem")

          true ->
            {st, {:const, name, [], lift_ty(ty)}}
        end

      {:const, name, _, _} ->
        reject!("polymorphic symbol #{name} in a modal problem")

      {:var, id, ty} ->
        {st, {:var, id, lift_ty(ty)}}

      {:app, f, a} ->
        {st, f} = lift(st, f)
        {st, a} = lift(st, a)
        {st, {:app, f, a}}

      {:lam, id, ty, body} ->
        {st, body} = lift(st, body)
        {st, {:lam, id, lift_ty(ty), body}}

      formula ->
        {st, {:var, v, _} = w} = fresh(st, @w)
        {st, body} = at(st, formula, w)
        {st, {:lam, v, @w, body}}
    end
  end

  defp lift_ty(@o), do: {:fun, @w, @o}
  defp lift_ty({:fun, a, b}), do: {:fun, lift_ty(a), lift_ty(b)}
  defp lift_ty({:base, n} = b) when n not in ["$int", "$rat", "$real"], do: b
  defp lift_ty(ty), do: reject!("type #{IR.show(ty)} in a modal problem")

  defp check_domain(%{spec: %{domains: :constant}} = st, _ty), do: st

  defp check_domain(st, {:base, _} = ty) when ty != @o,
    do: %{st | domains: MapSet.put(st.domains, ty)}

  defp check_domain(_st, ty),
    do: reject!("quantification over #{IR.show(ty)} with non-constant domains")

  defp guard(%{spec: %{domains: :constant}}, _q, _x, _ty, _w, body), do: body

  defp guard(_st, q, x, ty, w, body) do
    e = IR.app(exists(ty), [x, w])
    if q == :all, do: {:bin, :imp, e, body}, else: {:bin, :and, e, body}
  end

  defp rel(nil), do: {:const, "$$mrel", [], IR.arrows([@w, @w], @o)}
  defp rel(ix), do: {:const, "$$mrel" <> ix, [], IR.arrows([@w, @w], @o)}

  defp exists(ty), do: {:const, "$$mexists", [], IR.arrows([ty, @w], @o)}

  # ---------------------------------------------------------------------------
  # Frame and domain conditions
  # ---------------------------------------------------------------------------

  defp frame_axioms(st) do
    st.rels
    |> Enum.sort_by(&to_string/1)
    |> Enum.flat_map_reduce(st, fn ix, st ->
      Enum.map_reduce(st.spec.frame, st, fn cond, st ->
        if param?(st, :modalities_syntactical) do
          {st, ir} = schema(st, cond, ix)
          {{"$$modal_schema_#{cond}#{ix}", ir}, st}
        else
          {st, ir} = frame(st, cond, &IR.app(rel(ix), [&1, &2]))
          {{"$$modal_frame_#{cond}#{ix}", ir}, st}
        end
      end)
    end)
    |> then(fn {axioms, st} -> {st, axioms} end)
  end

  defp frame(st, cond, r) do
    {st, w} = fresh(st, @w)
    {st, v} = fresh(st, @w)
    {st, u} = fresh(st, @w)

    body =
      case cond do
        :t -> all([w], r.(w, w))
        :b -> all([w, v], imp(r.(w, v), r.(v, w)))
        :d -> all([w], ex(v, r.(w, v)))
        :four -> all([w, v, u], imp(and_(r.(w, v), r.(v, u)), r.(w, u)))
        :five -> all([w, v, u], imp(and_(r.(w, v), r.(w, u)), r.(v, u)))
        :cd -> all([w, v, u], imp(and_(r.(w, v), r.(w, u)), {:eq, v, u}))
        :c4 -> all([w, v], imp(r.(w, v), ex(u, and_(r.(w, u), r.(u, v)))))
        :universal -> all([w, v], r.(w, v))
      end

    {st, body}
  end

  # The modal axiom schema of frame condition `cond` for modality `ix`, embedded
  # like a global statement and closed over the proposition `Phi`.
  defp schema(st, cond, ix) do
    {st, {:var, pid, _} = p} = fresh(st, @o)
    box = &{:modal, :box, ix, &1}
    dia = &{:modal, :dia, ix, &1}

    formula =
      case cond do
        :t -> imp(box.(p), p)
        :b -> imp(p, box.(dia.(p)))
        :d -> imp(box.(p), dia.(p))
        :four -> imp(box.(p), box.(box.(p)))
        :five -> imp(dia.(p), box.(dia.(p)))
        :cd -> imp(dia.(p), box.(p))
        :c4 -> imp(box.(box.(p)), box.(p))
      end

    global_schema(st, [{:var, pid, lift_ty(@o)}], formula)
  end

  # `![Vars]: ![W]: formula at W`, a schema instance valid at every world.
  defp global_schema(st, vars, formula) do
    {st, w} = fresh(st, @w)
    {st, body} = at(st, formula, w)
    {st, all(vars ++ [w], body)}
  end

  # The (converse) Barcan formula of sort `ty` along modality `ix`, embedded with
  # relativised quantifiers and closed over `P: ty > $o`.
  defp barcan(st, kind, ty, ix) do
    {st, {:var, pid, _} = p} = fresh(st, {:fun, ty, @o})
    {st, {:var, xid, _} = x} = fresh(st, ty)
    {st, {:var, yid, _} = y} = fresh(st, ty)
    box = &{:modal, :box, ix, &1}
    px = {:quant, :all, xid, ty, {:app, p, x}}
    py = &{:quant, :all, yid, ty, &1.({:app, p, y})}

    formula =
      case kind do
        :cumulative -> imp(box.(px), py.(box))
        :decreasing -> imp(py.(box), box.(px))
      end

    global_schema(st, [{:var, pid, lift_ty({:fun, ty, @o})}], formula)
  end

  defp domain_axioms(st) do
    st.domains
    |> Enum.sort()
    |> Enum.flat_map_reduce(st, fn ty, st ->
      {st, x} = fresh(st, ty)
      {st, w} = fresh(st, @w)
      {st, v} = fresh(st, @w)
      e = &IR.app(exists(ty), [&1, &2])
      name = "$$modal_domain_#{IR.sort_name(ty)}"

      nonempty =
        if param?(st, :allow_empty_domains),
          do: [],
          else: [{name <> "_nonempty", all([w], ex(x, e.(x, w)))}]

      rels = Enum.sort_by(st.rels, &to_string/1)

      {monotone, st} =
        cond do
          st.spec.domains == :varying ->
            {[], st}

          param?(st, :domains_syntactical) ->
            tag = if st.spec.domains == :cumulative, do: "cbf", else: "bf"

            Enum.map_reduce(rels, st, fn ix, st ->
              {st, ir} = barcan(st, st.spec.domains, ty, ix)
              {{"#{name}_#{tag}#{ix}", ir}, st}
            end)

          true ->
            axioms =
              for ix <- rels do
                r = IR.app(rel(ix), [w, v])

                body =
                  if st.spec.domains == :cumulative,
                    do: imp(and_(e.(x, w), r), e.(x, v)),
                    else: imp(and_(e.(x, v), r), e.(x, w))

                {"#{name}_#{st.spec.domains}#{ix}", all([x, w, v], body)}
              end

            {axioms, st}
        end

      {nonempty ++ monotone, st}
    end)
    |> then(fn {axioms, st} -> {st, axioms} end)
  end

  defp all(vars, body),
    do:
      Enum.reduce(Enum.reverse(vars), body, fn {:var, id, ty}, b -> {:quant, :all, id, ty, b} end)

  defp ex({:var, id, ty}, body), do: {:quant, :ex, id, ty, body}
  defp imp(a, b), do: {:bin, :imp, a, b}
  defp and_(a, b), do: {:bin, :and, a, b}

  defp fresh(st, ty), do: {%{st | next: st.next + 1}, {:var, st.next, ty}}
end
