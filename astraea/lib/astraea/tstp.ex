defmodule Astraea.Tstp do
  @moduledoc """
  TSTP output of SZS answers and LCF-verified refutations, after Leo-III's
  `leo.modules.output` (`SZSResult`, `SZSOutput`, `ToTHF.withAnnotation`).

  `derivation/4` turns a verified `{:proved, steps, stats}` proof DAG into a
  CNF refutation in THF syntax, structured for derivation checkers such as GDV:

    * the input formulas the proof depends on, with `file(Problem, Name)` sources
    * conjectures negated by `inference(negate_conjecture, [status(cth)], ...)`
    * the input clauses, each derived from its formulas by
      `inference(cnf, [status(esa)], ...)`
    * one `thf(c_<id>, plain, Clause, inference(Rule, [status(thm)], Parents))`
      per kernel step (`Astraea.ProofChecker`), with `bind/2` parent details
      for instantiations, ending in `$false`; search-time Skolemization
      (`:cnf` with `:skolem`) has `status(esa)` and Hilbert choice instances are
      `introduced(axiom_of_choice, [], [])`

  Terms are printed by `Astraea.External.ThfPrinter`. Every clause is closed by
  universally quantifying its free variables `V<id>`.

  The clausifier does not record which formula an input clause came from, so
  `derivation/4` recovers it by clausifying candidate formulas one at a time
  (with the problem's definitions) and matching clauses up to variable renaming.
  A clause that matches no single formula cites all candidate formulas that share
  a symbol with it, which keeps the derivation connected but weakens that step.
  """

  alias Astraea.{Arena, Clausifier, ProofChecker, TptpLower}
  alias Astraea.External.ThfPrinter

  # Node tags (u8) matching `Astraea.Arena`
  @tag_const 1
  @tag_app 4
  @tag_lam 5
  @tag_eq 6
  @tag_not 7
  @tag_or 8
  @tag_forall 9

  # Formulas clausified one by one to recover the origin of input clauses.
  @max_origin_candidates 256

  # Free variables as marked by `clause_key/3`, optionally with Skolem symbols.
  @renamed ~r/\0\d+\0/
  @renamed_with_skolems ~r/\0\d+\0|\bsk_[0-9a-f]{8}\b/
  @masked [skolems: :masked]

  @szs_names %{
    success: "Success",
    theorem: "Theorem",
    unsatisfiable: "Unsatisfiable",
    contradictory_axioms: "ContradictoryAxioms",
    counter_satisfiable: "CounterSatisfiable",
    satisfiable: "Satisfiable",
    gave_up: "GaveUp",
    timeout: "Timeout",
    resource_out: "ResourceOut",
    memory_out: "MemoryOut",
    inappropriate: "Inappropriate",
    unknown: "Unknown",
    error: "Error",
    input_error: "InputError",
    syntax_error: "SyntaxError",
    type_error: "TypeError",
    usage_error: "UsageError",
    forced: "Forced",
    user: "User"
  }

  @doc """
  Returns the SZS ontology name of a status atom (`:counter_satisfiable` ->
  `"CounterSatisfiable"`).
  """
  @spec szs_name(atom()) :: String.t()
  def szs_name(status), do: Map.get(@szs_names, status, "Unknown")

  @doc """
  Renders `% SZS status <Status> for <problem>`, with ` : <info>` when given.
  """
  @spec status_line(atom(), String.t(), String.t() | nil) :: String.t()
  def status_line(status, problem, info \\ nil) do
    base = "% SZS status #{szs_name(status)} for #{problem}"
    if info in [nil, ""], do: base, else: base <> " : " <> info
  end

  @doc """
  Wraps `body` in `% SZS output start/end <dataform> for <problem>` lines.
  """
  @spec output_block(String.t(), String.t(), iodata()) :: iodata()
  def output_block(dataform, problem, body) do
    [
      ["% SZS output start ", dataform, " for ", problem, "\n"],
      body,
      ["% SZS output end ", dataform, " for ", problem, "\n"]
    ]
  end

  @doc """
  Renders an LCF-verified refutation as a TSTP derivation (without the SZS
  output block). `lowered` is the problem the proof was found for and
  `stats.arena` the arena of its steps. Options:
    * `:problem` - file name cited in `file/2` sources (default `"unknown"`)
    * `:problem_path`, `:tptp_root` - the problem file (and the root its includes
      are resolved against) whose formulas are printed verbatim
  """
  @spec derivation(TptpLower.t(), [ProofChecker.step()], map(), keyword()) :: String.t()
  def derivation(%TptpLower{} = lowered, steps, %{arena: %Arena{} = arena}, opts \\ []) do
    problem = Keyword.get(opts, :problem, "unknown")
    {arena, clauses} = replay(arena, steps)

    leaves = for {:axiom, id, clause} <- steps, do: {id, clause}
    origins = origins(lowered, arena, leaves)
    conj_names = MapSet.new(lowered.conjectures, &elem(&1, 0))

    used =
      origins |> Map.values() |> List.flatten() |> MapSet.new()

    {inputs, syms} = input_formulas(lowered, used, problem, opts)

    {derived, syms} =
      Enum.map_reduce(steps, syms, fn step, syms ->
        id = elem(step, 1)
        {body, syms} = ThfPrinter.clause(arena, Map.fetch!(clauses, id), syms)

        {role, source, syms} =
          case step do
            {:axiom, _id, _clause} ->
              parents = Map.fetch!(origins, id)
              conj? = Enum.any?(parents, &MapSet.member?(conj_names, &1))
              parents = Enum.map(parents, &if(conj?(&1, conj_names), do: neg_name(&1), else: &1))

              {if(conj?, do: "negated_conjecture", else: "plain"),
               inference("cnf", "esa", Enum.map(parents, &name/1)), syms}

            _ ->
              {source, syms} = source(arena, step, syms)
              {"plain", source, syms}
          end

        {["thf(", step_name(id), ", ", role, ", ", body, ",\n    ", source, ").\n"], syms}
      end)

    IO.iodata_to_binary([
      ThfPrinter.declarations(arena, syms, "decl_"),
      inputs,
      derived
    ])
  end

  @doc """
  Replays the clauses derived by the (already verified) kernel `steps`, keyed by
  step id. Mirrors the conclusions computed by `Astraea.ProofChecker`.
  """
  @spec replay(Arena.t(), [ProofChecker.step()]) ::
          {Arena.t(), %{non_neg_integer() => ProofChecker.clause()}}
  def replay(%Arena{} = arena, steps) do
    Enum.reduce(steps, {arena, %{}}, fn step, {ar, derived} ->
      {ar, clause} = conclusion(ar, derived, step)
      {ar, Map.put(derived, elem(step, 1), clause)}
    end)
  end

  defp conclusion(arena, _derived, {:avatar_split, _id, _p, guards}) do
    {arena, MapSet.new(Enum.map(guards, &{:pos, &1}))}
  end

  defp conclusion(arena, _derived, {:avatar_comp, _id, _p, guard, comp_lits}) do
    {arena, MapSet.put(comp_lits, {:neg, guard})}
  end

  defp conclusion(arena, _derived, {:axiom, _id, clause}), do: {arena, clause}

  defp conclusion(arena, _derived, {:refl, _id, term}) do
    {arena, norm} = Arena.beta_eta_norm(arena, term)
    unit_eq(arena, norm, norm)
  end

  defp conclusion(arena, derived, {:symm, _id, p}) do
    {lhs, rhs} = unit_sides(arena, derived[p])
    unit_eq(arena, rhs, lhs)
  end

  defp conclusion(arena, derived, {:trans, _id, p1, p2}) do
    {a, _} = unit_sides(arena, derived[p1])
    {_, c} = unit_sides(arena, derived[p2])
    unit_eq(arena, a, c)
  end

  defp conclusion(arena, derived, {:subst, _id, p, subst}) do
    Enum.reduce(derived[p], {arena, MapSet.new()}, fn {pol, atom}, {ar, acc} ->
      {ar, subbed} = Arena.subst_fvar(ar, atom, subst)
      {ar, MapSet.put(acc, {pol, subbed})}
    end)
  end

  defp conclusion(arena, derived, {:cong, _id, p, eq_atom, arg}) do
    {@tag_eq, _, _, lhs, rhs} = Arena.get_node(arena, eq_atom)
    {arena, fa} = Arena.mk_app(arena, lhs, arg)
    {arena, ga} = Arena.mk_app(arena, rhs, arg)
    {arena, fa} = Arena.beta_eta_norm(arena, fa)
    {arena, ga} = Arena.beta_eta_norm(arena, ga)
    {arena, eq} = Arena.mk_eq(arena, fa, ga)
    {arena, derived[p] |> MapSet.delete({:pos, eq_atom}) |> MapSet.put({:pos, eq})}
  end

  defp conclusion(arena, derived, {:func_ext, _id, p, fvar, ty}) do
    {lhs, rhs} = unit_sides(arena, derived[p])
    {arena, fv} = Arena.mk_fvar(arena, fvar, ty)
    {arena, l} = abstract(arena, lhs, fv, ty)
    {arena, r} = abstract(arena, rhs, fv, ty)
    unit_eq(arena, l, r)
  end

  defp conclusion(arena, derived, {:paramod, _id, e, t, eq_atom, target_lit, rewritten_lit}) do
    clause =
      derived[e]
      |> MapSet.delete({:pos, eq_atom})
      |> MapSet.union(MapSet.delete(derived[t], target_lit))
      |> MapSet.put(rewritten_lit)

    {arena, clause}
  end

  defp conclusion(arena, derived, {:cnf, _id, p, lit, rule}) do
    {:ok, arena, lits} = ProofChecker.expand_literal(arena, lit, rule)
    {arena, derived[p] |> MapSet.delete(lit) |> MapSet.union(MapSet.new(lits))}
  end

  defp conclusion(arena, _derived, {:choice, _id, pred, fvar}) do
    {:ok, arena, clause} = ProofChecker.choice_instance(arena, pred, fvar)
    {arena, clause}
  end

  # Ground arithmetic evaluation (input workstream): the step states its conclusion.
  defp conclusion(arena, _derived, {:arith_eval, _id, _p, clause}), do: {arena, clause}

  # Ground lambda / combinator / boolean evaluation
  defp conclusion(arena, _derived, {:eval, _id, _p, clause}), do: {arena, clause}

  defp conclusion(arena, derived, {:eq_fact, _id, p, eq1_id, eq2_id}) do
    parent = derived[p]
    {@tag_eq, _, _, lhs1, rhs1} = Arena.get_node(arena, eq1_id)
    {@tag_eq, _, _, lhs2, rhs2} = Arena.get_node(arena, eq2_id)
    {_common, rem1, rem2} = ProofChecker.match_eq_sides(lhs1, rhs1, lhs2, rhs2)
    {arena, neg_eq} = Arena.mk_eq(arena, rem1, rem2)

    new_clause =
      parent
      |> MapSet.delete({:pos, eq1_id})
      |> MapSet.put({:neg, neg_eq})

    {arena, new_clause}
  end

  defp conclusion(arena, derived, {:resolve, _id, p1, p2, {:pos, atom}}) do
    {c1, c2} = {derived[p1], derived[p2]}

    {arena, l1, l2} =
      if MapSet.member?(c1, {:pos, atom}) and MapSet.member?(c2, {:neg, atom}) do
        {arena, {:pos, atom}, {:neg, atom}}
      else
        {@tag_eq, _, _, l, r} = Arena.get_node(arena, atom)
        {arena, sym} = Arena.mk_eq(arena, r, l)

        if MapSet.member?(c1, {:pos, atom}) and MapSet.member?(c2, {:neg, sym}),
          do: {arena, {:pos, atom}, {:neg, sym}},
          else: {arena, {:pos, sym}, {:neg, atom}}
      end

    {arena, MapSet.union(MapSet.delete(c1, l1), MapSet.delete(c2, l2))}
  end

  defp unit_sides(arena, clause) do
    [{:pos, eq}] = MapSet.to_list(clause)
    {@tag_eq, _, _, lhs, rhs} = Arena.get_node(arena, eq)
    {lhs, rhs}
  end

  defp unit_eq(arena, lhs, rhs) do
    {arena, eq} = Arena.mk_eq(arena, lhs, rhs)
    {arena, MapSet.new([{:pos, eq}])}
  end

  defp abstract(arena, term, fv, ty) do
    {arena, body} = Arena.abstract_subterm(arena, term, fv, 0)
    {arena, lam} = Arena.mk_lam(arena, ty, body)
    Arena.beta_eta_norm(arena, lam)
  end

  # The TSTP source of a kernel step: its rule, SZS status and parents (with
  # `bind/2` details for instantiations). Choice instances are introduced axioms.
  defp source(_arena, {:choice, _, _, _}, syms),
    do: {"introduced(axiom_of_choice, [], [])", syms}

  defp source(arena, {:subst, _, p, subst}, syms) do
    {binds, syms} =
      subst
      |> Enum.sort()
      |> Enum.map_reduce(syms, fn {var, term}, syms ->
        {t, syms} = ThfPrinter.formula(arena, term, syms)
        {["bind(V", Integer.to_string(var), ", $thf(", t, "))"], syms}
      end)

    parent =
      if binds == [],
        do: step_name(p),
        else: [step_name(p), ":[", Enum.intersperse(binds, ", "), "]"]

    {inference("instantiate", "thm", [parent]), syms}
  end

  defp source(_arena, step, syms) do
    {rule, status} = rule(step)
    {inference(rule, status, step |> ProofChecker.step_parents() |> Enum.map(&step_name/1)), syms}
  end

  defp rule({:refl, _, _}), do: {"refl", "thm"}
  defp rule({:symm, _, _}), do: {"symmetry", "thm"}
  defp rule({:trans, _, _, _}), do: {"transitivity", "thm"}
  defp rule({:cong, _, _, _, _}), do: {"arg_cong", "thm"}
  defp rule({:eq_fact, _, _, _, _}), do: {"eq_fact", "thm"}
  defp rule({:func_ext, _, _, _, _}), do: {"func_ext", "thm"}
  defp rule({:paramod, _, _, _, _, _, _}), do: {"paramod", "thm"}
  defp rule({:resolve, _, _, _, _}), do: {"resolution", "thm"}
  defp rule({:avatar_split, _, _, _}), do: {"avatar_split", "thm"}
  defp rule({:avatar_comp, _, _, _, _}), do: {"avatar_component", "thm"}
  defp rule({:arith_eval, _, _, _}), do: {"evaluate", "thm"}
  defp rule({:eval, _, _, _}), do: {"eval", "thm"}
  defp rule({:cnf, _, _, _, :skolem}), do: {"skolemize", "esa"}
  defp rule({:cnf, _, _, _, :ext}), do: {"func_ext", "thm"}
  defp rule({:cnf, _, _, _, {:bool_eq, _}}), do: {"bool_ext", "thm"}
  defp rule({:cnf, _, _, _, {:forall, _}}), do: {"instantiate", "thm"}
  defp rule({:cnf, _, _, _, _rule}), do: {"cnf", "thm"}

  defp inference(rule, status, parents) do
    ["inference(", rule, ", [status(", status, ")], [", Enum.intersperse(parents, ", "), "])"]
  end

  defp step_name(id), do: ["c_", Integer.to_string(id)]

  defp neg_name(name), do: "neg_" <> name

  defp conj?(name, conj_names), do: MapSet.member?(conj_names, name)

  @name_word ~r/^([a-z][A-Za-z0-9_]*|[0-9]+)$/

  defp name(name) do
    if Regex.match?(@name_word, name), do: name, else: ThfPrinter.atom(name)
  end

  # Input formulas cited by the clausification steps, in problem order. They are
  # printed as written in the problem file when it can be read (so that `file/2`
  # leaves match it verbatim), else from their lowered form.
  defp input_formulas(lowered, used, problem, opts) do
    file = ThfPrinter.atom(problem)
    originals = original_formulas(opts)

    axioms =
      for {n, role, term} <- lowered.axioms, MapSet.member?(used, n), do: {n, role, term}

    conjs =
      for {n, term} <- lowered.conjectures, MapSet.member?(used, n), do: {n, "conjecture", term}

    Enum.flat_map_reduce(axioms ++ conjs, MapSet.new(), fn {n, role, term}, syms ->
      {lang, role, f, syms} =
        case Map.fetch(originals, n) do
          {:ok, {lang, orig_role, f}} ->
            # The lowered form only contributes the symbols to declare.
            {_lowered_f, syms} = ThfPrinter.formula(lowered.arena, term, syms)
            {lang, orig_role, f, syms}

          :error ->
            {f, syms} = ThfPrinter.formula(lowered.arena, term, syms)
            {"thf", role, f, syms}
        end

      line = [
        lang,
        "(",
        name(n),
        ", ",
        role,
        ", ",
        f,
        ",\n    file(",
        file,
        ", ",
        name(n),
        ")).\n"
      ]

      if role == "conjecture" do
        neg = [
          [lang, "(", name(neg_name(n)), ", negated_conjecture, ~ (", f, "),\n    "],
          [inference("negate_conjecture", "cth", [name(n)]), ").\n"]
        ]

        {[line, neg], syms}
      else
        {[line], syms}
      end
    end)
  end

  defp original_formulas(opts) do
    with path when is_binary(path) <- Keyword.get(opts, :problem_path),
         root = Keyword.get_lazy(opts, :tptp_root, &Astraea.TptpCorpus.default_tptp_root/0),
         {:ok, unit, _diagnostics} <-
           Tptp.Unit.from_file(path, resolver: {Tptp.Resolver.Fs, root: root}, max_concurrency: 1) do
      for {_file, stmt} <- Tptp.Unit.formulae(unit), into: %{} do
        {Tptp.Node.value(stmt.name),
         {Atom.to_string(stmt.language), Tptp.Node.value(stmt.role),
          Tptp.Printer.Canonical.to_iodata(stmt.formula)}}
      end
    else
      _ -> %{}
    end
  end

  # ---------------------------------------------------------------------------
  # Clause origins
  # ---------------------------------------------------------------------------

  # Maps each leaf `{id, clause}` to the names of the input formulas it came from.
  defp origins(lowered, arena, leaves) do
    leaf_keys = Map.new(leaves, fn {id, clause} -> {id, clause_key(arena, clause, @masked)} end)
    leaf_syms = Map.new(leaves, fn {id, clause} -> {id, clause_symbols(arena, clause)} end)
    wanted = leaf_syms |> Map.values() |> Enum.reduce(MapSet.new(), &MapSet.union/2)

    formulas =
      Enum.map(lowered.axioms, fn {n, role, t} -> {n, role, t} end) ++
        Enum.map(lowered.conjectures, fn {n, t} -> {n, "conjecture", t} end)

    formula_syms =
      Map.new(formulas, fn {n, _role, t} -> {n, term_symbols(lowered.arena, t, MapSet.new())} end)

    candidates =
      formulas
      |> Enum.filter(fn {n, role, _t} ->
        role != "definition" and not MapSet.disjoint?(formula_syms[n], wanted)
      end)
      |> Enum.take(@max_origin_candidates)

    clause_sets = clause_sets(lowered, candidates)

    definitions =
      for {n, "definition", t} <- formulas, sym = defined_symbol(lowered.arena, t), into: %{} do
        {sym, n}
      end

    Map.new(leaves, fn {id, _clause} ->
      key = leaf_keys[id]

      parents =
        case for({n, keys} <- clause_sets, MapSet.member?(keys, key), do: n) do
          [n | _] ->
            [n]

          [] ->
            sharing =
              for {n, _role, _t} <- formulas,
                  not MapSet.disjoint?(formula_syms[n], leaf_syms[id]),
                  do: n

            if sharing == [], do: Enum.map(formulas, &elem(&1, 0)), else: sharing
        end

      {id, parents ++ definitions_used(parents, definitions, formula_syms)}
    end)
  end

  # The definitions (`c = t` with role `definition`) that the clausifier inlined
  # into `names`, transitively.
  defp definitions_used(names, definitions, formula_syms) do
    syms = names |> Enum.map(&formula_syms[&1]) |> Enum.reduce(MapSet.new(), &MapSet.union/2)
    close_definitions(syms, MapSet.new(names), definitions, formula_syms, [])
  end

  defp close_definitions(syms, seen, definitions, formula_syms, acc) do
    new =
      for {sym, n} <- definitions,
          MapSet.member?(syms, sym),
          not MapSet.member?(seen, n),
          do: n

    case new do
      [] ->
        Enum.reverse(acc)

      _ ->
        syms = Enum.reduce(new, syms, &MapSet.union(&2, formula_syms[&1]))
        seen = MapSet.union(seen, MapSet.new(new))
        close_definitions(syms, seen, definitions, formula_syms, Enum.reverse(new) ++ acc)
    end
  end

  # The constant defined by `! [X..]: (c @ X..) = t`.
  defp defined_symbol(arena, id) do
    case Arena.get_node(arena, id) do
      {@tag_forall, _, _, _dom, body} -> defined_symbol(arena, body)
      {@tag_eq, _, _, lhs, _rhs} -> head_symbol(arena, lhs)
      _ -> nil
    end
  end

  defp head_symbol(arena, id) do
    case Arena.get_node(arena, id) do
      {@tag_app, _, _, fun, _arg} -> head_symbol(arena, fun)
      {@tag_const, _, _, sym, _} -> Map.fetch!(arena.symbol_names, sym)
      _ -> nil
    end
  end

  # Clause keys of each candidate formula, clausified together with the problem's
  # definitions (which the clausifier inlines) minus the definitions' own clauses.
  defp clause_sets(lowered, candidates) do
    defs = Enum.filter(lowered.axioms, fn {_n, role, _t} -> role == "definition" end)
    only = fn axioms, conjs, ib -> %{lowered | axioms: axioms, conjectures: conjs} |> keys(ib) end
    base = only.(defs, [], false)

    Enum.map(candidates, fn
      {n, "conjecture", t} ->
        keys =
          MapSet.union(only.(defs, [{n, t}], false), only.(defs, [{n, t}], true))

        {n, MapSet.difference(keys, base)}

      ax ->
        {elem(ax, 0), MapSet.difference(only.(defs ++ [ax], [], false), base)}
    end)
  end

  defp keys(lowered, inline_bridges) do
    {arena, clauses} =
      Clausifier.clausify(lowered, sine_limit: nil, inline_bridges: inline_bridges)

    MapSet.new(clauses, &clause_key(arena, &1, @masked))
  end

  @doc """
  A key identifying `clause` up to renaming of its free variables: literals are
  sorted by their variable-blind rendering and variables numbered by first
  occurrence. Keys of clauses from different arenas are comparable.

  With `skolems: :masked` Skolem symbols are renamed like variables. Their
  content-addressed names depend on the variable numbering of the clausification
  run, so this matches clauses of separate runs, but it also identifies clauses
  that differ only in their Skolem symbols.
  """
  @spec clause_key(Arena.t(), ProofChecker.clause(), keyword()) :: String.t()
  def clause_key(%Arena{} = arena, clause, opts \\ []) do
    renamed = if opts[:skolems] == :masked, do: @renamed_with_skolems, else: @renamed

    marked =
      clause
      |> Enum.map(fn {pol, atom} ->
        {printed, _} =
          ThfPrinter.formula(arena, atom, MapSet.new(),
            var_name: &["\0", Integer.to_string(&1), "\0"]
          )

        printed = IO.iodata_to_binary(printed)
        {String.replace(printed, renamed, "_"), pol, printed}
      end)
      |> Enum.sort()
      |> Enum.map_join(" | ", fn {_blind, pol, printed} -> "#{pol} #{printed}" end)

    {key, _numbering} =
      renamed
      |> Regex.split(marked, include_captures: true)
      |> Enum.map_reduce(%{}, fn part, numbering ->
        if Regex.match?(renamed, part) do
          numbering = Map.put_new(numbering, part, map_size(numbering))
          {"X#{numbering[part]}", numbering}
        else
          {part, numbering}
        end
      end)

    Enum.join(key)
  end

  defp clause_symbols(arena, clause) do
    Enum.reduce(clause, MapSet.new(), fn {_pol, atom}, acc -> term_symbols(arena, atom, acc) end)
  end

  defp term_symbols(arena, id, acc) do
    {tag, _flags, _ty, left, right} = Arena.get_node(arena, id)

    case tag do
      @tag_const ->
        name = Map.fetch!(arena.symbol_names, left)
        if String.starts_with?(name, "$"), do: acc, else: MapSet.put(acc, name)

      tag when tag in [@tag_app, @tag_eq, @tag_or] ->
        term_symbols(arena, right, term_symbols(arena, left, acc))

      tag when tag in [@tag_lam, @tag_forall] ->
        term_symbols(arena, right, acc)

      @tag_not ->
        term_symbols(arena, left, acc)

      _ ->
        acc
    end
  end
end
