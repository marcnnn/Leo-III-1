defmodule Astraea.RelevanceFilter do
  @moduledoc """
  Leo-III's symbol-based relevance filter (`modules/relevance_filter`: `PreFilterSet`,
  `FuncFrequency`, `RelevanceFilter`, `SeqFilter`, driven by
  `Control.getRelevantAxioms`), after Meng and Paulson, "Lightweight Relevance
  Filtering for Machine-Generated Resolution Problems".

  Every formula is reduced to the set of its uninterpreted constant symbols. Symbols
  of definitions (`Astraea.Clausifier` inlines them) are delta-expanded: a defined
  symbol stands for itself plus the expanded symbols of its body.

    1. The symbols of the conjectures (and `negated_conjecture` formulas) are marked
       as used. Round 0 considers every axiom that shares an expanded symbol with
       them.
    2. A candidate with symbol set `S` is taken in round `k` iff
       `sum / (sum + new) >= pass_k`, where `sum` is the sum of
       `1 + 2 / ln(freq(s) + 1)` over `s` in `S` (`freq(s)` is the number of formulas
       that mention `s`), `new` is the number of symbols of `S` that are not used yet,
       and `pass_0 = passmark`, `pass_(k+1) = pass_k + (1 - pass_k) / aging`.
    3. Taken axioms mark their expanded symbols as used; the next round considers
       the unused axioms that mention one of the newly used symbols. The filter
       stops when a round takes nothing.

  Like Leo-III, the filter keeps every axiom when there is no conjecture or when a
  conjecture mentions no uninterpreted symbol, and `:auto` picks the passmark from
  the number of axioms (no filtering below 15 axioms). Axioms that share no symbol
  with the selection are never reached, also when they have no symbols at all.

  Dropping axioms is sound for refutations (a refutation of a subset refutes the
  whole set) but not for model answers: a saturated filtered problem says nothing
  about the full one, so callers must treat a run on filtered input as incomplete
  (`Astraea.Clausifier.clausify_with_info/2` reports `:axioms_dropped`).
  """

  alias Astraea.Arena

  # Node tags (u8) matching `Astraea.Arena`
  @tag_const 1
  @tag_app 4
  @tag_lam 5
  @tag_eq 6
  @tag_not 7
  @tag_or 8
  @tag_forall 9

  # Leo-III `Configuration.DEFAULT_PASSMARK` and `DEFAULT_AGING`
  @default_passmark 0.56
  @default_aging 2.35

  @seed_roles ["negated_conjecture"]

  @type config :: :auto | %{optional(:passmark) => float(), optional(:aging) => float()}
  @type axiom :: {String.t(), String.t(), Arena.term_id()}

  @doc "Leo-III's default passmark (`--relevance-passmark`)."
  @spec default_passmark() :: float()
  def default_passmark, do: @default_passmark

  @doc "Leo-III's default aging factor (`--relevance-aging`)."
  @spec default_aging() :: float()
  def default_aging, do: @default_aging

  @doc """
  Resolves a filter configuration into `{passmark, aging}`, or `:all` when nothing
  is filtered. A map takes Leo-III's defaults for omitted keys (as Leo-III does when
  only one of `--relevance-passmark`/`--relevance-aging` is given); `:auto` follows
  the axiom-count table of `Control.getRelevantAxioms`.
  """
  @spec params(config(), non_neg_integer()) :: {float(), float()} | :all
  def params(:auto, n_axioms) do
    cond do
      n_axioms < 15 -> :all
      n_axioms < 20 -> {0.50, @default_aging}
      n_axioms < 100 -> {0.55, @default_aging}
      n_axioms < 200 -> {0.60, @default_aging}
      n_axioms < 500 -> {0.62, @default_aging}
      n_axioms < 1000 -> {0.64, @default_aging}
      n_axioms < 2000 -> {0.70, @default_aging}
      true -> {0.75, @default_aging}
    end
  end

  def params(%{} = config, _n_axioms) do
    passmark = Map.get(config, :passmark) || @default_passmark
    aging = Map.get(config, :aging) || @default_aging
    {passmark * 1.0, aging * 1.0}
  end

  @doc """
  Selects the relevant axioms. `axioms` are `{name, role, term_id}` (formulas with
  role `negated_conjecture` act as conjectures and are always kept), `conjectures`
  are `{name, term_id}`, and `defs` maps defined constant term ids to their bodies
  (delta expansion). Returns the selected axioms in input order.
  """
  @spec select(Arena.t(), [axiom()], [{String.t(), Arena.term_id()}], %{}, config()) ::
          [axiom()]
  def select(%Arena{} = arena, axioms, conjectures, defs, config) do
    {seeds, candidates} = Enum.split_with(axioms, fn {_n, role, _id} -> role in @seed_roles end)
    seed_ids = Enum.map(conjectures, &elem(&1, 1)) ++ Enum.map(seeds, &elem(&1, 2))

    case params(config, length(candidates)) do
      :all ->
        axioms

      {passmark, aging} ->
        seed_syms = Enum.map(seed_ids, &symbols(arena, &1))

        if seed_syms == [] or Enum.any?(seed_syms, &(MapSet.size(&1) == 0)) do
          axioms
        else
          kept = run(arena, candidates, seed_ids, seed_syms, defs, passmark, aging)
          Enum.filter(axioms, fn {_n, role, _id} = ax -> role in @seed_roles or ax in kept end)
        end
    end
  end

  # `Control.getRelevantAxioms0` over a `PreFilterSet` built from `candidates` and
  # the seeds. Candidates are addressed by their list index.
  defp run(arena, candidates, seed_ids, seed_syms, defs, passmark, aging) do
    def_syms = expand_defs(arena, defs)

    entries =
      candidates
      |> Enum.with_index()
      |> Map.new(fn {{_n, _r, id} = ax, idx} ->
        raw = symbols(arena, id)
        {idx, %{axiom: ax, raw: raw, expanded: expand(raw, def_syms)}}
      end)

    # `FuncFrequency`: the number of formulas (axioms and conjectures) per symbol
    freq =
      Enum.reduce(Map.values(entries) |> Enum.map(& &1.raw) |> Kernel.++(seed_syms), %{}, fn
        syms, acc -> Enum.reduce(syms, acc, fn s, m -> Map.update(m, s, 1, &(&1 + 1)) end)
      end)

    # `PreFilterSet.reverse`: expanded symbol -> candidate indices
    reverse =
      Enum.reduce(entries, %{}, fn {idx, e}, acc ->
        Enum.reduce(e.expanded, acc, fn s, m -> Map.update(m, s, [idx], &[idx | &1]) end)
      end)

    used =
      seed_ids
      |> Enum.map(&expand(symbols(arena, &1), def_syms))
      |> Enum.reduce(MapSet.new(), &MapSet.union/2)

    state = %{
      entries: entries,
      freq: freq,
      reverse: reverse,
      unused: Map.keys(entries) |> MapSet.new()
    }

    loop(state, used, used, 0, passmark, aging, MapSet.new())
  end

  defp loop(state, used, new_syms, round, passmark, aging, kept) do
    pass = Enum.reduce(1..round//1, passmark, fn _, p -> p + (1 - p) / aging end)

    taken =
      new_syms
      |> Enum.flat_map(&Map.get(state.reverse, &1, []))
      |> Enum.uniq()
      |> Enum.filter(&MapSet.member?(state.unused, &1))
      |> Enum.sort()
      |> Enum.filter(&(grade(state, state.entries[&1].raw, used) >= pass))

    if taken == [] do
      kept
    else
      fresh =
        taken
        |> Enum.map(&state.entries[&1].expanded)
        |> Enum.reduce(MapSet.new(), &MapSet.union/2)
        |> MapSet.difference(used)

      state = %{state | unused: MapSet.difference(state.unused, MapSet.new(taken))}
      kept = Enum.reduce(taken, kept, &MapSet.put(&2, state.entries[&1].axiom))
      loop(state, MapSet.union(used, fresh), fresh, round + 1, passmark, aging, kept)
    end
  end

  # `RelevanceFilter.apply`: Leo-III sums the frequency weight over all symbols of
  # the candidate (not only the relevant ones, as in Meng and Paulson).
  defp grade(state, syms, used) do
    if MapSet.size(syms) == 0 do
      1.0
    else
      new = MapSet.size(syms) - MapSet.size(MapSet.intersection(syms, used))

      sum =
        Enum.reduce(syms, 0.0, fn s, acc ->
          acc + 1 + 2 / :math.log(Map.get(state.freq, s, 1) + 1)
        end)

      sum / (sum + new)
    end
  end

  # `PreFilterSet.expaned_symbols`: a defined symbol contributes itself and its
  # delta-expanded body symbols.
  defp expand(raw, def_syms) do
    Enum.reduce(raw, MapSet.new(), fn s, acc ->
      case Map.fetch(def_syms, s) do
        {:ok, body} -> acc |> MapSet.union(body) |> MapSet.put(s)
        :error -> MapSet.put(acc, s)
      end
    end)
  end

  # `PreFilterSet.defn`: defined symbol -> fully delta-expanded body symbols (the
  # defined symbols inside a body are replaced by their own expansion).
  defp expand_defs(arena, defs) do
    bodies =
      Map.new(defs, fn {const_id, body_id} ->
        {@tag_const, _, _, sym_id, _} = Arena.get_node(arena, const_id)
        {sym_id, symbols(arena, body_id)}
      end)

    Map.new(bodies, fn {sym, _} -> {sym, delta(sym, bodies, MapSet.new([sym]))} end)
  end

  defp delta(sym, bodies, visiting) do
    Enum.reduce(Map.fetch!(bodies, sym), MapSet.new(), fn s, acc ->
      cond do
        MapSet.member?(visiting, s) -> acc
        Map.has_key?(bodies, s) -> MapSet.union(acc, delta(s, bodies, MapSet.put(visiting, s)))
        true -> MapSet.put(acc, s)
      end
    end)
  end

  @doc "Uninterpreted constant symbols (symbol ids) of `term_id`, without `$true`/`$false`."
  @spec symbols(Arena.t(), Arena.term_id()) :: MapSet.t(non_neg_integer())
  def symbols(%Arena{} = arena, term_id), do: collect(arena, term_id, MapSet.new())

  defp collect(arena, term_id, acc) do
    {tag, _flags, _ty, left, right} = Arena.get_node(arena, term_id)

    case tag do
      @tag_const ->
        name = Map.get(arena.symbol_names, left, "")
        if name in ["$true", "$false"], do: acc, else: MapSet.put(acc, left)

      @tag_not ->
        collect(arena, left, acc)

      t when t in [@tag_lam, @tag_forall] ->
        collect(arena, right, acc)

      t when t in [@tag_app, @tag_eq, @tag_or] ->
        collect(arena, right, collect(arena, left, acc))

      _ ->
        acc
    end
  end
end
