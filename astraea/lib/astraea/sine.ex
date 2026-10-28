defmodule Astraea.Sine do
  @moduledoc """
  Leo-III's SInE axiom selection (`--sine`, `--standard-sine`): `modules/relevance`
  (`SineSelector`, `AxiomFilter`, `AxiomFilterConfig`, `SymbolDistribution`) driven
  by `Control.RelevanceFilterControl` (`getBestFilterConfig`,
  `guessSineFilterConfig`, `getRelevantAxiomsNew`) from `SeqLoop.effectiveInputNew`.
  After Hoder and Voronkov, "Sine Qua Non for Large Theory Reasoning", CADE-23.

  Every formula is reduced to the set of its uninterpreted constant symbols, and the
  occurrence count `occ(s)` of a symbol is the number of formulas (axioms,
  conjectures, `negated_conjecture` formulas and definition bodies) that mention it.

    1. Trigger relation: an axiom `A` is triggered by its symbol `s` iff
       `occ(s) <= tolerance * occ(s')` for the rarest symbol `s'` of `A`. Axioms
       without symbols are always selected.
    2. The symbols of the conjectures are triggered in step 0. Step `k + 1`
       selects the axioms triggered by the symbols that step `k` triggered for the
       first time; their symbols, and the body symbols of triggered defined
       symbols, are the next step's symbols. Selection stops after `max_depth`
       steps (`-1`: until nothing new is selected) or when it would exceed
       `max_size` axioms, in which case the last step is cut to fit.
    3. Problems with at most 25 axioms are passed whole
       (`ThresholdPassFilterConfig(passingThreshold = 25, ...)`), and nothing is
       filtered without a conjecture.

  The configuration (`config/2`) is either given as
  `%{threshold: t, max_size: n, max_depth: d}` (Leo-III `--sine "t;n;d"`), or
  guessed from the numbers of internal (problem file) and external (`include`d)
  axioms by Leo-III's table, whose fallback is a configuration chosen from the
  total count; `:standard` (`--standard-sine`) always takes that fallback.

  Dropping axioms is sound for refutations but not for model answers, so callers
  must treat a run on filtered input as incomplete
  (`Astraea.Clausifier.clausify_with_info/2` reports `:axioms_dropped`).
  """

  alias Astraea.{Arena, RelevanceFilter}

  # Node tag (u8) matching `Astraea.Arena`
  @tag_const 1

  # `RelevanceFilterControl.passingThreshold`
  @passing_threshold 25

  @seed_roles ["negated_conjecture"]

  @typedoc """
  A SInE configuration (Leo-III `SineConfig`): `tolerance` (the `--sine` threshold),
  `max_size` (`maxAbsoluteSize`), `max_depth` (`-1` unbounded). Leo-III's
  `maxProportion` is always 1 and omitted.
  """
  @type config :: %{tolerance: float(), max_size: pos_integer(), max_depth: integer()}

  @typedoc """
  The `:sine` option of `Astraea.Clausifier`: `:auto` guesses the configuration
  (Leo-III `--sine` without a valid value), a map or a `"t;n;d"` string gives it.
  """
  @type option ::
          :auto
          | String.t()
          | %{threshold: number(), max_size: pos_integer(), max_depth: integer()}

  @type axiom :: {String.t(), String.t(), Arena.term_id()}

  @doc "Problems with at most this many axioms are not filtered (Leo-III 25)."
  @spec passing_threshold() :: pos_integer()
  def passing_threshold, do: @passing_threshold

  @doc """
  Parses Leo-III's `--sine "threshold;maxAbsoluteSize;maxDepth"` value. Returns
  `:error` when Leo-III's parse would throw (it then warns and guesses).
  """
  @spec parse(String.t()) :: {:ok, config()} | :error
  def parse(value) when is_binary(value) do
    with [t, n, d | _] <- String.split(value, ";"),
         {:ok, t} <- parse_double(t),
         {n, ""} <- Integer.parse(String.trim(n)),
         {d, ""} <- Integer.parse(String.trim(d)) do
      {:ok, %{tolerance: t, max_size: n, max_depth: d}}
    else
      _ -> :error
    end
  end

  # Scala's `toDouble` accepts integers and decimals (`2`, `1.5`, `.5`).
  defp parse_double(str) do
    str = String.trim(str)
    str = if String.starts_with?(str, "."), do: "0" <> str, else: str

    case Float.parse(str) do
      {f, ""} -> {:ok, f}
      _ -> :error
    end
  end

  @doc """
  Resolves the `:sine` option against the axiom counts (`internal` from the problem
  file, `external` from includes), Leo-III `getBestFilterConfig`. An explicit
  configuration is used as given; `:auto` and an unparsable string guess one
  (`guess/3`, with `standard: true` for `--standard-sine`).
  """
  @spec config(option(), keyword()) :: config()
  def config(option, opts \\ []) do
    internal = Keyword.get(opts, :internal, 0)
    external = Keyword.get(opts, :external, 0)
    standard = Keyword.get(opts, :standard, false)

    case option do
      %{threshold: t, max_size: n, max_depth: d} ->
        %{tolerance: t * 1.0, max_size: n, max_depth: d}

      value when is_binary(value) ->
        case parse(value) do
          {:ok, config} -> config
          :error -> guess(internal, external, standard)
        end

      :auto ->
        guess(internal, external, standard)
    end
  end

  @doc """
  Leo-III's `defaultConfig` of `guessSineFilterConfig`, by the total number of
  axioms (`--standard-sine`, and the table's fallback).
  """
  @spec default_config(non_neg_integer()) :: config()
  def default_config(axioms) do
    tolerance =
      cond do
        axioms <= 100 -> 3.5
        axioms <= 500 -> 2.5
        axioms <= 1000 -> 2.0
        true -> 1.5
      end

    %{tolerance: tolerance, max_size: 1000, max_depth: -1}
  end

  # `guessSineFilterConfig`: configurations 1-50 of Antoine's optimization, by id.
  # Ids 1-25 cap the selection at 200 axioms, 26-50 do not; within each half the
  # depth runs through -1, 1, 2, 3, 5 and the tolerance through 1, 1.5, 2, 3, 5.
  @tolerances [1.0, 1.5, 2.0, 3.0, 5.0]
  @depths [-1, 1, 2, 3, 5]

  # `{internal range, external range, total range, configuration id}`, tried in order.
  @table [
    {402..759, 7014..10723, 7450..11210, 21},
    {34..511, 45455..54878, 45494..55190, 36},
    {3726..4179, 50640..50640, 54366..54819, 6},
    {238..415, 24..4083, 342..4438, 3},
    {1050..1569, 24107..24107, 25157..25676, 40},
    {2247..2766, 50640..50640, 52887..53406, 8},
    {366..935, 48429..54878, 49029..55331, 36},
    {49..421, 31281..37032, 31552..37248, 11},
    {614..991, 12853..18212, 13515..18931, 6},
    {2..278, 15728..20100, 15793..20164, 6},
    {32..652, 36589..42948, 36931..43108, 26},
    {115..342, 3438..6241, 3588..6415, 11},
    {1689..2066, 24107..24107, 25796..26173, 5},
    {139..335, 13306..16189, 13468..16501, 1},
    {149..402, 5435..9047, 5787..9378, 11},
    {1003..1399, 14903..16969, 15907..18362, 6},
    {1..141, 2663..5560, 2701..5597, 13},
    {440..967, 22237..26862, 22694..27536, 36},
    {3310..3671, 50640..50640, 53950..54311, 6},
    {130..386, 9898..12853, 10089..13176, 11},
    {4..175, 8723..11999, 8751..12121, 11},
    {1397..1835, 14903..16969, 16307..18804, 1},
    {303..759, 28944..36069, 29303..36582, 7},
    {34..443, 19346..23601, 19591..24011, 26},
    {281..608, 15728..19346, 16107..19840, 46},
    {2..157, 12280..15838, 12300..15872, 6},
    {2794..3274, 50640..50640, 53434..53914, 37},
    {951..1566, 46764..50640, 47836..52206, 41},
    {768..1150, 4083..9047, 4936..9885, 6},
    {492..796, 1963..5435, 2633..6189, 28},
    {25..309, 26219..31281, 26303..31359, 26},
    {3..135, 7..2468, 39..2563, 1},
    {331..631, 11795..15242, 12183..15659, 1},
    {0..166, 5604..8723, 5631..8738, 13},
    {1627..2231, 43121..50640, 45149..52871, 6},
    {101..271, 7..3058, 145..3234, 12},
    {371..590, 1060..5435, 1488..5915, 23},
    {532..997, 39415..48429, 40118..49340, 7},
    {1203..1605, 39415..43121, 40618..44532, 31}
  ]

  @doc """
  The table entry of `guessSineFilterConfig` for `internal`/`external` axioms, `0`
  (the fallback `default_config/1`) when no row matches.
  """
  @spec table_id(non_neg_integer(), non_neg_integer()) :: 0..50
  def table_id(internal, external) do
    total = internal + external

    Enum.find_value(@table, 0, fn {int, ext, tot, id} ->
      if internal in int and external in ext and total in tot, do: id
    end)
  end

  @doc "Configuration `id` (1-50) of Leo-III's table."
  @spec table_config(1..50) :: config()
  def table_config(id) when id in 1..50 do
    idx = id - 1

    %{
      tolerance: Enum.at(@tolerances, rem(idx, 5)),
      max_size: if(idx < 25, do: 200, else: 999_999_999),
      max_depth: Enum.at(@depths, rem(div(idx, 5), 5))
    }
  end

  @doc """
  Leo-III `guessSineFilterConfig(externalAxioms, internalAxioms)`: the table's
  configuration, or `default_config/1` when no row matches or `standard` is set.
  """
  @spec guess(non_neg_integer(), non_neg_integer(), boolean()) :: config()
  def guess(internal, external, standard \\ false) do
    case table_id(internal, external) do
      id when id == 0 or standard -> default_config(internal + external)
      id -> table_config(id)
    end
  end

  @doc """
  Selects the axioms (Leo-III `getRelevantAxiomsNew` with
  `ThresholdPassFilterConfig(25, config)`). `axioms` are `{name, role, term_id}`
  (role `negated_conjecture` acts as a conjecture and is always kept),
  `conjectures` are `{name, term_id}`, and `defs` maps defined constant term ids to
  their bodies. Returns the selected axioms in input order.
  """
  @spec select(Arena.t(), [axiom()], [{String.t(), Arena.term_id()}], %{}, config()) ::
          [axiom()]
  def select(%Arena{} = arena, axioms, conjectures, defs, config) do
    {seeds, candidates} = Enum.split_with(axioms, fn {_n, role, _id} -> role in @seed_roles end)
    seed_ids = Enum.map(conjectures, &elem(&1, 1)) ++ Enum.map(seeds, &elem(&1, 2))

    if seed_ids == [] or length(candidates) <= @passing_threshold do
      axioms
    else
      kept = run(arena, candidates, seed_ids, defs, config)

      # Candidates are numbered in input order, skipping the seeds.
      {selected, _i} =
        Enum.flat_map_reduce(axioms, 0, fn {_n, role, _id} = ax, i ->
          cond do
            role in @seed_roles -> {[ax], i}
            MapSet.member?(kept, i) -> {[ax], i + 1}
            true -> {[], i + 1}
          end
        end)

      selected
    end
  end

  # `SineFilter.apply`: the indices (in `candidates`) of the selected candidates.
  defp run(arena, candidates, seed_ids, defs, config) do
    def_syms =
      Map.new(defs, fn {const_id, body_id} ->
        {@tag_const, _, _, sym_id, _} = Arena.get_node(arena, const_id)
        {sym_id, RelevanceFilter.symbols(arena, body_id)}
      end)

    seed_syms = Enum.map(seed_ids, &RelevanceFilter.symbols(arena, &1))
    entries = Enum.map(candidates, fn {_n, _r, id} -> RelevanceFilter.symbols(arena, id) end)

    # `SymbolDistribution` over the axioms, definition bodies and conjectures
    occ =
      Enum.reduce(entries ++ Map.values(def_syms) ++ seed_syms, %{}, fn syms, acc ->
        Enum.reduce(syms, acc, fn s, m -> Map.update(m, s, 1, &(&1 + 1)) end)
      end)

    {trigger, special} = trigger_relation(entries, occ, config.tolerance)
    zero = Enum.reduce(seed_syms, MapSet.new(), &MapSet.union/2)
    max_size = min(config.max_size, length(candidates))

    # Like Leo-III, only the symbol-free axioms are kept when the conjectures
    # mention no symbol.
    selected =
      if MapSet.size(zero) == 0 do
        MapSet.new()
      else
        depth = if config.max_depth < 0, do: :infinity, else: config.max_depth

        st = %{
          trigger: trigger,
          def_syms: def_syms,
          entries: List.to_tuple(entries),
          max: max_size
        }

        loop(st, depth, -1, zero, MapSet.new(), MapSet.new())
      end

    MapSet.union(selected, special)
  end

  # `SineSelector.apply` (companion): symbol -> triggered candidate indices, and the
  # candidates without symbols.
  defp trigger_relation(entries, occ, tolerance) do
    entries
    |> Enum.with_index()
    |> Enum.reduce({%{}, MapSet.new()}, fn {syms, idx}, {rel, special} ->
      if MapSet.size(syms) == 0 do
        {rel, MapSet.put(special, idx)}
      else
        local = (syms |> Enum.map(&Map.fetch!(occ, &1)) |> Enum.min()) * tolerance

        rel =
          syms
          |> Enum.filter(&(Map.fetch!(occ, &1) <= local))
          |> Enum.reduce(rel, fn s, m -> Map.update(m, s, [idx], &[idx | &1]) end)

        {rel, special}
      end
    end)
  end

  # `SineSelector.apply` (instance): the stepwise closure under the trigger relation.
  defp loop(st, depth, last_size, k_syms, triggered_syms, triggered) do
    if depth == 0 or MapSet.size(triggered) <= last_size do
      triggered
    else
      fresh = Enum.reject(k_syms, &MapSet.member?(triggered_syms, &1))
      triggered_syms = Enum.reduce(fresh, triggered_syms, &MapSet.put(&2, &1))
      k_axioms = fresh |> Enum.flat_map(&Map.get(st.trigger, &1, [])) |> MapSet.new()
      size = MapSet.size(triggered)

      if size + MapSet.size(k_axioms) > st.max do
        # Leo-III counts and takes `maxSize - size` axioms of this step in hash set
        # order, some of which may already be selected. The count is kept; the
        # unselected ones are taken first, in input order.
        cut =
          k_axioms
          |> Enum.sort_by(&{MapSet.member?(triggered, &1), &1})
          |> Enum.take(max(st.max - size, 0))
          |> MapSet.new()

        MapSet.union(triggered, cut)
      else
        def_syms =
          Enum.reduce(k_syms, MapSet.new(), fn s, acc ->
            MapSet.union(acc, Map.get(st.def_syms, s, MapSet.new()))
          end)

        next_syms =
          Enum.reduce(k_axioms, def_syms, &MapSet.union(elem(st.entries, &1), &2))

        depth = if depth == :infinity, do: depth, else: depth - 1
        loop(st, depth, size, next_syms, triggered_syms, MapSet.union(triggered, k_axioms))
      end
    end
  end
end
