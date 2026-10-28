defmodule Astraea.ProblemStatistics do
  @moduledoc """
  Problem statistics, after Leo-III's `leo.modules.input.ProblemStatistics`.

  Leo-III counts, while parsing, the `include` directives of the problem file, the
  formulas stated in it (`immediate`) and those it includes, and, while
  preprocessing, the `axiom`/`hypothesis` formulas of either origin. It uses the
  axiom counts to pick a SInE configuration (`guessSineFilterConfig`). The same
  counts come from a `Tptp.Unit` here (`from_unit/1`; `formulas/1` and `axioms/1`
  are Leo-III's sums).

  `from_lowered/2` adds what the lowered problem (`Astraea.TptpLower`) shows:
  assumptions, conjectures and definitions, roles, the signature (base types,
  uninterpreted symbols, highest symbol order), the language fragments, and the
  total tree size, depth and number of quantifiers, lambdas and equations of the
  formulas. `from_file/2` and `from_string/2` compute both.
  """

  alias Astraea.{Arena, TptpLower}
  alias Tptp.Statement.{Annotated, Include}

  # Node tags (u8) matching `Astraea.Arena`
  @tag_app 4
  @tag_lam 5
  @tag_eq 6
  @tag_not 7
  @tag_or 8
  @tag_forall 9

  defstruct includes: 0,
            immediate_formulas: 0,
            included_formulas: 0,
            local_axioms: 0,
            included_axioms: 0,
            assumptions: 0,
            conjectures: 0,
            definitions: 0,
            roles: %{},
            base_types: 0,
            symbols: 0,
            max_order: 0,
            higher_order: false,
            size: 0,
            max_depth: 0,
            quantifiers: 0,
            lambdas: 0,
            equations: 0,
            fragments: [],
            incomplete: []

  @type t :: %__MODULE__{}

  @doc "Formulas of the problem file and its includes (Leo-III `formulas`)."
  @spec formulas(t()) :: non_neg_integer()
  def formulas(%__MODULE__{} = s), do: s.immediate_formulas + s.included_formulas

  @doc "Axioms and hypotheses of either origin (Leo-III `axioms`)."
  @spec axioms(t()) :: non_neg_integer()
  def axioms(%__MODULE__{} = s), do: s.local_axioms + s.included_axioms

  @doc """
  Parses and lowers `path` (expanding includes from `:tptp_root`) and returns the
  statistics of both stages.
  """
  @spec from_file(Path.t(), keyword()) :: {:ok, t()} | {:error, term()}
  def from_file(path, opts \\ []) do
    path |> Tptp.Unit.from_file(resolver: resolver(opts), max_concurrency: 1) |> parsed(opts)
  end

  @doc "As `from_file/2`, for TPTP source text."
  @spec from_string(String.t(), keyword()) :: {:ok, t()} | {:error, term()}
  def from_string(source, opts \\ []) do
    source |> Tptp.Unit.from_string(resolver: resolver(opts), max_concurrency: 1) |> parsed(opts)
  end

  defp resolver(opts) do
    {Tptp.Resolver.Fs,
     root: Keyword.get(opts, :tptp_root, Astraea.TptpCorpus.default_tptp_root())}
  end

  defp parsed({:ok, unit, diagnostics}, opts) do
    case Enum.filter(diagnostics, &(&1.severity == :error)) do
      [] ->
        with {:ok, lowered} <- TptpLower.lower_unit(unit, opts),
             do: {:ok, from_lowered(lowered, from_unit(unit))}

      errors ->
        {:error, {:parse, Enum.map(errors, & &1.message)}}
    end
  end

  defp parsed({:error, _} = err, _opts), do: err

  @doc """
  Leo-III's parse-time counts: includes of the root file, formulas of the root
  file and of the included files (after include selection), and the `axiom` and
  `hypothesis` formulas among them.
  """
  @spec from_unit(Tptp.Unit.t(), t()) :: t()
  def from_unit(%Tptp.Unit{} = unit, %__MODULE__{} = stats \\ %__MODULE__{}) do
    root = Map.fetch!(unit.files, unit.root)

    {local, included} =
      unit |> Tptp.Unit.formulae() |> Enum.split_with(fn {id, _} -> id == unit.root end)

    %{
      stats
      | includes: Enum.count(root.statements, &match?(%Include{}, &1)),
        immediate_formulas: length(local),
        included_formulas: length(included),
        local_axioms: Enum.count(local, &axiom?/1),
        included_axioms: Enum.count(included, &axiom?/1)
    }
  end

  defp axiom?({_id, %Annotated{} = st}), do: Annotated.role_word(st) in ["axiom", "hypothesis"]

  @doc """
  Statistics of a lowered problem (see the module documentation), added to `stats`.
  """
  @spec from_lowered(TptpLower.t(), t()) :: t()
  def from_lowered(%TptpLower{} = lowered, %__MODULE__{} = stats \\ %__MODULE__{}) do
    arena = lowered.arena
    roots = Enum.map(lowered.axioms, &elem(&1, 2)) ++ Enum.map(lowered.conjectures, &elem(&1, 1))

    {_memo, metrics} =
      Enum.reduce(roots, {%{}, %{size: 0, depth: 0, foralls: 0, lams: 0, eqs: 0}}, fn id,
                                                                                      {memo, acc} ->
        {memo, m} = metrics(arena, id, memo)

        {memo,
         %{
           size: acc.size + m.size,
           depth: max(acc.depth, m.depth),
           foralls: acc.foralls + m.foralls,
           lams: acc.lams + m.lams,
           eqs: acc.eqs + m.eqs
         }}
      end)

    user_symbols =
      Enum.reject(lowered.const_types, fn {name, _ty} -> String.starts_with?(name, "$") end)

    max_order =
      user_symbols |> Enum.map(fn {_n, ty} -> order(arena, ty) end) |> Enum.max(fn -> 0 end)

    base_types =
      Enum.count(arena.type_table, fn
        {_id, {:base, name}} -> not String.starts_with?(name, "$")
        _ -> false
      end)

    roles =
      Enum.frequencies(
        Enum.map(lowered.axioms, &elem(&1, 1)) ++
          Enum.map(lowered.conjectures, fn _ -> "conjecture" end)
      )

    %{
      stats
      | assumptions: length(lowered.axioms),
        conjectures: length(lowered.conjectures),
        definitions: length(lowered.definitions),
        roles: roles,
        base_types: base_types,
        symbols: length(user_symbols),
        max_order: max_order,
        higher_order: max_order > 1 or metrics.lams > 0 or ho_quantifier?(arena, roots),
        size: metrics.size,
        max_depth: metrics.depth,
        quantifiers: metrics.foralls,
        lambdas: metrics.lams,
        equations: metrics.eqs,
        fragments: lowered.fragments,
        incomplete: lowered.incomplete
    }
  end

  @doc """
  Renders `stats` as TPTP comment lines (`% key: value`).
  """
  @spec to_comment(t()) :: String.t()
  def to_comment(%__MODULE__{} = stats) do
    fields = [
      formulas: formulas(stats),
      includes: stats.includes,
      included_formulas: stats.included_formulas,
      axioms: axioms(stats),
      local_axioms: stats.local_axioms,
      included_axioms: stats.included_axioms,
      assumptions: stats.assumptions,
      conjectures: stats.conjectures,
      definitions: stats.definitions,
      base_types: stats.base_types,
      symbols: stats.symbols,
      max_order: stats.max_order,
      higher_order: stats.higher_order,
      size: stats.size,
      max_depth: stats.max_depth,
      quantifiers: stats.quantifiers,
      lambdas: stats.lambdas,
      equations: stats.equations,
      fragments: Enum.join(stats.fragments, ",")
    ]

    Enum.map_join(fields, fn {k, v} -> "% #{k}: #{v}\n" end)
  end

  # Tree metrics of `id`, memoized per hash-consed node.
  defp metrics(arena, id, memo) do
    case Map.fetch(memo, id) do
      {:ok, m} ->
        {memo, m}

      :error ->
        {tag, _flags, _ty, left, right} = Arena.get_node(arena, id)

        children =
          case tag do
            t when t in [@tag_app, @tag_eq, @tag_or] -> [left, right]
            @tag_not -> [left]
            t when t in [@tag_lam, @tag_forall] -> [right]
            _ -> []
          end

        {kids, memo} =
          Enum.map_reduce(children, memo, fn c, memo -> swap(metrics(arena, c, memo)) end)

        m = %{
          size: 1 + sum(kids, :size),
          depth: 1 + Enum.max(Enum.map(kids, & &1.depth), fn -> 0 end),
          foralls: sum(kids, :foralls) + if(tag == @tag_forall, do: 1, else: 0),
          lams: sum(kids, :lams) + if(tag == @tag_lam, do: 1, else: 0),
          eqs: sum(kids, :eqs) + if(tag == @tag_eq, do: 1, else: 0)
        }

        {Map.put(memo, id, m), m}
    end
  end

  defp swap({a, b}), do: {b, a}

  defp sum(kids, key), do: kids |> Enum.map(&Map.fetch!(&1, key)) |> Enum.sum()

  # Quantification over `$o` or a function type.
  defp ho_quantifier?(arena, roots) do
    Enum.any?(roots, &ho_quantifier_in?(arena, &1))
  end

  defp ho_quantifier_in?(arena, id) do
    {tag, _flags, _ty, left, right} = Arena.get_node(arena, id)

    case tag do
      @tag_forall ->
        ho_domain?(arena, left) or
          ho_quantifier_in?(arena, right)

      @tag_lam ->
        ho_quantifier_in?(arena, right)

      @tag_not ->
        ho_quantifier_in?(arena, left)

      t when t in [@tag_app, @tag_eq, @tag_or] ->
        ho_quantifier_in?(arena, left) or ho_quantifier_in?(arena, right)

      _ ->
        false
    end
  end

  # `$o` or a function type (`$i` and user base types are first-order domains).
  defp ho_domain?(arena, ty) do
    case Map.fetch!(arena.type_table, ty) do
      :o -> true
      {:arrow, _, _} -> true
      _ -> false
    end
  end

  # Order of a type: 0 for base types, `max(order(dom) + 1, order(cod))` for arrows.
  defp order(arena, ty) do
    case Map.fetch!(arena.type_table, ty) do
      {:arrow, dom, cod} -> max(order(arena, dom) + 1, order(arena, cod))
      _ -> 0
    end
  end
end
