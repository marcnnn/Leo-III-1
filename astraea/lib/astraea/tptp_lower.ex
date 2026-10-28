defmodule Astraea.TptpLower do
  @moduledoc """
  Lowers TPTP problems (parsed with `{:tptp, "~> 0.3.0"}`) into the flat 12-byte
  `Astraea.Arena` IR, resolving transitive `include('Axioms/...')` directives.

  The input pipeline lives in `Astraea.Input`:

    1. `Astraea.Input.Elaborator` type-checks THF, TFF, FOF and CNF statements into
       a named IR (TH1 polymorphism, arithmetic, choice, `$let`, `$ite`, tuples),
    2. `Astraea.Input.Modal` embeds modal problems (`logic` statements) into HOL,
    3. `Astraea.Input.Monomorphizer` instantiates polymorphic assumptions,
    4. `Astraea.Input.Emitter` interns the result as de Bruijn arena terms, and
    5. `Astraea.Input.Arith` evaluates ground arithmetic.

  Lowering is trusted: input it cannot translate faithfully (including statements
  the parser reports errors for) yields `{:error, reason}` instead of an
  approximation. A problem whose translation is sound but incomplete (bounded
  monomorphization) lists the reasons in `:incomplete`; `:fragments` names the
  language features the problem uses.

  Roles: `conjecture`s go to `:conjectures` (several are conjoined into one, as
  all of them have to be proved), everything else that states a formula, including
  `negated_conjecture`, is an assumption in `:axioms`.
  """

  alias Astraea.Arena
  alias Astraea.Input.{Arith, Elaborator, Emitter, IR, Modal, Monomorphizer}

  defstruct arena: Arena.new(),
            base_types: %{
              "$o" => Arena.ty_o(),
              "$oType" => Arena.ty_o(),
              "$i" => Arena.ty_i(),
              "$iType" => Arena.ty_i()
            },
            const_types: %{},
            axioms: [],
            conjectures: [],
            definitions: [],
            incomplete: [],
            fragments: [],
            axiom_counts: nil

  @type t :: %__MODULE__{
          arena: Arena.t(),
          base_types: %{String.t() => Arena.type_id()},
          const_types: %{String.t() => Arena.type_id()},
          axioms: [{String.t(), String.t(), Arena.term_id()}],
          conjectures: [{String.t(), Arena.term_id()}],
          definitions: [{String.t(), Arena.term_id()}],
          incomplete: [term()],
          fragments: [atom()],
          axiom_counts: {non_neg_integer(), non_neg_integer()} | nil
        }

  @doc """
  Loads a TPTP file (expanding `include`s from `tptp_root`) and lowers all
  statements into an `Astraea.Arena`. Options: `:tptp_root`, and `:monomorphization`
  (keyword list for `Astraea.Input.Monomorphizer.run/2`).
  """
  @spec from_file(Path.t(), keyword()) :: {:ok, t()} | {:error, term()}
  def from_file(path, opts \\ []) do
    path
    |> Tptp.Unit.from_file(resolver: resolver(opts), max_concurrency: 1)
    |> parsed(opts)
  end

  @spec from_string(String.t(), keyword()) :: {:ok, t()} | {:error, term()}
  def from_string(source, opts \\ []) do
    source
    |> Tptp.Unit.from_string(resolver: resolver(opts), max_concurrency: 1)
    |> parsed(opts)
  end

  defp resolver(opts) do
    tptp_root = Keyword.get(opts, :tptp_root, Astraea.TptpCorpus.default_tptp_root())
    {Tptp.Resolver.Fs, root: tptp_root}
  end

  defp parsed({:ok, unit, diagnostics}, opts) do
    case Enum.filter(diagnostics, &(&1.severity == :error)) do
      [] -> lower_unit(unit, opts)
      errors -> {:error, {:parse, Enum.map(errors, & &1.message)}}
    end
  end

  defp parsed({:error, _} = err, _opts), do: err

  @spec lower_unit(Tptp.Unit.t(), keyword()) :: {:ok, t()} | {:error, term()}
  def lower_unit(%Tptp.Unit{} = unit, opts \\ []) do
    {stmts, ctx} =
      unit |> Tptp.Unit.statements() |> Enum.map(&elem(&1, 1)) |> Elaborator.elaborate()

    {logic, stmts} = Enum.split_with(stmts, &match?({:logic, _}, &1))

    stmts =
      case logic do
        [] ->
          stmts

        [{:logic, spec}] ->
          {stmts, _next_id} = Modal.embed(stmts, Modal.parse_spec(spec), ctx.next_id)
          stmts

        _ ->
          IR.reject!("several logic specifications")
      end

    {stmts, incomplete} = Monomorphizer.run(stmts, Keyword.get(opts, :monomorphization, []))
    fragments = ctx.features |> MapSet.to_list() |> Enum.sort()
    # Axioms of the problem file and of its includes, for Leo-III's SInE
    # configuration table (`Astraea.Sine`).
    stats = Astraea.ProblemStatistics.from_unit(unit)
    lowered = emit(stmts, incomplete, fragments)
    {:ok, %{lowered | axiom_counts: {stats.local_axioms, stats.included_axioms}}}
  rescue
    e -> {:error, Exception.message(e)}
  end

  defp emit(stmts, incomplete, fragments) do
    state = seed_builtins(%__MODULE__{})
    em = Emitter.new(state.arena, state.base_types, state.const_types)

    {em, acc} =
      Enum.reduce(stmts, {em, %{axioms: [], conjectures: [], definitions: []}}, fn
        {:sort, name}, {em, acc} ->
          {Emitter.sort(em, name), acc}

        {:decl, name, ty}, {em, acc} ->
          {Emitter.decl(em, name, ty), acc}

        {:formula, name, role, [], ir}, {em, acc} ->
          {em, id} = Emitter.formula(em, ir)
          {em, classify(acc, name, role, id)}
      end)

    {em, acc} =
      em
      |> Emitter.definitions()
      |> Enum.reduce({em, acc}, fn {name, ir}, {em, acc} ->
        {em, id} = Emitter.formula(em, ir)
        {em, classify(acc, name, "axiom", id)}
      end)

    {arena, acc} = if :arith in fragments, do: evaluate(em.arena, acc), else: {em.arena, acc}
    {arena, conjectures} = conjoin(arena, Enum.reverse(acc.conjectures))

    %{
      state
      | arena: arena,
        base_types: em.base_types,
        const_types: em.const_types,
        axioms: Enum.reverse(acc.axioms),
        conjectures: conjectures,
        definitions: Enum.reverse(acc.definitions),
        incomplete: incomplete,
        fragments: fragments
    }
  end

  defp classify(acc, name, role, id) do
    case Elaborator.base_role(role) do
      "conjecture" ->
        %{acc | conjectures: [{name, id} | acc.conjectures]}

      "definition" ->
        %{
          acc
          | axioms: [{name, "definition", id} | acc.axioms],
            definitions: [{name, id} | acc.definitions]
        }

      _ ->
        %{acc | axioms: [{name, role, id} | acc.axioms]}
    end
  end

  # Ground arithmetic evaluation of the input formulas (see `Astraea.Input.Arith`).
  defp evaluate(arena, acc) do
    {axioms, arena} =
      Enum.map_reduce(acc.axioms, arena, fn {n, r, id}, ar ->
        {ar, id} = Arith.eval(ar, id)
        {{n, r, id}, ar}
      end)

    {conjectures, arena} =
      Enum.map_reduce(acc.conjectures, arena, fn {n, id}, ar ->
        {ar, id} = Arith.eval(ar, id)
        {{n, id}, ar}
      end)

    {arena, %{acc | axioms: axioms, conjectures: conjectures}}
  end

  defp conjoin(arena, conjectures) when length(conjectures) < 2, do: {arena, conjectures}

  defp conjoin(arena, [{n, id} | rest]) do
    {arena, {names, conj}} =
      Enum.reduce(rest, {arena, {[n], id}}, fn {n2, id2}, {ar, {names, acc}} ->
        {ar, both} = Arena.mk_and(ar, acc, id2)
        {ar, {[n2 | names], both}}
      end)

    {arena, [{names |> Enum.reverse() |> Enum.join("&"), conj}]}
  end

  defp seed_builtins(%__MODULE__{arena: arena} = state) do
    {arena, _true_id} = Arena.mk_const(arena, "$true", :o)
    {arena, _false_id} = Arena.mk_const(arena, "$false", :o)

    %{
      state
      | arena: arena,
        const_types: %{
          "$true" => Arena.ty_o(),
          "$false" => Arena.ty_o()
        }
    }
  end
end
