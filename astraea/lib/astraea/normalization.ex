defmodule Astraea.Normalization do
  @moduledoc """
  Leo-III's normalization mode (`leo.modules.modes.Normalization`, run by
  `--processOnly`) and its translation mode (`Modes.toTHF`, run by `--toTHF`):
  a TPTP problem is lowered like `Astraea.Prover.prove_string/2` does, normalized,
  and printed as a THF problem for other provers.

  Every formula is beta-eta normalized and simplified
  (`Astraea.Calculus.Simplification`), miniscoped (`Astraea.Calculus.Miniscope`)
  and its logical arguments are extracted (`Astraea.Calculus.ArgumentExtraction`).
  With `cnf: true`, assumptions are clausified first
  (`Astraea.Calculus.RenameCnf`, with formula renaming and the `BoolExt`/`FuncExt`
  expansions) and the arguments are extracted from the clauses. As in Leo-III the
  conjecture is kept as a formula with role `conjecture` (never clausified), and
  the definitions introduced by extraction are normalized again, until no argument
  is left to extract (each round only sees proper subterms of the previous one).

  ## Equisatisfiability

  The output is equisatisfiable with the input, and when the input has a
  conjecture `C` and assumptions `Ax`, `Ax' + ~C'` is equisatisfiable with
  `Ax + ~C`, so the SZS status (Theorem, CounterSatisfiable, ...) is preserved:

    * simplification, miniscoping, NNF, distribution and the extensionality
      expansions are equivalences in extensional Henkin semantics (TPTP THF);
    * argument extraction and formula renaming add definitions of fresh symbols,
      a conservative extension, and replace a subterm by its definiendum, which is
      equivalent under the definition (renaming keeps one implication only, which
      still entails the original formula);
    * Skolemization of assumptions introduces fresh symbols for witnesses; the
      conjecture is not Skolemized, so the symbols do not occur in it.

  All introduced symbols (`sk_`, `def_`, `xarg_`) are content-addressed (derived
  from the formula they stand for, without counters), so equal subformulas share
  one symbol whose interpretation above is the same everywhere. "Fresh" is
  checked: the run fails if the input already uses a symbol of that shape, or if
  two different introduced symbols would print alike (hash collision).

  This argument is about the lowered problem. If lowering is not faithful
  (bounded monomorphization, modal embeddings, uninterpreted arithmetic beyond
  ground evaluation, choice, see `Astraea.Prover`), the output need not be
  equisatisfiable with the original TPTP text, so normalization refuses such
  input unless `allow_incomplete: true` (then the caveats are printed as comments).
  Unlike `Astraea.Clausifier`, nothing is filtered (no SInE) or truncated: a
  formula whose CNF exceeds `:max_clauses` is an error.

  Deviations from Leo-III: `definition` statements are emitted as axioms (their
  normal form need not be `c = t` any more), Leo-III's `LiftEq` is a no-op on the
  arena (equations are already atoms), and `xType 2` extracts lambda
  abstractions where Leo-III is unimplemented.
  """

  alias Astraea.{Arena, TptpLower}
  alias Astraea.Calculus.{ArgumentExtraction, Miniscope, RenameCnf, Simplification}
  alias Astraea.External.ThfPrinter
  alias Astraea.Input.Elaborator

  @tag_skolem 10

  # Fragments whose lowering is faithful in both directions (see `Astraea.Prover`).
  @model_faithful_fragments [:thf, :tff, :fof, :cnf, :ite, :let, :distinct]

  @generated ~r/^(sk_[0-9a-f]{8}|(def|xarg)_[0-9a-f]{16})$/

  @typedoc "A normalized statement: a closed formula or a clause."
  @type entry ::
          {name :: String.t(), role :: String.t(),
           {:formula, Arena.term_id()} | {:clause, Astraea.ProofChecker.clause()}}

  @type result :: %{arena: Arena.t(), entries: [entry()], caveats: [String.t()]}

  @doc """
  Lowers and normalizes the TPTP `source` (see `normalize_lowered/2`). Lowering
  options (`:tptp_root`, `:monomorphization`) are passed to `Astraea.TptpLower`.
  """
  @spec normalize_string(String.t(), keyword()) :: {:ok, String.t()} | {:error, term()}
  def normalize_string(source, opts \\ []) do
    with {:ok, lowered} <- TptpLower.from_string(source, opts),
         do: normalize_lowered(lowered, opts)
  end

  @doc "Lowers and normalizes the TPTP file at `path` (see `normalize_lowered/2`)."
  @spec normalize_file(Path.t(), keyword()) :: {:ok, String.t()} | {:error, term()}
  def normalize_file(path, opts \\ []) do
    with {:ok, lowered} <- TptpLower.from_file(path, opts), do: normalize_lowered(lowered, opts)
  end

  @doc """
  Normalizes a lowered problem and renders it as THF (see `normalize/2` for the
  options).
  """
  @spec normalize_lowered(TptpLower.t(), keyword()) :: {:ok, String.t()} | {:error, term()}
  def normalize_lowered(%TptpLower{} = lowered, opts \\ []) do
    with {:ok, result} <- normalize(lowered, opts), do: {:ok, render(result, lowered, opts)}
  end

  @doc """
  Normalizes a lowered problem. Options (Leo-III flag in parentheses):
    * `:cnf` - clausify the assumptions (`--cnf`, default `false`)
    * `:renaming` - formula renaming threshold for `:cnf`, `false` disables it
      (`--renaming N`, default `0`)
    * `:extraction` - `:boolean`, `:predicate`, `:function` (or 0, 1, 2), or
      `false` to disable (`--xType N`, default `:predicate`)
    * `:extract_local` - also extract terms with bound variables (`--xLocal`,
      default `false`)
    * `:extensionality` - `BoolExt`/`FuncExt` expansion in `:cnf` (default `true`)
    * `:max_clauses` - per formula, see `Astraea.Calculus.RenameCnf` (default 10000)
    * `:allow_incomplete` - accept input whose lowering is not faithful (default
      `false`)
  """
  @spec normalize(TptpLower.t(), keyword()) :: {:ok, result()} | {:error, term()}
  def normalize(%TptpLower{} = lowered, opts \\ []) do
    with {:ok, caveats} <- check_input(lowered, opts) do
      st = %{
        arena: lowered.arena,
        cnf: Keyword.get(opts, :cnf, false),
        rename_opts: [
          renaming: Keyword.get(opts, :renaming, 0),
          extensionality: Keyword.get(opts, :extensionality, true),
          max_clauses: Keyword.get(opts, :max_clauses, 10_000)
        ],
        extract_opts: extract_opts(opts),
        defined: MapSet.new(),
        extracted: MapSet.new(),
        entries: []
      }

      st =
        Enum.reduce(lowered.axioms, st, fn {name, role, id}, st ->
          process(st, name, output_role(role), id, st.cnf)
        end)

      st =
        Enum.reduce(lowered.conjectures, st, fn {name, id}, st ->
          process(st, name, "conjecture", id, false)
        end)

      result = %{arena: st.arena, entries: Enum.reverse(st.entries), caveats: caveats}
      with :ok <- check_collisions(result), do: {:ok, result}
    end
  catch
    {:normalization_error, reason} -> {:error, reason}
  end

  @doc """
  Leo-III's `--toTHF`: the lowered problem printed as THF without normalization.
  """
  @spec to_thf(TptpLower.t()) :: String.t()
  def to_thf(%TptpLower{} = lowered) do
    entries =
      Enum.map(lowered.axioms, fn {name, role, id} ->
        {name, output_role(role), {:formula, id}}
      end) ++
        Enum.map(lowered.conjectures, fn {name, id} -> {name, "conjecture", {:formula, id}} end)

    render(%{arena: lowered.arena, entries: entries, caveats: []}, lowered, header: "toTHF")
  end

  @doc """
  Renders a `normalize/2` result as a THF problem: `$tType` declarations for the
  base types, type declarations for the input signature and every introduced
  symbol, then the statements in order. Clauses are universally closed.
  """
  @spec render(result(), TptpLower.t(), keyword()) :: String.t()
  def render(
        %{arena: arena, entries: entries, caveats: caveats},
        %TptpLower{} = lowered,
        opts \\ []
      ) do
    {body, syms} =
      Enum.map_reduce(entries, MapSet.new(), fn {name, role, item}, syms ->
        {text, syms} =
          case item do
            {:formula, id} -> ThfPrinter.formula(arena, id, syms)
            {:clause, clause} -> ThfPrinter.clause(arena, clause, syms)
          end

        {["thf(", ThfPrinter.atom(name), ", ", role, ", ", text, ").\n"], syms}
      end)

    input_syms =
      for {name, ty} <- lowered.const_types,
          not String.starts_with?(name, "$"),
          into: MapSet.new(),
          do: {name, ty}

    IO.iodata_to_binary([
      header(opts),
      Enum.map(caveats, &["% Caveat: ", &1, "\n"]),
      type_decls(arena),
      symbol_decls(arena, MapSet.union(syms, input_syms)),
      body
    ])
  end

  # ---------------------------------------------------------------------------
  # Pipeline
  # ---------------------------------------------------------------------------

  defp process(st, name, role, term_id, clausal?) do
    {arena, t} = Simplification.apply(st.arena, term_id)
    {arena, t} = Miniscope.apply(arena, t)
    st = %{st | arena: arena}

    {st, items, defs} = if clausal?, do: clauses(st, name, t), else: formula(st, t)

    st = %{st | entries: emit(items, name, role, st.arena, st.entries)}

    Enum.reduce(defs, st, fn {const, def_formula}, st ->
      if MapSet.member?(st.extracted, const) do
        st
      else
        st = %{st | extracted: MapSet.put(st.extracted, const)}
        process(st, const_name(st.arena, const), "axiom", def_formula, st.cnf)
      end
    end)
  end

  defp formula(st, t) do
    case st.extract_opts do
      nil ->
        {st, [{:formula, t}], []}

      opts ->
        {arena, t, defs} = ArgumentExtraction.apply(st.arena, t, opts)
        {%{st | arena: arena}, [{:formula, t}], defs}
    end
  end

  defp clauses(st, name, t) do
    case RenameCnf.clausify(st.arena, t, [defined: st.defined] ++ st.rename_opts) do
      {:ok, arena, clauses, defined} ->
        st = %{st | arena: arena, defined: defined}

        {items, {arena, defs}} =
          Enum.map_reduce(clauses, {st.arena, []}, fn clause, {ar, acc} ->
            case st.extract_opts do
              nil ->
                {{:clause, clause}, {ar, acc}}

              opts ->
                {ar, clause, defs} = ArgumentExtraction.apply_clause(ar, clause, opts)
                {{:clause, clause}, {ar, acc ++ defs}}
            end
          end)

        {%{st | arena: arena}, items, Enum.uniq(defs)}

      {:error, reason} ->
        throw({:normalization_error, {reason, name}})
    end
  end

  # Statements simplified to `$true` are dropped, except conjectures.
  defp emit(items, name, role, arena, acc) do
    items =
      Enum.reject(items, fn
        {:formula, id} -> role != "conjecture" and Arena.truth_const?(arena, id, "$true")
        {:clause, _} -> false
      end)

    case items do
      [single] ->
        [{name, role, single} | acc]

      _ ->
        items
        |> Enum.with_index(1)
        |> Enum.reduce(acc, fn {item, i}, acc -> [{"#{name}_#{i}", role, item} | acc] end)
    end
  end

  defp extract_opts(opts) do
    case Keyword.get(opts, :extraction, :predicate) do
      false -> nil
      type -> [type: type, local: Keyword.get(opts, :extract_local, false)]
    end
  end

  defp output_role(role) do
    case Elaborator.base_role(role) do
      "definition" -> "axiom"
      base -> base
    end
  end

  defp const_name(arena, const) do
    {_tag, _flags, _ty, sym, _} = Arena.get_node(arena, const)
    Map.fetch!(arena.symbol_names, sym)
  end

  # ---------------------------------------------------------------------------
  # Checks
  # ---------------------------------------------------------------------------

  defp check_input(%TptpLower{} = lowered, opts) do
    clashes = lowered.arena.symbols |> Map.keys() |> Enum.filter(&Regex.match?(@generated, &1))

    caveats =
      Enum.map(lowered.incomplete, &"incomplete lowering: #{inspect(&1)}") ++
        (lowered.fragments
         |> Enum.reject(&(&1 in @model_faithful_fragments))
         |> Enum.map(&"fragment #{&1} is not lowered faithfully"))

    cond do
      clashes != [] -> {:error, {:reserved_symbols, Enum.sort(clashes)}}
      caveats == [] or Keyword.get(opts, :allow_incomplete, false) -> {:ok, caveats}
      true -> {:error, {:unfaithful_input, caveats}}
    end
  end

  # Introduced symbols must print to distinct names: Skolem names carry a 32-bit
  # hash, so two Skolem nodes for different formulas could print alike.
  defp check_collisions(%{arena: arena}) do
    skolems =
      arena.nodes
      |> Map.values()
      |> Enum.flat_map(fn packed ->
        case Arena.decode_node(packed) do
          {@tag_skolem, _, _ty, hash, phi} -> [{hash, phi}]
          _ -> []
        end
      end)
      |> Enum.group_by(&elem(&1, 0), &elem(&1, 1))
      |> Enum.filter(fn {_hash, phis} -> length(Enum.uniq(phis)) > 1 end)

    if skolems == [],
      do: :ok,
      else: {:error, {:skolem_collision, Enum.map(skolems, &elem(&1, 0))}}
  end

  # ---------------------------------------------------------------------------
  # Rendering
  # ---------------------------------------------------------------------------

  defp header(opts) do
    mode = Keyword.get(opts, :header, "processOnly")

    settings =
      [:cnf, :renaming, :extraction, :extract_local]
      |> Enum.filter(&Keyword.has_key?(opts, &1))
      |> Enum.map_join(", ", fn k -> "#{k}: #{inspect(Keyword.fetch!(opts, k))}" end)

    [
      "% Generated by Astraea.Normalization (Leo-III --",
      mode,
      ")",
      if(settings == "", do: "", else: [" ", settings]),
      "\n"
    ]
  end

  defp type_decls(arena) do
    arena.type_table
    |> Enum.flat_map(fn
      {_id, {:base, name}} -> if String.starts_with?(name, "$"), do: [], else: [name]
      _ -> []
    end)
    |> Enum.sort()
    |> Enum.with_index()
    |> Enum.map(fn {name, idx} ->
      ["thf(decl_ty_", Integer.to_string(idx), ", type, ", ThfPrinter.atom(name), ": $tType).\n"]
    end)
  end

  defp symbol_decls(arena, syms) do
    by_name = Enum.group_by(syms, &elem(&1, 0), &elem(&1, 1))

    case Enum.find(by_name, fn {_name, tys} -> length(tys) > 1 end) do
      nil -> :ok
      {name, _} -> raise ArgumentError, "symbol #{name} printed with several types"
    end

    syms
    |> Enum.sort()
    |> Enum.with_index()
    |> Enum.map(fn {{name, ty}, idx} ->
      [
        "thf(decl_sym_",
        Integer.to_string(idx),
        ", type, ",
        ThfPrinter.atom(name),
        ": ",
        ThfPrinter.type(arena, ty),
        ").\n"
      ]
    end)
  end
end
