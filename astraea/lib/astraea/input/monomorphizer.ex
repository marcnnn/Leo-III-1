defmodule Astraea.Input.Monomorphizer do
  @moduledoc """
  Heuristic monomorphization of TH1/TF1 problems, after Leo-III's
  `Monomorphization` (and the Sledgehammer/Why3 schemes it follows).

  Polymorphic assumptions (statements with schematic type variables) are not
  emitted themselves. Instead, the ground instances `c<T1,...,Tn>` of polymorphic
  constants occurring in the monomorphic part are matched against the polymorphic
  occurrences `c<S1,...,Sn>` in each schematic statement; every type each variable
  receives this way is a candidate, and the statement is instantiated with all
  combinations of candidates. The new instances may mention further ground
  instances, so this is iterated up to a fixpoint.

  Instances of assumptions are consequences of them, so the result is sound. It is
  incomplete in general: a variable that never receives a candidate leaves its
  statement unused, and the iteration is bounded by `:rounds` (default 3), at most
  `:per_statement` (default 64) new instances per statement and round, and
  `:max_instances` (default 1000) in total. Hitting a bound is reported, so that
  callers know the run is incomplete.
  """

  alias Astraea.Input.IR

  @defaults [rounds: 3, per_statement: 64, max_instances: 1000]

  @doc """
  Replaces the schematic statements in `stmts` by their instances. Returns the new
  statement list and the list of bounds that cut the instantiation short.
  """
  @spec run([tuple()], keyword()) :: {[tuple()], [{:monomorphization, atom()}]}
  def run(stmts, opts \\ []) do
    opts = @defaults |> Keyword.merge(opts) |> Map.new()

    {poly, mono} =
      Enum.split_with(stmts, &match?({:formula, _, _, [_ | _], _}, &1))

    if poly == [] do
      {stmts, []}
    else
      schemas = Enum.map(poly, &schema/1)
      known = mono |> Enum.flat_map(&formula_instances/1) |> Enum.reduce(%{}, &add_instance/2)
      state = %{known: known, done: MapSet.new(), out: [], count: 0, cut: MapSet.new()}
      state = rounds(schemas, state, known != %{}, 1, opts)
      cut = state.cut |> Enum.sort() |> Enum.map(&{:monomorphization, &1})
      {mono ++ Enum.reverse(state.out), cut}
    end
  end

  defp schema({:formula, name, role, tvars, ir}) do
    patterns =
      ir
      |> IR.reduce([], fn
        {:const, c, [_ | _] = args, _}, acc ->
          if Enum.all?(args, &IR.ground?/1), do: acc, else: [{c, args} | acc]

        _, acc ->
          acc
      end)
      |> Enum.uniq()

    %{name: name, role: role, tvars: tvars, ir: ir, patterns: patterns}
  end

  defp rounds(_schemas, state, false, _round, _opts), do: state

  defp rounds(_schemas, state, true, round, %{rounds: max}) when round > max do
    %{state | cut: MapSet.put(state.cut, :round_limit)}
  end

  defp rounds(schemas, state, true, round, opts) do
    before = state.known

    state =
      Enum.reduce(schemas, state, fn schema, state ->
        schema
        |> substitutions(state.known)
        |> Stream.reject(&MapSet.member?(state.done, {schema.name, &1}))
        |> limit(state, opts)
        |> then(fn {substs, state} ->
          Enum.reduce(substs, state, &instantiate(schema, &1, &2))
        end)
      end)

    rounds(schemas, state, state.known != before, round + 1, opts)
  end

  defp limit(substs, state, opts) do
    room = max(min(opts.per_statement, opts.max_instances - state.count), 0)
    substs = Enum.take(substs, room + 1)

    cond do
      length(substs) <= room ->
        {substs, state}

      room < opts.per_statement ->
        {Enum.take(substs, room), %{state | cut: MapSet.put(state.cut, :instance_limit)}}

      true ->
        {Enum.take(substs, room), %{state | cut: MapSet.put(state.cut, :statement_limit)}}
    end
  end

  # All combinations of the candidate types of each schematic variable, lazily.
  defp substitutions(schema, known) do
    candidates =
      for {c, pargs} <- schema.patterns,
          args <- Map.get(known, c, []),
          reduce: %{} do
        acc ->
          case match_all(pargs, args, %{}) do
            :error ->
              acc

            s ->
              Enum.reduce(s, acc, fn {v, ty}, acc ->
                Map.update(acc, v, MapSet.new([ty]), &MapSet.put(&1, ty))
              end)
          end
      end

    if Enum.all?(schema.tvars, &Map.has_key?(candidates, &1)) do
      Enum.reduce(schema.tvars, [%{}], fn var, substs ->
        tys = Enum.sort(candidates[var])
        Stream.flat_map(substs, fn s -> Stream.map(tys, &Map.put(s, var, &1)) end)
      end)
    else
      []
    end
  end

  defp instantiate(schema, s, state) do
    ir = IR.map_types(schema.ir, &IR.subst_ty(&1, s))
    k = state.count + 1
    stmt = {:formula, "#{schema.name}@#{k}", schema.role, [], ir}
    known = Enum.reduce(formula_instances(stmt), state.known, &add_instance/2)

    %{
      state
      | out: [stmt | state.out],
        count: k,
        known: known,
        done: MapSet.put(state.done, {schema.name, s})
    }
  end

  defp add_instance({c, args}, known),
    do: Map.update(known, c, MapSet.new([args]), &MapSet.put(&1, args))

  defp formula_instances({:formula, _, _, [], ir}) do
    IR.reduce(ir, [], fn
      {:const, c, [_ | _] = args, _}, acc -> [{c, args} | acc]
      _, acc -> acc
    end)
  end

  defp formula_instances(_), do: []

  # One-way matching of a type pattern against a ground type.
  defp match_all([], [], s), do: s

  defp match_all([p | ps], [t | ts], s) do
    case match(p, t, s) do
      :error -> :error
      s -> match_all(ps, ts, s)
    end
  end

  defp match_all(_, _, _), do: :error

  defp match({:tvar, v}, t, s) do
    case Map.fetch(s, v) do
      {:ok, ^t} -> s
      {:ok, _} -> :error
      :error -> Map.put(s, v, t)
    end
  end

  defp match({:fun, a, b}, {:fun, c, d}, s), do: match_all([a, b], [c, d], s)
  defp match({:tapp, n, as}, {:tapp, n, bs}, s), do: match_all(as, bs, s)
  defp match({:tuple, as}, {:tuple, bs}, s), do: match_all(as, bs, s)
  defp match(t, t, s), do: s
  defp match(_, _, _), do: :error
end
