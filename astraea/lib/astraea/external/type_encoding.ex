defmodule Astraea.External.TypeEncoding do
  @moduledoc """
  Type guards for untyped (FOF) output of `Astraea.External.FolEncoding`
  problems, after Leo-III's `leo.modules.encoding.TypeEncoding` (`MonoGuards`,
  `MonoGuardsLight`; both are unimplemented stubs in Leo-III).

  A guarded sort `s` gets a predicate `astraea_is_<s>`. Quantified variables of
  guarded sorts are relativized (`! [X]: (astraea_is_s(X) => ...)`), every
  function symbol with a guarded result sort gets a typing axiom
  `! [Xs]: astraea_is_s(f(Xs))`, and every guarded sort an inhabitation axiom
  `? [X]: astraea_is_s(X)`.

    * `:mono_guards` guards every sort.
    * `:mono_guards_light` guards only the sorts that
      `Astraea.External.Monotonicity` cannot show monotonic. Variables of
      monotonic sorts range over the whole untyped domain, which is sound because
      their domains can be extended to its cardinality.

  Both are sound and complete for the many-sorted problem: a typed model gives an
  untyped one over the union of the (extended) sort domains, with the guards as
  sort membership and functions extended arbitrarily into their result sorts; an
  untyped model gives a typed one by restricting guarded sorts to their guards.
  """

  alias Astraea.Arena
  alias Astraea.External.{FolEncoding, Monotonicity}

  @doc """
  Returns the guarded sorts of `problem` for the variant `types`.
  """
  @spec guarded_sorts(FolEncoding.Problem.t(), :mono_guards | :mono_guards_light) ::
          MapSet.t(Arena.type_id())
  def guarded_sorts(%FolEncoding.Problem{} = problem, :mono_guards), do: used_sorts(problem)

  def guarded_sorts(%FolEncoding.Problem{} = problem, :mono_guards_light) do
    problem.formulas |> Enum.map(& &1.formula) |> Monotonicity.nonmonotonic_sorts()
  end

  @doc "Name of the guard predicate of sort `ty`."
  @spec guard_name(Arena.type_id()) :: String.t()
  def guard_name(ty), do: "astraea_is_" <> Integer.to_string(ty)

  @doc """
  Returns the typing and inhabitation axioms for `guarded` sorts as untyped
  formulas, in a deterministic order.
  """
  @spec axioms(FolEncoding.Problem.t(), MapSet.t(Arena.type_id())) :: [FolEncoding.fo_formula()]
  def axioms(%FolEncoding.Problem{} = problem, guarded) do
    typing =
      problem.signature
      |> Enum.sort()
      |> Enum.flat_map(fn
        {name, {:fun, args, res}} ->
          if MapSet.member?(guarded, res) do
            vars = Enum.with_index(args, fn ty, i -> {"X" <> Integer.to_string(i), ty} end)
            atom = {:pred, guard_name(res), [{:fn, name, Enum.map(vars, &to_var/1)}]}
            [if(vars == [], do: atom, else: {:all, vars, atom})]
          else
            []
          end

        {_name, {:pred, _args}} ->
          []
      end)

    inhabited =
      guarded
      |> Enum.sort()
      |> Enum.map(fn ty -> {:exists, [{"X", ty}], {:pred, guard_name(ty), [{:var, "X", ty}]}} end)

    typing ++ inhabited
  end

  defp to_var({name, ty}), do: {:var, name, ty}

  defp used_sorts(problem) do
    from_sig =
      Enum.flat_map(problem.signature, fn
        {_name, {:fun, args, res}} -> [res | args]
        {_name, {:pred, args}} -> args
      end)

    problem.formulas
    |> Enum.reduce(MapSet.new(from_sig), fn %{formula: f}, acc -> var_sorts(f, acc) end)
  end

  defp var_sorts(f, acc) do
    case f do
      {:all, vars, g} -> var_sorts(g, Enum.reduce(vars, acc, &MapSet.put(&2, elem(&1, 1))))
      {:not, g} -> var_sorts(g, acc)
      {op, l, r} when op in [:or, :iff] -> var_sorts(r, var_sorts(l, acc))
      _ -> acc
    end
  end
end
