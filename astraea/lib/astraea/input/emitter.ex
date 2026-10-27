defmodule Astraea.Input.Emitter do
  @moduledoc """
  Translates ground `Astraea.Input.IR` into `Astraea.Arena` terms (named binders to
  de Bruijn indices, IR types to interned arena types).

  Symbols introduced by elaboration are given meaning here by definitional axioms
  over fresh constants, which are conservative extensions and hence sound:

    * `$$ite: $o > T > T > T` (non-Boolean `$ite`):
      `! [C, A, B]: ((C => $$ite @ C @ A @ B = A) & (~ C => $$ite @ C @ A @ B = B))`;
    * tuples of type `[T1, ..., Tn]` (a sort of their own) with constructor `$$tuple`
      and projections `$$proj1`, ..., `$$projn`: every projection inverts the
      constructor and every element is the tuple of its projections;
    * distinct objects (`"abc"`, of type `$i`) are pairwise unequal.
  """

  alias Astraea.Arena
  alias Astraea.Input.IR

  import IR, only: [reject!: 1]

  @o IR.o()
  @i IR.i()

  defstruct arena: nil,
            base_types: %{},
            const_types: %{},
            ites: MapSet.new(),
            tuples: MapSet.new(),
            distinct: MapSet.new()

  @type t :: %__MODULE__{}

  @spec new(Arena.t(), map(), map()) :: t()
  def new(arena, base_types, const_types),
    do: %__MODULE__{arena: arena, base_types: base_types, const_types: const_types}

  @spec sort(t(), String.t()) :: t()
  def sort(%__MODULE__{} = st, name) do
    {st, _} = type(st, {:base, name})
    st
  end

  @spec decl(t(), String.t(), IR.ty()) :: t()
  def decl(%__MODULE__{} = st, name, ty) do
    {st, _} = term(st, {:const, name, [], ty}, [])
    st
  end

  @doc "Emits a closed formula."
  @spec formula(t(), IR.tm()) :: {t(), Arena.term_id()}
  def formula(%__MODULE__{} = st, ir), do: term(st, ir, [])

  @spec type(t(), IR.ty()) :: {t(), Arena.type_id()}
  def type(st, @o), do: {st, Arena.ty_o()}
  def type(st, @i), do: {st, Arena.ty_i()}

  def type(st, {:base, name}) do
    {arena, id} = Arena.intern_type(st.arena, {:base, name})
    {%{st | arena: arena, base_types: Map.put(st.base_types, name, id)}, id}
  end

  def type(st, {:fun, a, b}) do
    {st, a} = type(st, a)
    {st, b} = type(st, b)
    {arena, id} = Arena.intern_type(st.arena, {:arrow, a, b})
    {%{st | arena: arena}, id}
  end

  def type(st, {k, _, _} = ty) when k == :tapp, do: type(st, {:base, IR.sort_name(ty)})
  def type(st, {:tuple, _} = ty), do: type(st, {:base, IR.sort_name(ty)})
  def type(_st, ty), do: reject!("non-ground type #{IR.show(ty)}")

  defp term(st, ir, scope) do
    case ir do
      {:const, name, args, ty} ->
        name = if args == [], do: name, else: IR.sort_name({:tapp, name, args})
        {st, ty_id} = type(st, ty)
        st = note(st, name, ty)
        {arena, id} = Arena.mk_const(st.arena, name, ty_id)
        {%{st | arena: arena, const_types: Map.put(st.const_types, name, ty_id)}, id}

      {:var, id, ty} ->
        case Enum.find_index(scope, &(&1 == id)) do
          nil ->
            reject!("free variable in a formula")

          ix ->
            {st, ty_id} = type(st, ty)
            arena(st, &Arena.mk_bvar(&1, ix, ty_id))
        end

      {:app, f, a} ->
        {st, f} = term(st, f, scope)
        {st, a} = term(st, a, scope)
        arena(st, &Arena.mk_app(&1, f, a))

      {:lam, id, ty, body} ->
        {st, ty_id} = type(st, ty)
        {st, b} = term(st, body, [id | scope])
        arena(st, &Arena.mk_lam(&1, ty_id, b))

      {:quant, q, id, ty, body} ->
        {st, ty_id} = type(st, ty)
        {st, b} = term(st, body, [id | scope])
        mk = if q == :all, do: &Arena.mk_forall/3, else: &Arena.mk_exists/3
        arena(st, &mk.(&1, ty_id, b))

      {:not, a} ->
        {st, a} = term(st, a, scope)
        arena(st, &Arena.mk_not(&1, a))

      {:eq, a, b} ->
        binary(st, &Arena.mk_eq/3, a, b, scope)

      {:bin, op, a, b} ->
        mk =
          case op do
            :and -> &Arena.mk_and/3
            :or -> &Arena.mk_or/3
            :imp -> &Arena.mk_imp/3
            :iff -> &Arena.mk_iff/3
          end

        binary(st, mk, a, b, scope)

      {:modal, _, _, _} ->
        reject!("modal operator without a logic specification")
    end
  end

  defp binary(st, mk, a, b, scope) do
    {st, a} = term(st, a, scope)
    {st, b} = term(st, b, scope)
    arena(st, &mk.(&1, a, b))
  end

  defp arena(st, fun) do
    {arena, id} = fun.(st.arena)
    {%{st | arena: arena}, id}
  end

  defp note(st, "$$ite", {:fun, @o, {:fun, ty, _}}), do: %{st | ites: MapSet.put(st.ites, ty)}
  defp note(st, "$$tuple", ty), do: %{st | tuples: MapSet.put(st.tuples, result(ty))}
  defp note(st, "\"" <> _ = name, @i), do: %{st | distinct: MapSet.put(st.distinct, name)}
  defp note(st, _name, _ty), do: st

  defp result({:fun, _, b}), do: result(b)
  defp result(ty), do: ty

  # ---------------------------------------------------------------------------
  # Definitional axioms
  # ---------------------------------------------------------------------------

  @doc """
  The definitional axioms for the generated symbols that were emitted so far, as
  named IR formulas.
  """
  @spec definitions(t()) :: [{String.t(), IR.tm()}]
  def definitions(%__MODULE__{} = st) do
    ites = st.ites |> Enum.sort() |> Enum.map(&{"$$ite_def_#{IR.sort_name(&1)}", ite_def(&1)})
    tuples = st.tuples |> Enum.sort() |> Enum.flat_map(&tuple_defs/1)
    ites ++ tuples ++ distinct_def(Enum.sort(st.distinct))
  end

  defp ite_def(ty) do
    [c, a, b] = vars([@o, ty, ty])
    ite = IR.app({:const, "$$ite", [], IR.arrows([@o, ty, ty], ty)}, [c, a, b])
    body = {:bin, :and, {:bin, :imp, c, {:eq, ite, a}}, {:bin, :imp, {:not, c}, {:eq, ite, b}}}
    all([c, a, b], body)
  end

  defp tuple_defs({:tuple, tys} = tt) do
    xs = vars(tys)
    tuple = {:const, "$$tuple", [], IR.arrows(tys, tt)}

    projs =
      tys
      |> Enum.with_index(1)
      |> Enum.map(fn {ty, k} -> {:const, "$$proj#{k}", [], {:fun, tt, ty}} end)

    [t] = vars([tt], length(tys))
    name = "$$tuple_def_#{IR.sort_name(tt)}"

    inverse =
      projs
      |> Enum.zip(xs)
      |> Enum.map(fn {p, x} -> {:eq, {:app, p, IR.app(tuple, xs)}, x} end)

    [
      {name <> "_proj", all(xs, IR.conj(inverse))},
      {name <> "_eta", all([t], {:eq, IR.app(tuple, Enum.map(projs, &{:app, &1, t})), t})}
    ]
  end

  defp distinct_def(names) when length(names) < 2, do: []

  defp distinct_def(names) do
    consts = Enum.map(names, &{:const, &1, [], @i})

    pairs =
      for {a, i} <- Enum.with_index(consts),
          {b, j} <- Enum.with_index(consts),
          i < j,
          do: {:not, {:eq, a, b}}

    [{"$$distinct_objects", IR.conj(pairs)}]
  end

  defp vars(tys, offset \\ 0),
    do: tys |> Enum.with_index(offset) |> Enum.map(fn {ty, k} -> {:var, k, ty} end)

  defp all(vars, body),
    do:
      Enum.reduce(Enum.reverse(vars), body, fn {:var, id, ty}, b -> {:quant, :all, id, ty, b} end)
end
