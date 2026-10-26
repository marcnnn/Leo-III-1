defmodule Astraea.Calculus.FingerprintIndex do
  @moduledoc """
  Higher-order fingerprint indexing (Schulz, "Fingerprint Indexing for Paramodulation
  and Rewriting", IJCAR 2012) for retrieving unification and matching partners.

  A fingerprint samples a term at eight positions of its spine view
  (`Astraea.Calculus.Terms.view/2`, arguments numbered from 0):

      e, 0, 1, 2, 0.0, 0.1, 1.0, 1.1

  This is Schulz's `FP8` shape. Literal atoms are dominated by `p a b`, `s = t`,
  `~ (s = t)` and connective nests, whose distinguishing symbols sit at depth two
  (`f` in `f(x) = g(y)` is at `0`, its arguments at `0.0`, `0.1`); deeper samples
  rarely reject more candidates but cost a full fingerprint lane each.

  Every sample is an integer feature:

    * `0` (N): the position does not exist and cannot be created by instantiation
      (its parent is rigid with fewer arguments),
    * `1` (V): a free variable or flexible head `F @ ...` sits here,
    * `2` (B): the position lies below a variable or below a lambda,
    * `3` (L): a lambda abstraction (unifies with any term of arrow type by eta),
    * `>= 4`: a rigid head, i.e. a constant, Skolem, combinator, de Bruijn variable
      (one class per index and type) or a connective (`=` and `!` per type, `~`, `|`).

  Terms are sampled in beta-eta normal form. Only a rigid head clash, a rigid head
  against N, or a variable against N can reject a pair, so the unification filter
  never drops a unifiable pair. The stricter matching table (pattern against
  target, target variables are constants) additionally rejects a rigid pattern head
  against a target variable.

  The compatibility test is a 5 x 5 class table lookup per position, ANDed over the
  positions (`compat_kernel/3`). Rows are stored in a Structure-of-Arrays layout (one
  binary lane per position) so that the whole index can be checked against a batch
  of queries with one integer `Nx` graph compiled by `NxSimd.Compiler`. Without Nx
  (or below `:nx_min_rows`) the identical table is evaluated in plain Elixir.

  The index is incremental: inserts append to the lanes (amortized O(1)), deletes
  are tombstones that are filtered from query results.
  """

  alias Astraea.Arena
  alias Astraea.Calculus.Terms

  @positions [[], [0], [1], [2], [0, 0], [0, 1], [1, 0], [1, 1]]
  @width length(@positions)

  @n 0
  @v 1
  @b 2
  @l 3
  @not_code 5
  @or_code 6

  # Class tables indexed by `5 * class(query) + class(target)` with
  # `class(x) = min(x, 4)`; entry 24 (rigid vs rigid) additionally needs equal codes.
  #                 N  V  B  L  S
  @unify_table [1, 0, 1, 0, 0] ++
                 [0, 1, 1, 1, 1] ++
                 [1, 1, 1, 1, 1] ++
                 [0, 1, 1, 1, 1] ++
                 [0, 1, 1, 1, 1]
  @match_table [1, 0, 1, 0, 0] ++
                 [0, 1, 1, 1, 1] ++
                 [1, 1, 1, 1, 1] ++
                 [0, 1, 1, 1, 1] ++
                 [0, 0, 1, 1, 1]

  defstruct lanes: List.duplicate(<<>>, @width),
            rows: %{},
            payloads: %{},
            dead: MapSet.new(),
            size: 0

  @type mode :: :unify | :match
  @type fingerprint :: tuple()
  @type t :: %__MODULE__{}

  @spec new() :: t()
  def new, do: %__MODULE__{}

  @doc "Number of sample positions per fingerprint."
  @spec width() :: pos_integer()
  def width, do: @width

  @doc "The class table of `mode` as a flat list of 25 `0 | 1` entries."
  @spec table(mode()) :: [0 | 1]
  def table(:unify), do: @unify_table
  def table(:match), do: @match_table

  # ---------------------------------------------------------------------------
  # Fingerprints
  # ---------------------------------------------------------------------------

  @doc """
  Samples `term_id` (beta-eta normal) at the fingerprint positions.
  """
  @spec fingerprint(Arena.t(), Arena.term_id()) :: fingerprint()
  def fingerprint(%Arena{} = arena, term_id) do
    @positions
    |> Enum.map(&sample(arena, term_id, &1))
    |> List.to_tuple()
  end

  defp sample(arena, term_id, []), do: code(arena, Terms.view(arena, term_id))

  defp sample(arena, term_id, [i | rest]) do
    case Terms.view(arena, term_id) do
      {:rigid, _head, children} ->
        case Enum.at(children, i) do
          {child, _shift} -> sample(arena, child, rest)
          nil -> @n
        end

      _flex_or_lambda ->
        @b
    end
  end

  defp code(_arena, {:flex, _, _}), do: @v
  defp code(_arena, {:lam, _, _}), do: @l
  defp code(_arena, {:rigid, :not, _}), do: @not_code
  defp code(_arena, {:rigid, :or, _}), do: @or_code
  defp code(_arena, {:rigid, {:sym, id}, _}), do: 8 + 4 * id
  defp code(_arena, {:rigid, {:eq, ty}, _}), do: 9 + 4 * ty
  defp code(_arena, {:rigid, {:forall, ty}, _}), do: 10 + 4 * ty

  @doc """
  Plain-Elixir compatibility test of a query fingerprint against a stored one.
  """
  @spec compatible?(mode(), fingerprint(), fingerprint()) :: boolean()
  def compatible?(mode, query, target), do: compatible?(table_tuple(mode), query, target, 0)

  defp compatible?(_table, _q, _t, @width), do: true

  defp compatible?(table, q, t, pos) do
    feature_ok?(table, elem(q, pos), elem(t, pos)) and compatible?(table, q, t, pos + 1)
  end

  defp feature_ok?(table, qv, tv) do
    idx = 5 * min(qv, 4) + min(tv, 4)
    elem(table, idx) == 1 and (idx != 24 or qv == tv)
  end

  defp table_tuple(:unify), do: List.to_tuple(@unify_table)
  defp table_tuple(:match), do: List.to_tuple(@match_table)

  # ---------------------------------------------------------------------------
  # Incremental index
  # ---------------------------------------------------------------------------

  @doc "Adds `term_id` with `payload`; returns the index and the new row slot."
  @spec insert(t(), Arena.t(), Arena.term_id(), term()) :: {t(), non_neg_integer()}
  def insert(%__MODULE__{} = index, %Arena{} = arena, term_id, payload) do
    fp = fingerprint(arena, term_id)
    slot = index.size

    lanes =
      index.lanes
      |> Enum.with_index()
      |> Enum.map(fn {lane, pos} -> <<lane::binary, elem(fp, pos)::32-signed-little>> end)

    index = %{
      index
      | lanes: lanes,
        rows: Map.put(index.rows, slot, fp),
        payloads: Map.put(index.payloads, slot, payload),
        size: slot + 1
    }

    {index, slot}
  end

  @doc "Tombstones every row whose payload satisfies `fun`."
  @spec delete_where(t(), (term() -> boolean())) :: t()
  def delete_where(%__MODULE__{} = index, fun) do
    dead =
      for {slot, payload} <- index.payloads, fun.(payload), reduce: index.dead do
        acc -> MapSet.put(acc, slot)
      end

    %{index | dead: dead, payloads: Map.drop(index.payloads, MapSet.to_list(dead))}
  end

  @doc "Number of live rows."
  @spec live_count(t()) :: non_neg_integer()
  def live_count(%__MODULE__{} = index), do: map_size(index.payloads)

  @doc """
  For each query fingerprint returns the payloads of all live rows compatible with
  it under `mode`. Options: `:backend` (`:auto | :elixir | :nx`) and
  `:nx_min_rows` (default 4096) for `:auto`.
  """
  @spec query(t(), [fingerprint()], mode(), keyword()) :: [[term()]]
  def query(%__MODULE__{} = index, queries, mode, opts \\ []) do
    case backend(index, queries, opts) do
      :nx -> query_nx(index, queries, mode)
      :elixir -> query_elixir(index, queries, mode)
    end
  end

  defp backend(index, queries, opts) do
    case Keyword.get(opts, :backend, :auto) do
      :auto ->
        if nx_available?() and queries != [] and
             index.size >= Keyword.get(opts, :nx_min_rows, 4096),
           do: :nx,
           else: :elixir

      other ->
        other
    end
  end

  defp query_elixir(index, queries, mode) do
    table = table_tuple(mode)

    Enum.map(queries, fn q ->
      for {slot, payload} <- index.payloads,
          compatible?(table, q, Map.fetch!(index.rows, slot), 0),
          do: payload
    end)
  end

  @doc "Returns true iff `Nx` and `NxSimd.Compiler` are available."
  @spec nx_available?() :: boolean()
  def nx_available?, do: Code.ensure_loaded?(Nx) and Code.ensure_loaded?(NxSimd.Compiler)

  if Code.ensure_loaded?(Nx) do
    @doc """
    Integer `Nx` compatibility kernel: `queries` `{q, 8}` (`:s32`), `table` `{25}`
    (`:u8`), `targets` SoA `{8, n}` (`:s32`) to a `{q, n}` `:u8` mask. Each position
    is one fused table lookup (`Nx.take`) and equality test.
    """
    def compat_kernel(queries, table, targets) do
      {q, width} = Nx.shape(queries)
      {^width, n} = Nx.shape(targets)

      Enum.reduce(0..(width - 1), Nx.broadcast(Nx.tensor(1, type: :u8), {q, n}), fn pos, acc ->
        qv = queries |> Nx.slice([0, pos], [q, 1])
        tv = targets |> Nx.slice([pos, 0], [1, n])
        idx = Nx.add(Nx.multiply(Nx.min(qv, 4), 5), Nx.min(tv, 4))
        rigid_ok = Nx.logical_or(Nx.equal(qv, tv), Nx.not_equal(idx, 24))
        Nx.logical_and(acc, Nx.logical_and(Nx.take(table, idx), rigid_ok))
      end)
    end

    defp query_nx(index, queries, mode) do
      cap = bucket(index.size, 1024)
      qcap = bucket(length(queries), 8)
      runner = runner(qcap, cap)

      targets =
        index.lanes
        |> Enum.map(&pad(&1, cap - index.size))
        |> IO.iodata_to_binary()
        |> Nx.from_binary(:s32)
        |> Nx.reshape({@width, cap})

      q_rows =
        Enum.map(queries, &Tuple.to_list/1) ++
          List.duplicate(List.duplicate(@n, @width), qcap - length(queries))

      q_tensor = Nx.tensor(q_rows, type: :s32)
      t_tensor = Nx.tensor(table(mode), type: :u8)

      runner.(q_tensor, t_tensor, targets)
      |> Nx.to_binary()
      |> mask_rows(cap)
      |> Enum.take(length(queries))
      |> Enum.map(fn row ->
        for slot <- row, slot < index.size, {:ok, p} <- [Map.fetch(index.payloads, slot)], do: p
      end)
    end

    defp mask_rows(bin, cap) do
      for <<row::binary-size(cap) <- bin>> do
        for {1, slot} <- Enum.with_index(:binary.bin_to_list(row)), do: slot
      end
    end

    defp pad(lane, 0), do: lane
    defp pad(lane, k), do: [lane, :binary.copy(<<@n::32-signed-little>>, k)]

    # One compiled runner per padded shape, cached for the VM lifetime.
    defp runner(q, n) do
      key = {__MODULE__, :runner, q, n}

      case :persistent_term.get(key, nil) do
        nil ->
          args = [
            Nx.template({q, @width}, :s32),
            Nx.template({25}, :u8),
            Nx.template({@width, n}, :s32)
          ]

          compiled = Nx.Defn.compile(&compat_kernel/3, args, compiler: NxSimd.Compiler)
          :persistent_term.put(key, compiled)
          compiled

        compiled ->
          compiled
      end
    end

    defp bucket(n, min), do: max(min, next_pow2(n))
    defp next_pow2(n) when n <= 1, do: 1
    defp next_pow2(n), do: 2 * next_pow2(div(n + 1, 2))
  else
    defp query_nx(index, queries, mode), do: query_elixir(index, queries, mode)
  end
end
