defmodule Astraea.Engine.FVIndex do
  @moduledoc """
  Incremental feature-vector index (Leo-III `FVIndex`, Schulz 2013) over clause ids,
  answering the prefilter queries of forward/backward subsumption and backward
  demodulation: which stored vectors are `<=` (resp. `>=`) a query in all 16 lanes.

  The layout is log-structured. New entries go to a short `tail` that is scanned in
  plain Elixir; every `@seal` entries the tail is sealed into a Structure-of-Arrays
  segment (`{16, cap}` `:u16`, `cap` a power of two), and segments of similar size
  are merged, so there are O(log n) segments and each entry is copied O(log n)
  times. Removals only drop the id from `members` (query results are filtered by it, ids are
  never reinserted); dead rows disappear when their segment is next copied.

  Segments are scanned with the `Astraea.Engine.Kernels` `defn` kernels compiled by
  NxSimd (`backend: :nx_simd`) or with the plain-Elixir reference scan
  (`backend: :elixir`). A kernel call costs a roughly constant 10-30 us on armix,
  so NxSimd is used only for segments of at least `@seal` columns and batches of
  queries; below that the Elixir scan, which exits at the first failing lane, wins.
  """

  alias Astraea.Engine.Kernels

  @lanes 16
  @max_lane 0xFFFF
  @seal 1024
  @batch_sizes [8, 32, 128]

  @type fv :: tuple()
  @type backend :: :nx_simd | :elixir
  @type t :: %__MODULE__{
          backend: backend(),
          tail: [{non_neg_integer(), fv()}],
          tail_size: non_neg_integer(),
          segments: [map()],
          members: MapSet.t()
        }

  defstruct backend: :elixir,
            tail: [],
            tail_size: 0,
            segments: [],
            members: MapSet.new()

  @doc """
  An empty index. `:backend` is `:auto` (NxSimd when available, else Elixir),
  `:nx_simd` or `:elixir`.
  """
  @spec new(keyword()) :: t()
  def new(opts \\ []) do
    backend =
      case Keyword.get(opts, :backend, :auto) do
        :auto -> if Kernels.simd_available?(), do: :nx_simd, else: :elixir
        :nx_simd -> if Kernels.simd_available?(), do: :nx_simd, else: :elixir
        :elixir -> :elixir
      end

    %__MODULE__{backend: backend}
  end

  @doc "Clamps a list or tuple of 16 lane counts into a `:u16` feature vector."
  @spec fv(Enumerable.t()) :: fv()
  def fv(lanes), do: lanes |> Enum.map(&min(&1, @max_lane)) |> List.to_tuple()

  @spec size(t()) :: non_neg_integer()
  def size(%__MODULE__{} = index), do: MapSet.size(index.members)

  @spec member?(t(), non_neg_integer()) :: boolean()
  def member?(%__MODULE__{members: members}, id), do: MapSet.member?(members, id)

  @spec insert(t(), non_neg_integer(), fv()) :: t()
  def insert(%__MODULE__{} = index, id, fv) when tuple_size(fv) == @lanes do
    index = %{
      index
      | tail: [{id, fv} | index.tail],
        tail_size: index.tail_size + 1,
        members: MapSet.put(index.members, id)
    }

    if index.tail_size >= @seal, do: seal(index), else: index
  end

  @spec delete(t(), Enumerable.t()) :: t()
  def delete(%__MODULE__{} = index, ids) do
    Enum.reduce(ids, index, fn id, acc ->
      %{acc | members: MapSet.delete(acc.members, id)}
    end)
  end

  @doc "Ids whose vector is `<= fv` in every lane (candidate forward subsumers)."
  @spec subsumers(t(), fv()) :: [non_neg_integer()]
  def subsumers(%__MODULE__{} = index, fv), do: hd(query(index, :subsumers, [fv]))

  @doc "Ids whose vector is `>= fv` in every lane (candidates for backward subsumption)."
  @spec subsumed(t(), fv()) :: [non_neg_integer()]
  def subsumed(%__MODULE__{} = index, fv), do: hd(query(index, :subsumed, [fv]))

  @doc "`subsumers/2` for many query vectors at once (one kernel call per segment)."
  @spec subsumers_batch(t(), [fv()]) :: [[non_neg_integer()]]
  def subsumers_batch(%__MODULE__{} = index, fvs), do: query(index, :subsumers, fvs)

  @doc "`subsumed/2` for many query vectors at once."
  @spec subsumed_batch(t(), [fv()]) :: [[non_neg_integer()]]
  def subsumed_batch(%__MODULE__{} = index, fvs), do: query(index, :subsumed, fvs)

  @doc "Reference lane test: `a <= b` in every lane."
  @spec le?(fv(), fv()) :: boolean()
  def le?(a, b), do: le?(a, b, 0)

  defp le?(_a, _b, @lanes), do: true
  defp le?(a, b, i), do: elem(a, i) <= elem(b, i) and le?(a, b, i + 1)

  # ---------------------------------------------------------------------------
  # Queries
  # ---------------------------------------------------------------------------

  defp query(_index, _dir, []), do: []

  defp query(%__MODULE__{} = index, dir, fvs) do
    from_segments =
      Enum.reduce(index.segments, Enum.map(fvs, fn _ -> [] end), fn seg, acc ->
        Enum.zip_with(scan_segment(index.backend, seg, dir, fvs), acc, &++/2)
      end)

    Enum.zip_with(fvs, from_segments, fn fv, found ->
      tail = for {id, row} <- index.tail, hit?(dir, row, fv), do: id
      Enum.filter(tail ++ found, &MapSet.member?(index.members, &1))
    end)
  end

  defp hit?(:subsumers, row, fv), do: le?(row, fv)
  defp hit?(:subsumed, row, fv), do: le?(fv, row)

  defp scan_segment(:nx_simd, seg, dir, fvs) do
    case simd_scan(seg, dir, fvs) do
      nil -> elixir_scan(seg, dir, fvs)
      found -> found
    end
  end

  defp scan_segment(:elixir, seg, dir, fvs), do: elixir_scan(seg, dir, fvs)

  defp elixir_scan(seg, dir, fvs) do
    Enum.map(fvs, fn fv -> for {id, row} <- seg.rows, hit?(dir, row, fv), do: id end)
  end

  # One query: the single-vector kernel. Several: the batch kernel, padded to the
  # next batch size, in chunks of the largest one.
  defp simd_scan(seg, dir, [fv]) do
    with runner when runner != nil <- Kernels.runner(dir, [{@lanes}, {@lanes, seg.cap}]) do
      mask = runner.(Nx.from_binary(fv_binary(fv), :u16), seg.tensor) |> Nx.to_binary()
      [mask_ids(mask, 0, seg)]
    end
  end

  defp simd_scan(seg, dir, fvs) do
    fvs
    |> Enum.chunk_every(List.last(@batch_sizes))
    |> Enum.reduce_while([], fn chunk, acc ->
      case simd_batch(seg, dir, chunk) do
        nil -> {:halt, nil}
        found -> {:cont, acc ++ found}
      end
    end)
  end

  defp simd_batch(seg, dir, fvs) do
    k = length(fvs)
    width = Enum.find(@batch_sizes, &(&1 >= k))
    kernel = if dir == :subsumers, do: :subsumers_batch, else: :subsumed_batch

    with runner when runner != nil <- Kernels.runner(kernel, [{@lanes, width}, {@lanes, seg.cap}]) do
      # The answers of the padding queries are never read.
      pad = List.to_tuple(List.duplicate(0, @lanes))
      qs = soa_binary(Enum.map(fvs ++ List.duplicate(pad, width - k), &{nil, &1}), width)

      mask =
        runner.(qs |> Nx.from_binary(:u16) |> Nx.reshape({@lanes, width}), seg.tensor)
        |> Nx.to_binary()

      for i <- 0..(k - 1), do: mask_ids(mask, i * seg.cap, seg)
    end
  end

  defp mask_ids(mask, offset, seg) do
    for {pos, 1} <- :binary.matches(mask, <<1>>, scope: {offset, seg.cap}),
        slot = pos - offset,
        slot < seg.count,
        do: elem(seg.ids, slot)
  end

  # ---------------------------------------------------------------------------
  # Sealing & merging
  # ---------------------------------------------------------------------------

  # Binary-counter merging: the sealed tail absorbs its predecessor while it holds at
  # least half as many live entries; dead entries are dropped whenever rows are copied.
  defp seal(%__MODULE__{} = index) do
    segments =
      index.segments
      |> Enum.reverse()
      |> absorb(live_rows(Enum.reverse(index.tail), index), index)

    %{index | tail: [], tail_size: 0, segments: segments}
  end

  defp absorb([older | rest] = segments, rows, index) do
    older_rows = live_rows(older.rows, index)

    if length(rows) * 2 >= length(older_rows),
      do: absorb(rest, older_rows ++ rows, index),
      else: Enum.reverse([build_segment(rows, index.backend) | segments])
  end

  defp absorb([], rows, index), do: [build_segment(rows, index.backend)]

  defp live_rows(rows, index), do: Enum.filter(rows, &MapSet.member?(index.members, elem(&1, 0)))

  defp build_segment(rows, backend) do
    count = length(rows)
    cap = capacity(count, @seal)
    ids = rows |> Enum.map(&elem(&1, 0)) |> List.to_tuple()

    tensor =
      if backend == :nx_simd do
        rows |> soa_binary(cap) |> Nx.from_binary(:u16) |> Nx.reshape({@lanes, cap})
      end

    %{rows: rows, ids: ids, count: count, cap: cap, tensor: tensor}
  end

  defp capacity(count, cap) when cap >= count, do: cap
  defp capacity(count, cap), do: capacity(count, cap * 2)

  defp soa_binary(rows, cap) do
    pad = (cap - length(rows)) * 2

    for lane <- 0..(@lanes - 1), into: <<>> do
      column = for {_, fv} <- rows, into: <<>>, do: <<elem(fv, lane)::16-native>>
      <<column::binary, 0::size(pad)-unit(8)>>
    end
  end

  defp fv_binary(fv), do: for(lane <- Tuple.to_list(fv), into: <<>>, do: <<lane::16-native>>)
end
