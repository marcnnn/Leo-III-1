defmodule Astraea.Engine.Kernels do
  @moduledoc """
  Integer `Nx.Defn` kernels of the saturation engine, the single source of truth for
  every bulk feature-vector test. They run compiled to native SIMD code by
  `NxSimd.Compiler` when it is available (`runner/2`, via `Astraea.NxKernel`) and otherwise serve as the
  executable specification that `Astraea.Engine.FVIndex`'s plain-Elixir path is
  property-tested against.

  A block is a Structure-of-Arrays `{16, n}` `:u16` table of clause feature vectors
  (one column per clause). Writing the lane conjunction as an unrolled chain of
  `logical_and`s (instead of `Nx.all/2` or a `sum` over lanes) lets `NxSimd.Codegen`
  fuse all 16 comparisons into one unit-stride vector loop.
  """
  import Nx.Defn

  alias Astraea.NxKernel

  @lanes 16

  @doc "Mask over the columns `c` of `block` with `c <= q` in every lane."
  defn(subsumers(q, block), do: all_lanes(block <= Nx.new_axis(q, 1)))

  @doc "Mask over the columns `c` of `block` with `c >= q` in every lane."
  defn(subsumed(q, block), do: all_lanes(block >= Nx.new_axis(q, 1)))

  @doc "`{k, n}` mask: `subsumers/2` for each of the `k` query columns of `qs` (`{16, k}`)."
  defn(subsumers_batch(qs, block),
    do: all_lanes(Nx.new_axis(block, 1) <= Nx.new_axis(qs, 2))
  )

  @doc "`{k, n}` mask: `subsumed/2` for each of the `k` query columns of `qs` (`{16, k}`)."
  defn(subsumed_batch(qs, block),
    do: all_lanes(Nx.new_axis(block, 1) >= Nx.new_axis(qs, 2))
  )

  deftransformp all_lanes(cmp) do
    Enum.reduce(1..(@lanes - 1), cmp[0], &Nx.logical_and(&2, cmp[&1]))
  end

  @doc """
  The NxSimd runner of `kernel` for `:u16` arguments of the given shapes, or `nil`
  until it is compiled (see `Astraea.NxKernel.runner/2`).
  """
  @spec runner(atom(), [tuple()]) :: function() | nil
  def runner(kernel, shapes), do: NxKernel.runner(capture(kernel), templates(shapes))

  @doc "Compiles `kernel` for `:u16` arguments of the given shapes synchronously."
  @spec compile_kernel(atom(), [tuple()]) :: function()
  def compile_kernel(kernel, shapes), do: NxKernel.compile(capture(kernel), templates(shapes))

  @doc "Compiles the kernels for the given shapes now, so later runs find them cached."
  @spec warmup([{atom(), [tuple()]}]) :: :ok
  def warmup(specs),
    do:
      specs
      |> Enum.map(fn {k, shapes} -> {capture(k), templates(shapes)} end)
      |> NxKernel.warmup()

  defp capture(kernel), do: Function.capture(__MODULE__, kernel, 2)
  defp templates(shapes), do: Enum.map(shapes, &Nx.template(&1, :u16))
end
