defmodule Astraea.Engine.Kernels do
  @moduledoc """
  Integer `Nx.Defn` kernels of the saturation engine, the single source of truth for
  every bulk feature-vector test. They run compiled to native SIMD code by
  `NxSimd.Compiler` when it is available (`runner/2`) and otherwise serve as the
  executable specification that `Astraea.Engine.FVIndex`'s plain-Elixir path is
  property-tested against.

  A block is a Structure-of-Arrays `{16, n}` `:u16` table of clause feature vectors
  (one column per clause). Writing the lane conjunction as an unrolled chain of
  `logical_and`s (instead of `Nx.all/2` or a `sum` over lanes) lets `NxSimd.Codegen`
  fuse all 16 comparisons into one unit-stride vector loop.
  """
  import Nx.Defn

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

  @doc "Whether compiled kernels can be used in this VM."
  @spec simd_available?() :: boolean()
  def simd_available? do
    Code.ensure_loaded?(NxSimd) and apply(NxSimd, :available?, []) == true
  end

  @doc """
  The NxSimd-compiled runner of `kernel` for the given argument shapes, or `nil`
  while it is not compiled yet. Compilation (a host C++ build on first use, cached
  on disk afterwards) runs in a background process, so a prover never blocks on it;
  callers use the plain-Elixir path until the runner is ready.
  """
  @spec runner(atom(), [tuple()]) :: (... -> Nx.Tensor.t()) | nil
  def runner(kernel, shapes) do
    key = {__MODULE__, kernel, shapes}

    case :persistent_term.get(key, nil) do
      fun when is_function(fun) ->
        fun

      nil ->
        :persistent_term.put(key, :compiling)
        spawn(fn -> :persistent_term.put(key, try_compile(kernel, shapes)) end)
        nil

      _compiling_or_failed ->
        nil
    end
  end

  defp try_compile(kernel, shapes) do
    compile_kernel(kernel, shapes)
  rescue
    _ -> :failed
  end

  @doc "Compiles `kernel` for `shapes` synchronously (warm-up and benchmarks)."
  @spec compile_kernel(atom(), [tuple()]) :: (... -> Nx.Tensor.t())
  def compile_kernel(kernel, shapes) do
    templates = Enum.map(shapes, &Nx.template(&1, :u16))
    Nx.Defn.compile(Function.capture(__MODULE__, kernel, 2), templates, compiler: NxSimd.Compiler)
  end

  @doc "Compiles `kernels` for the given shapes now, so later runs find them cached."
  @spec warmup([{atom(), [tuple()]}]) :: :ok
  def warmup(specs) do
    if simd_available?() do
      Enum.each(specs, fn {kernel, shapes} ->
        :persistent_term.put({__MODULE__, kernel, shapes}, compile_kernel(kernel, shapes))
      end)
    end

    :ok
  end
end
