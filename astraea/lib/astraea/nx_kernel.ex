defmodule Astraea.NxKernel do
  @moduledoc """
  Shared runtime for the integer `Nx.Defn` kernels that `NxSimd.Compiler` turns into
  native SIMD code (`Astraea.Engine.Kernels`, `Astraea.Calculus.FingerprintIndex`).

  Runners are cached per kernel and argument templates in `:persistent_term` for the
  VM lifetime (NxSimd additionally caches the built shared object on disk). The first
  request for a shape starts compilation in a background process and returns `nil`,
  so a prover keeps going on its plain-Elixir path instead of blocking on a host C++
  build; `warmup/1` compiles ahead of time.
  """

  @doc "Whether NxSimd is installed and its kernel loader NIF is loaded."
  @spec available?() :: boolean()
  def available? do
    Code.ensure_loaded?(NxSimd) and apply(NxSimd, :available?, []) == true
  end

  @doc """
  The compiled runner of `kernel` (a remote capture of a `defn`) for `templates`
  (`Nx.template/2` values), or `nil` while it is compiling, failed to compile or
  NxSimd is unavailable.
  """
  @spec runner(function(), [Nx.Tensor.t()]) :: function() | nil
  def runner(kernel, templates) do
    key = cache_key(kernel, templates)

    case :persistent_term.get(key, nil) do
      fun when is_function(fun) ->
        fun

      nil ->
        if available?() do
          :persistent_term.put(key, :compiling)
          spawn(fn -> :persistent_term.put(key, try_compile(kernel, templates)) end)
        end

        nil

      _compiling_or_failed ->
        nil
    end
  end

  @doc "Compiles `kernel` for `templates` with `NxSimd.Compiler` (synchronously)."
  @spec compile(function(), [Nx.Tensor.t()]) :: function()
  def compile(kernel, templates),
    do: Nx.Defn.compile(kernel, templates, compiler: NxSimd.Compiler)

  @doc "Compiles and caches the given `{kernel, templates}` pairs now."
  @spec warmup([{function(), [Nx.Tensor.t()]}]) :: :ok
  def warmup(specs) do
    if available?() do
      Enum.each(specs, fn {kernel, templates} ->
        :persistent_term.put(cache_key(kernel, templates), compile(kernel, templates))
      end)
    end

    :ok
  end

  @doc "The smallest power of two `>= n`, at least `min` (padded kernel shapes)."
  @spec bucket(non_neg_integer(), pos_integer()) :: pos_integer()
  def bucket(n, min) when min >= n, do: min
  def bucket(n, min), do: bucket(n, min * 2)

  defp try_compile(kernel, templates) do
    compile(kernel, templates)
  rescue
    _ -> :failed
  end

  defp cache_key(kernel, templates),
    do: {__MODULE__, kernel, Enum.map(templates, &{&1.type, &1.shape})}
end
