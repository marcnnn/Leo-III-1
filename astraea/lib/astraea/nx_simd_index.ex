defmodule Astraea.NxSimdIndex do
  @moduledoc """
  Gate 4 helpers around the Structure-of-Arrays feature-vector kernel of
  `Astraea.Engine.Kernels` (the prover itself uses `Astraea.Engine.FVIndex`):
  packing `{16, N}` `:u16` tables and compiling the kernel with `NxSimd.Compiler`
  (`-O3 -march=native` C++, integer widths checked by `NxFixed.WidthCheck`).
  """

  alias Astraea.Engine.Kernels

  @doc """
  `:u8` mask of shape `{n}`: `1` where `cand[lane] <= targets_soa[lane, idx]` for
  every lane, i.e. `Kernels.subsumed/2`.
  """
  def fv_subsumes_soa_kernel(cand, targets_soa), do: Kernels.subsumed(cand, targets_soa)

  @doc """
  Packs a list of 16-lane feature vectors (`[[u16]]` of length `N`) into a
  transposed Structure-of-Arrays `:u16` `Nx.Tensor` of shape `{16, N}` and a
  candidate `:u16` `Nx.Tensor` of shape `{16}`.
  """
  def pack_soa_tensors(cand_fv, target_fvs) do
    n = length(target_fvs)
    cand_tensor = Nx.tensor(cand_fv, type: :u16)

    soa_tensor =
      target_fvs
      |> Nx.tensor(type: :u16)
      |> Nx.transpose(axes: [1, 0])
      |> Nx.backend_copy(Nx.BinaryBackend)

    {cand_tensor, soa_tensor, n}
  end

  @doc """
  Compiles the kernel for the shapes of the given tensors with `NxSimd.Compiler`.
  Returns `{compiled_runner_fn, generated_cpp_source}`; requires NxSimd.
  """
  def compile_soa_subsumption(cand_tensor, soa_tensor, opts \\ []) do
    expr = Nx.Defn.debug_expr(&Kernels.subsumed/2).(cand_tensor, soa_tensor)
    cpp_source = apply(NxSimd.Compiler, :source, [expr, opts])
    runner = Kernels.compile_kernel(:subsumed, [Nx.shape(cand_tensor), Nx.shape(soa_tensor)])
    {runner, cpp_source}
  end
end
