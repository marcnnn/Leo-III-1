defmodule Astraea.NxSimdIndex do
  @moduledoc """
  Vectorized 16-lane Feature-Vector (`FVIndex`) subsumption and quantized `int8`
  PGO clause-utility scoring powered by `NxSimd.Compiler` and `NxFixed.WidthCheck`.

  Uses a Structure-of-Arrays (SoA) `{16, N}` layout for the clause feature table so
  `NxSimd.Codegen` fuses all 16 feature comparisons into a single `#pragma omp simd`
  unit-stride vector loop with zero intermediate scratch buffer allocation (`arena_size == 0`).
  """

  @doc """
  Pure `Nx` `defn`-compatible Structure-of-Arrays 16-lane subsumption kernel:
  Given `cand` of shape `{16}` (`:u16`) and `targets_soa` of shape `{16, n}` (`:u16`),
  returns a `:u8` mask of shape `{n}` where `1` means `forall lane in 0..15: cand[lane] <= targets_soa[lane, idx]`.
  """
  def fv_subsumes_soa_kernel(cand, targets_soa) do
    {16, n} = Nx.shape(targets_soa)

    Enum.reduce(
      1..15,
      Nx.less_equal(Nx.slice(cand, [0], [1]), Nx.slice(targets_soa, [0, 0], [1, n])),
      fn lane, acc ->
        lane_cmp =
          Nx.less_equal(Nx.slice(cand, [lane], [1]), Nx.slice(targets_soa, [lane, 0], [1, n]))

        Nx.logical_and(acc, lane_cmp)
      end
    )
    |> Nx.reshape({n})
  end

  @doc """
  Packs a list of 16-lane feature vectors (`[[u16]]` of length `N`) into a
  transposed Structure-of-Arrays `:u16` `Nx.Tensor` of shape `{16, N}` and a
  candidate `:u16` `Nx.Tensor` of shape `{16}`.
  """
  def pack_soa_tensors(cand_fv, target_fvs) do
    n = length(target_fvs)
    cand_tensor = Nx.tensor(cand_fv, type: :u16)

    # Row-major {N, 16} transposed to contiguous {16, N} Structure-of-Arrays
    soa_tensor =
      target_fvs
      |> Nx.tensor(type: :u16)
      |> Nx.transpose(axes: [1, 0])
      |> Nx.backend_copy(Nx.BinaryBackend)

    {cand_tensor, soa_tensor, n}
  end

  @doc """
  Compiles `fv_subsumes_soa_kernel/2` via `NxSimd.Compiler` (checking integer widths
  with `NxFixed.WidthCheck` and emitting `-O3 -march=native -fopenmp-simd` C++20).
  Returns `{compiled_runner_fn, generated_cpp_source}`.
  """
  def compile_soa_subsumption(cand_tensor, soa_tensor, opts \\ []) do
    expr = Nx.Defn.debug_expr(&fv_subsumes_soa_kernel/2).(cand_tensor, soa_tensor)
    cpp_source = NxSimd.Compiler.source(expr, opts)

    runner =
      Nx.Defn.compile(&fv_subsumes_soa_kernel/2, [cand_tensor, soa_tensor],
        compiler: NxSimd.Compiler
      )

    {runner, cpp_source}
  end
end
