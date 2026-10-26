defmodule Astraea.Native do
  @moduledoc """
  Layer 4 Native Rustler NIF bindings (`astraea_native`) for zero-copy Arena KBO
  ordering and SIMD 16-lane Feature-Vector (`FVIndex`) subsumption.
  """

  use Rustler,
    otp_app: :astraea,
    crate: "astraea_native"

  @spec nif_kbo_compare(binary(), non_neg_integer(), non_neg_integer()) ::
          :gt | :lt | :eq | :inc
  def nif_kbo_compare(_arena_bin, _s_id, _t_id),
    do: :erlang.nif_error(:nif_not_loaded)

  @spec nif_feature_vector(binary(), non_neg_integer()) :: [non_neg_integer()]
  def nif_feature_vector(_arena_bin, _term_id),
    do: :erlang.nif_error(:nif_not_loaded)

  @spec nif_fv_subsumes_batch([non_neg_integer()], binary()) :: [non_neg_integer()]
  def nif_fv_subsumes_batch(_cand_fv, _targets_bin),
    do: :erlang.nif_error(:nif_not_loaded)

  @doc """
  Packs a list of 16-lane feature vectors into a contiguous 64-byte-per-vector
  big-endian binary for `nif_fv_subsumes_batch/2`.
  """
  @spec pack_feature_vectors([[non_neg_integer()]]) :: binary()
  def pack_feature_vectors(fvs) do
    for fv <- fvs, lane <- fv, into: <<>> do
      <<lane::32-big>>
    end
  end
end
