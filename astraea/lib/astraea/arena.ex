defmodule Astraea.Arena do
  @moduledoc """
  Layer 2 Canonical Flat Logic IR (u32-indexed hash-consed arena) for monomorphic THF0.

  Matches the binary node layout defined in `Notes/master_thesis_proposal.md`:
  `<<tag::8, flags::8, type_id::16, left::32, right::32>>` (12 bytes/node),
  plus deterministic content-addressed Skolem symbol derivation so parallel OTP
  workers can safely exchange unit lemmas without central counter synchronization.
  """

  import Bitwise

  @type type_id :: non_neg_integer()
  @type term_id :: non_neg_integer()

  # Built-in base types
  @ty_o 0
  @ty_i 1

  # Node tags (u8)
  @tag_const 1
  @tag_bvar 2
  @tag_fvar 3
  @tag_app 4
  @tag_lam 5
  @tag_eq 6
  @tag_not 7
  @tag_or 8
  @tag_forall 9
  @tag_skolem 10
  @tag_comb 11

  # Combinator IDs for binder-free lowering (S, K, I, B, C)
  @comb_s 1
  @comb_k 2
  @comb_i 3
  @comb_b 4
  @comb_c 5

  defstruct types: %{
              :o => @ty_o,
              :i => @ty_i
            },
            type_table: %{
              @ty_o => :o,
              @ty_i => :i
            },
            next_type_id: 2,
            nodes: %{},
            node_index: %{},
            symbols: %{},
            symbol_names: %{},
            next_symbol_id: 1

  @type t :: %__MODULE__{}

  @spec new() :: t()
  def new, do: %__MODULE__{}

  @spec ty_o() :: type_id()
  def ty_o, do: @ty_o

  @spec ty_i() :: type_id()
  def ty_i, do: @ty_i

  @doc """
  Interns a monomorphic HOL type (`:o`, `:i`, `{:base, name}`, or `{:arrow, dom_id, cod_id}`).
  """
  @spec intern_type(t(), term()) :: {t(), type_id()}
  def intern_type(%__MODULE__{} = arena, :o), do: {arena, @ty_o}
  def intern_type(%__MODULE__{} = arena, :i), do: {arena, @ty_i}

  def intern_type(%__MODULE__{} = arena, {:arrow, dom, cod}) do
    {arena, dom_id} = intern_type(arena, dom)
    {arena, cod_id} = intern_type(arena, cod)
    key = {:arrow, dom_id, cod_id}

    case Map.fetch(arena.types, key) do
      {:ok, id} ->
        {arena, id}

      :error ->
        id = arena.next_type_id

        arena = %{
          arena
          | types: Map.put(arena.types, key, id),
            type_table: Map.put(arena.type_table, id, key),
            next_type_id: id + 1
        }

        {arena, id}
    end
  end

  def intern_type(%__MODULE__{} = arena, {:base, name}) when is_binary(name) do
    key = {:base, name}

    case Map.fetch(arena.types, key) do
      {:ok, id} ->
        {arena, id}

      :error ->
        id = arena.next_type_id

        arena = %{
          arena
          | types: Map.put(arena.types, key, id),
            type_table: Map.put(arena.type_table, id, key),
            next_type_id: id + 1
        }

        {arena, id}
    end
  end

  def intern_type(%__MODULE__{} = arena, type_id) when is_integer(type_id) do
    {arena, type_id}
  end

  @doc """
  Encodes a single 12-byte arena node: `<<tag::8, flags::8, type_id::16, left::32, right::32>>`.
  """
  @spec encode_node(non_neg_integer(), non_neg_integer(), type_id(), non_neg_integer(), non_neg_integer()) ::
          <<_::96>>
  def encode_node(tag, flags, type_id, left, right) do
    <<tag::8, flags::8, type_id::16-big, left::32-big, right::32-big>>
  end

  @spec decode_node(<<_::96>>) :: {non_neg_integer(), non_neg_integer(), type_id(), non_neg_integer(), non_neg_integer()}
  def decode_node(<<tag::8, flags::8, type_id::16-big, left::32-big, right::32-big>>) do
    {tag, flags, type_id, left, right}
  end

  @doc """
  Hash-conses a 12-byte node into the arena, returning `{arena, term_id}` in O(1).
  """
  @spec intern_node(t(), non_neg_integer(), non_neg_integer(), type_id(), non_neg_integer(), non_neg_integer()) ::
          {t(), term_id()}
  def intern_node(%__MODULE__{} = arena, tag, flags, type_id, left, right) do
    packed = encode_node(tag, flags, type_id, left, right)

    case Map.fetch(arena.node_index, packed) do
      {:ok, id} ->
        {arena, id}

      :error ->
        id = map_size(arena.nodes)

        arena = %{
          arena
          | nodes: Map.put(arena.nodes, id, packed),
            node_index: Map.put(arena.node_index, packed, id)
        }

        {arena, id}
    end
  end

  @spec intern_symbol(t(), String.t()) :: {t(), non_neg_integer()}
  def intern_symbol(%__MODULE__{} = arena, name) when is_binary(name) do
    case Map.fetch(arena.symbols, name) do
      {:ok, sym_id} ->
        {arena, sym_id}

      :error ->
        sym_id = arena.next_symbol_id

        arena = %{
          arena
          | symbols: Map.put(arena.symbols, name, sym_id),
            symbol_names: Map.put(arena.symbol_names, sym_id, name),
            next_symbol_id: sym_id + 1
        }

        {arena, sym_id}
    end
  end

  @spec mk_const(t(), String.t(), term()) :: {t(), term_id()}
  def mk_const(%__MODULE__{} = arena, name, ty) do
    {arena, ty_id} = intern_type(arena, ty)
    {arena, sym_id} = intern_symbol(arena, name)
    intern_node(arena, @tag_const, 0, ty_id, sym_id, 0)
  end

  @spec mk_bvar(t(), non_neg_integer(), term()) :: {t(), term_id()}
  def mk_bvar(%__MODULE__{} = arena, de_bruijn_idx, ty) when de_bruijn_idx >= 0 do
    {arena, ty_id} = intern_type(arena, ty)
    intern_node(arena, @tag_bvar, 1, ty_id, de_bruijn_idx, 0)
  end

  @spec mk_app(t(), term_id(), term_id()) :: {t(), term_id()}
  def mk_app(%__MODULE__{} = arena, fun_id, arg_id) do
    {_, f_flags, f_ty, _, _} = get_node(arena, fun_id)
    {_, a_flags, a_ty, _, _} = get_node(arena, arg_id)

    case Map.fetch!(arena.type_table, f_ty) do
      {:arrow, ^a_ty, ret_ty} ->
        flags = bor(f_flags, a_flags)
        intern_node(arena, @tag_app, flags, ret_ty, fun_id, arg_id)

      other ->
        raise ArgumentError,
              "Type mismatch in application: expected {:arrow, #{a_ty}, _}, got #{inspect(other)}"
    end
  end

  @spec mk_lam(t(), term(), term_id()) :: {t(), term_id()}
  def mk_lam(%__MODULE__{} = arena, var_ty, body_id) do
    {arena, dom_id} = intern_type(arena, var_ty)
    {_, b_flags, cod_id, _, _} = get_node(arena, body_id)
    {arena, arrow_id} = intern_type(arena, {:arrow, dom_id, cod_id})
    intern_node(arena, @tag_lam, b_flags, arrow_id, dom_id, body_id)
  end

  @spec mk_eq(t(), term_id(), term_id()) :: {t(), term_id()}
  def mk_eq(%__MODULE__{} = arena, lhs_id, rhs_id) do
    {_, l_flags, l_ty, _, _} = get_node(arena, lhs_id)
    {_, r_flags, r_ty, _, _} = get_node(arena, rhs_id)

    if l_ty != r_ty do
      raise ArgumentError, "Equality type mismatch: #{l_ty} != #{r_ty}"
    end

    # Canonicalize commutative ground equality ordering when needed
    intern_node(arena, @tag_eq, bor(l_flags, r_flags), @ty_o, lhs_id, rhs_id)
  end

  @spec mk_comb(t(), :s | :k | :i | :b | :c, term()) :: {t(), term_id()}
  def mk_comb(%__MODULE__{} = arena, comb, ty) do
    {arena, ty_id} = intern_type(arena, ty)

    comb_id =
      case comb do
        :s -> @comb_s
        :k -> @comb_k
        :i -> @comb_i
        :b -> @comb_b
        :c -> @comb_c
      end

    intern_node(arena, @tag_comb, 0, ty_id, comb_id, 0)
  end

  @spec get_node(t(), term_id()) ::
          {non_neg_integer(), non_neg_integer(), type_id(), non_neg_integer(), non_neg_integer()}
  def get_node(%__MODULE__{} = arena, id) do
    arena.nodes
    |> Map.fetch!(id)
    |> decode_node()
  end

  @doc """
  Serializes a term DAG rooted at `root_id` into a canonical structural binary
  (independent of arena insertion order) and computes its 32-bit content-addressed
  Skolem hash. Parallel OTP workers computing Skolem witnesses for alpha-equivalent
  quantified formulas always derive the exact same Skolem ID without coordination.
  """
  @spec skolem_hash(t(), term_id()) :: non_neg_integer()
  def skolem_hash(%__MODULE__{} = arena, root_id) do
    canonical = canonical_bytes(arena, root_id)
    <<hash32::32-big, _rest::binary>> = :crypto.hash(:sha256, canonical)
    hash32
  end

  @spec mk_skolem(t(), term_id(), term()) :: {t(), term_id()}
  def mk_skolem(%__MODULE__{} = arena, quantified_predicate_id, skolem_ty) do
    {arena, ty_id} = intern_type(arena, skolem_ty)
    sk_hash = skolem_hash(arena, quantified_predicate_id)
    intern_node(arena, @tag_skolem, 0, ty_id, sk_hash, quantified_predicate_id)
  end

  @spec canonical_bytes(t(), term_id()) :: binary()
  def canonical_bytes(%__MODULE__{} = arena, term_id) do
    {tag, _flags, ty_id, left, right} = get_node(arena, term_id)
    ty_bytes = canonical_type_bytes(arena, ty_id)

    case tag do
      @tag_const ->
        name = Map.fetch!(arena.symbol_names, left)
        <<@tag_const::8, ty_bytes::binary, byte_size(name)::16-big, name::binary>>

      @tag_bvar ->
        <<@tag_bvar::8, ty_bytes::binary, left::32-big>>

      @tag_comb ->
        <<@tag_comb::8, ty_bytes::binary, left::8>>

      @tag_skolem ->
        <<@tag_skolem::8, ty_bytes::binary, left::32-big>>

      @tag_app ->
        <<@tag_app::8, ty_bytes::binary, canonical_bytes(arena, left)::binary,
          canonical_bytes(arena, right)::binary>>

      @tag_lam ->
        dom_bytes = canonical_type_bytes(arena, left)

        <<@tag_lam::8, ty_bytes::binary, dom_bytes::binary,
          canonical_bytes(arena, right)::binary>>

      @tag_eq ->
        <<@tag_eq::8, canonical_bytes(arena, left)::binary, canonical_bytes(arena, right)::binary>>
    end
  end

  defp canonical_type_bytes(%__MODULE__{} = arena, ty_id) do
    case Map.fetch!(arena.type_table, ty_id) do
      :o -> <<0>>
      :i -> <<1>>
      {:base, name} -> <<2, byte_size(name)::16-big, name::binary>>
      {:arrow, d, c} -> <<3, canonical_type_bytes(arena, d)::binary, canonical_type_bytes(arena, c)::binary>>
    end
  end

  @doc """
  Exports the entire arena node table as a contiguous little/big-endian binary buffer
  (`12 * N` bytes) suitable for zero-copy Rustler NIF inspection.
  """
  @spec to_flat_binary(t()) :: binary()
  def to_flat_binary(%__MODULE__{} = arena) do
    count = map_size(arena.nodes)

    if count == 0 do
      <<>>
    else
      0..(count - 1)
      |> Enum.map(&Map.fetch!(arena.nodes, &1))
      |> IO.iodata_to_binary()
    end
  end
end
