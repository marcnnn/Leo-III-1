defmodule Astraea.Arena do
  @moduledoc """
  Layer 2 Canonical Flat Logic IR (u32-indexed hash-consed arena) for monomorphic THF0.

  Matches the binary node layout defined in `Notes/master_thesis_proposal.md`:
  `<<tag::8, flags::8, type_id::16, left::32, right::32>>` (12 bytes/node),
  supporting:
    1. Spine / de Bruijn higher-order terms with reference beta-eta normalization,
    2. Binder-free typed combinator lowering (S, K, I, B, C) and reduction,
    3. Content-addressed Skolem symbol derivation (`skolem_hash/2`), and
    4. Reference Knuth-Bendix Ordering (`kbo_compare/3`) & Feature Vector (`feature_vector/2`).
  """

  import Bitwise

  @type type_id :: non_neg_integer()
  @type term_id :: non_neg_integer()

  # Built-in base types
  @ty_o 0
  @ty_i 1

  # Node tags (u8) — kept identical between Elixir Layer 2 and Rust Layer 4 NIF
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

  # Node flag bits
  @flag_has_bvar 0x01
  @flag_has_fvar 0x02

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

  @spec type_of(t(), term_id()) :: type_id()
  def type_of(%__MODULE__{} = arena, term_id) do
    {_tag, _flags, ty_id, _left, _right} = get_node(arena, term_id)
    ty_id
  end

  @doc """
  Encodes a single 12-byte arena node: `<<tag::8, flags::8, type_id::16, left::32, right::32>>`.
  """
  @spec encode_node(non_neg_integer(), non_neg_integer(), type_id(), non_neg_integer(), non_neg_integer()) ::
          <<_::96>>
  def encode_node(tag, flags, type_id, left, right) do
    <<tag::8, flags::8, type_id::16-big, left::32-big, right::32-big>>
  end

  @spec decode_node(<<_::96>>) ::
          {non_neg_integer(), non_neg_integer(), type_id(), non_neg_integer(), non_neg_integer()}
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
    intern_node(arena, @tag_bvar, @flag_has_bvar, ty_id, de_bruijn_idx, 0)
  end

  @spec mk_fvar(t(), non_neg_integer(), term()) :: {t(), term_id()}
  def mk_fvar(%__MODULE__{} = arena, var_id, ty) when var_id >= 0 do
    {arena, ty_id} = intern_type(arena, ty)
    intern_node(arena, @tag_fvar, @flag_has_fvar, ty_id, var_id, 0)
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
              "Type mismatch in application: expected {:arrow, #{a_ty}, _} (#{inspect(arena.type_table[a_ty])}), got #{inspect(other)}"
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

    intern_node(arena, @tag_eq, bor(l_flags, r_flags), @ty_o, lhs_id, rhs_id)
  end

  @spec mk_not(t(), term_id()) :: {t(), term_id()}
  def mk_not(%__MODULE__{} = arena, arg_id) do
    {_, flags, ty_id, _, _} = get_node(arena, arg_id)

    if ty_id != @ty_o do
      raise ArgumentError, "Negation expects $o, got type_id #{ty_id}"
    end

    intern_node(arena, @tag_not, flags, @ty_o, arg_id, 0)
  end

  @spec mk_or(t(), term_id(), term_id()) :: {t(), term_id()}
  def mk_or(%__MODULE__{} = arena, lhs_id, rhs_id) do
    {_, l_flags, l_ty, _, _} = get_node(arena, lhs_id)
    {_, r_flags, r_ty, _, _} = get_node(arena, rhs_id)

    if l_ty != @ty_o or r_ty != @ty_o do
      raise ArgumentError, "Disjunction expects $o operands"
    end

    intern_node(arena, @tag_or, bor(l_flags, r_flags), @ty_o, lhs_id, rhs_id)
  end

  @spec mk_and(t(), term_id(), term_id()) :: {t(), term_id()}
  def mk_and(%__MODULE__{} = arena, lhs_id, rhs_id) do
    {arena, nl} = mk_not(arena, lhs_id)
    {arena, nr} = mk_not(arena, rhs_id)
    {arena, disj} = mk_or(arena, nl, nr)
    mk_not(arena, disj)
  end

  @spec mk_imp(t(), term_id(), term_id()) :: {t(), term_id()}
  def mk_imp(%__MODULE__{} = arena, lhs_id, rhs_id) do
    {arena, nl} = mk_not(arena, lhs_id)
    mk_or(arena, nl, rhs_id)
  end

  @spec mk_iff(t(), term_id(), term_id()) :: {t(), term_id()}
  def mk_iff(%__MODULE__{} = arena, lhs_id, rhs_id) do
    mk_eq(arena, lhs_id, rhs_id)
  end

  @spec mk_forall(t(), term(), term_id()) :: {t(), term_id()}
  def mk_forall(%__MODULE__{} = arena, var_ty, body_id) do
    {arena, dom_id} = intern_type(arena, var_ty)
    {_, b_flags, cod_id, _, _} = get_node(arena, body_id)

    if cod_id != @ty_o do
      raise ArgumentError, "Forall body must have type $o"
    end

    intern_node(arena, @tag_forall, b_flags, @ty_o, dom_id, body_id)
  end

  @spec mk_exists(t(), term(), term_id()) :: {t(), term_id()}
  def mk_exists(%__MODULE__{} = arena, var_ty, body_id) do
    {arena, neg_body} = mk_not(arena, body_id)
    {arena, all_neg} = mk_forall(arena, var_ty, neg_body)
    mk_not(arena, all_neg)
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

  # ---------------------------------------------------------------------------
  # Reference De Bruijn Shifting, Substitution, and Beta-Eta Normalization
  # ---------------------------------------------------------------------------

  @doc """
  Shifts bound de Bruijn indices >= `cutoff` by `delta` (which may be negative).
  """
  @spec shift(t(), term_id(), integer(), non_neg_integer()) :: {t(), term_id()}
  def shift(%__MODULE__{} = arena, term_id, 0, _cutoff), do: {arena, term_id}

  def shift(%__MODULE__{} = arena, term_id, delta, cutoff) do
    {tag, flags, ty_id, left, right} = get_node(arena, term_id)

    if band(flags, @flag_has_bvar) == 0 do
      {arena, term_id}
    else
      case tag do
        @tag_bvar ->
          if left >= cutoff do
            mk_bvar(arena, left + delta, ty_id)
          else
            {arena, term_id}
          end

        @tag_app ->
          {arena, l2} = shift(arena, left, delta, cutoff)
          {arena, r2} = shift(arena, right, delta, cutoff)
          mk_app(arena, l2, r2)

        @tag_lam ->
          {arena, b2} = shift(arena, right, delta, cutoff + 1)
          mk_lam(arena, left, b2)

        @tag_forall ->
          {arena, b2} = shift(arena, right, delta, cutoff + 1)
          mk_forall(arena, left, b2)

        @tag_eq ->
          {arena, l2} = shift(arena, left, delta, cutoff)
          {arena, r2} = shift(arena, right, delta, cutoff)
          mk_eq(arena, l2, r2)

        @tag_or ->
          {arena, l2} = shift(arena, left, delta, cutoff)
          {arena, r2} = shift(arena, right, delta, cutoff)
          mk_or(arena, l2, r2)

        @tag_not ->
          {arena, l2} = shift(arena, left, delta, cutoff)
          mk_not(arena, l2)

        _ ->
          {arena, term_id}
      end
    end
  end

  @doc """
  Substitutes bound variable `bvar_idx` with `replacement_id` inside `body_id`.
  """
  @spec subst_bvar(t(), term_id(), non_neg_integer(), term_id()) :: {t(), term_id()}
  def subst_bvar(%__MODULE__{} = arena, body_id, bvar_idx, replacement_id) do
    {tag, flags, ty_id, left, right} = get_node(arena, body_id)

    if band(flags, @flag_has_bvar) == 0 do
      {arena, body_id}
    else
      case tag do
        @tag_bvar ->
          cond do
            left == bvar_idx -> {arena, replacement_id}
            left > bvar_idx -> mk_bvar(arena, left - 1, ty_id)
            true -> {arena, body_id}
          end

        @tag_app ->
          {arena, l2} = subst_bvar(arena, left, bvar_idx, replacement_id)
          {arena, r2} = subst_bvar(arena, right, bvar_idx, replacement_id)
          mk_app(arena, l2, r2)

        @tag_lam ->
          {arena, rep_shifted} = shift(arena, replacement_id, 1, 0)
          {arena, b2} = subst_bvar(arena, right, bvar_idx + 1, rep_shifted)
          mk_lam(arena, left, b2)

        @tag_forall ->
          {arena, rep_shifted} = shift(arena, replacement_id, 1, 0)
          {arena, b2} = subst_bvar(arena, right, bvar_idx + 1, rep_shifted)
          mk_forall(arena, left, b2)

        @tag_eq ->
          {arena, l2} = subst_bvar(arena, left, bvar_idx, replacement_id)
          {arena, r2} = subst_bvar(arena, right, bvar_idx, replacement_id)
          mk_eq(arena, l2, r2)

        @tag_or ->
          {arena, l2} = subst_bvar(arena, left, bvar_idx, replacement_id)
          {arena, r2} = subst_bvar(arena, right, bvar_idx, replacement_id)
          mk_or(arena, l2, r2)

        @tag_not ->
          {arena, l2} = subst_bvar(arena, left, bvar_idx, replacement_id)
          mk_not(arena, l2)

        _ ->
          {arena, body_id}
      end
    end
  end

  @doc """
  Computes the full beta-eta normal form of `term_id` in the pure Elixir Reference Arena.
  """
  @spec beta_eta_norm(t(), term_id()) :: {t(), term_id()}
  def beta_eta_norm(%__MODULE__{} = arena, term_id) do
    {tag, _flags, _ty_id, left, right} = get_node(arena, term_id)

    case tag do
      @tag_app ->
        {arena, f_norm} = beta_eta_norm(arena, left)
        {arena, a_norm} = beta_eta_norm(arena, right)

        case get_node(arena, f_norm) do
          {@tag_lam, _, _, _dom, body_id} ->
            {arena, subbed} = subst_bvar(arena, body_id, 0, a_norm)
            beta_eta_norm(arena, subbed)

          _ ->
            mk_app(arena, f_norm, a_norm)
        end

      @tag_lam ->
        {arena, b_norm} = beta_eta_norm(arena, right)

        # Eta-contraction: (^ [X]: (F @ X)) -> F when BVar(0) does not occur free in F
        case get_node(arena, b_norm) do
          {@tag_app, _, _, fun_id, arg_id} ->
            case get_node(arena, arg_id) do
              {@tag_bvar, _, _, 0, _} ->
                if not occurs_bvar?(arena, fun_id, 0) do
                  shift(arena, fun_id, -1, 1)
                else
                  mk_lam(arena, left, b_norm)
                end

              _ ->
                mk_lam(arena, left, b_norm)
            end

          _ ->
            mk_lam(arena, left, b_norm)
        end

      @tag_forall ->
        {arena, b_norm} = beta_eta_norm(arena, right)
        mk_forall(arena, left, b_norm)

      @tag_eq ->
        {arena, l_norm} = beta_eta_norm(arena, left)
        {arena, r_norm} = beta_eta_norm(arena, right)
        mk_eq(arena, l_norm, r_norm)

      @tag_or ->
        {arena, l_norm} = beta_eta_norm(arena, left)
        {arena, r_norm} = beta_eta_norm(arena, right)
        mk_or(arena, l_norm, r_norm)

      @tag_not ->
        {arena, l_norm} = beta_eta_norm(arena, left)
        mk_not(arena, l_norm)

      _ ->
        {arena, term_id}
    end
  end

  @spec occurs_bvar?(t(), term_id(), non_neg_integer()) :: boolean()
  def occurs_bvar?(%__MODULE__{} = arena, term_id, target_idx) do
    {tag, flags, _ty, left, right} = get_node(arena, term_id)

    if band(flags, @flag_has_bvar) == 0 do
      false
    else
      case tag do
        @tag_bvar ->
          left == target_idx

        @tag_app ->
          occurs_bvar?(arena, left, target_idx) or occurs_bvar?(arena, right, target_idx)

        @tag_lam ->
          occurs_bvar?(arena, right, target_idx + 1)

        @tag_forall ->
          occurs_bvar?(arena, right, target_idx + 1)

        @tag_eq ->
          occurs_bvar?(arena, left, target_idx) or occurs_bvar?(arena, right, target_idx)

        @tag_or ->
          occurs_bvar?(arena, left, target_idx) or occurs_bvar?(arena, right, target_idx)

        @tag_not ->
          occurs_bvar?(arena, left, target_idx)

        _ ->
          false
      end
    end
  end

  # ---------------------------------------------------------------------------
  # Typed Combinator Lowering (S, K, I, B, C) & Combinator Reduction
  # ---------------------------------------------------------------------------

  @doc """
  Lowers lambda-abstractions into binder-free typed Schönfinkel-Curry combinators
  (`S, K, I, B, C`) via Turner-style bracket abstraction, eliminating bound variables.
  """
  @spec to_combinators(t(), term_id()) :: {t(), term_id()}
  def to_combinators(%__MODULE__{} = arena, term_id) do
    {tag, _flags, _ty_id, left, right} = get_node(arena, term_id)

    case tag do
      @tag_app ->
        {arena, l_c} = to_combinators(arena, left)
        {arena, r_c} = to_combinators(arena, right)
        mk_app(arena, l_c, r_c)

      @tag_lam ->
        # First convert inner lambdas bottom-up, then bracket-abstract BVar(0)
        {arena, body_c} = to_combinators(arena, right)
        bracket_abstract(arena, left, body_c)

      @tag_eq ->
        {arena, l_c} = to_combinators(arena, left)
        {arena, r_c} = to_combinators(arena, right)
        mk_eq(arena, l_c, r_c)

      @tag_or ->
        {arena, l_c} = to_combinators(arena, left)
        {arena, r_c} = to_combinators(arena, right)
        mk_or(arena, l_c, r_c)

      @tag_not ->
        {arena, l_c} = to_combinators(arena, left)
        mk_not(arena, l_c)

      _ ->
        {arena, term_id}
    end
  end

  defp bracket_abstract(%__MODULE__{} = arena, var_ty, body_id) do
    {tag, _flags, body_ty, left, right} = get_node(arena, body_id)

    cond do
      # [x] x  ==>  I : var_ty > var_ty
      tag == @tag_bvar and left == 0 ->
        {arena, i_ty} = intern_type(arena, {:arrow, var_ty, var_ty})
        mk_comb(arena, :i, i_ty)

      # [x] M (where x not in M)  ==>  K @ M
      not occurs_bvar?(arena, body_id, 0) ->
        {arena, shifted} = shift(arena, body_id, -1, 1)
        {arena, ret_ty} = intern_type(arena, {:arrow, var_ty, body_ty})
        {arena, k_ty} = intern_type(arena, {:arrow, body_ty, ret_ty})
        {arena, k_node} = mk_comb(arena, :k, k_ty)
        mk_app(arena, k_node, shifted)

      # [x] (F @ G)
      tag == @tag_app ->
        f_has = occurs_bvar?(arena, left, 0)
        g_has = occurs_bvar?(arena, right, 0)

        cond do
          # Eta rule: [x] (F @ x) ==> F
          not f_has and elem(get_node(arena, right), 0) == @tag_bvar and
              elem(get_node(arena, right), 3) == 0 ->
            shift(arena, left, -1, 1)

          # B combinator: [x] (F @ G) when x only in G ==> B @ F @ ([x] G)
          not f_has and g_has ->
            {arena, f_s} = shift(arena, left, -1, 1)
            {arena, g_abs} = bracket_abstract(arena, var_ty, right)
            f_ty = type_of(arena, f_s)
            g_abs_ty = type_of(arena, g_abs)
            {arena, res_ty} = intern_type(arena, {:arrow, var_ty, body_ty})
            {arena, b1} = intern_type(arena, {:arrow, g_abs_ty, res_ty})
            {arena, b_ty} = intern_type(arena, {:arrow, f_ty, b1})
            {arena, b_node} = mk_comb(arena, :b, b_ty)
            {arena, bf} = mk_app(arena, b_node, f_s)
            mk_app(arena, bf, g_abs)

          # C combinator: [x] (F @ G) when x only in F ==> C @ ([x] F) @ G
          f_has and not g_has ->
            {arena, f_abs} = bracket_abstract(arena, var_ty, left)
            {arena, g_s} = shift(arena, right, -1, 1)
            f_abs_ty = type_of(arena, f_abs)
            g_ty = type_of(arena, g_s)
            {arena, res_ty} = intern_type(arena, {:arrow, var_ty, body_ty})
            {arena, c1} = intern_type(arena, {:arrow, g_ty, res_ty})
            {arena, c_ty} = intern_type(arena, {:arrow, f_abs_ty, c1})
            {arena, c_node} = mk_comb(arena, :c, c_ty)
            {arena, cf} = mk_app(arena, c_node, f_abs)
            mk_app(arena, cf, g_s)

          # S combinator: [x] (F @ G) when x in both ==> S @ ([x] F) @ ([x] G)
          true ->
            {arena, f_abs} = bracket_abstract(arena, var_ty, left)
            {arena, g_abs} = bracket_abstract(arena, var_ty, right)
            f_abs_ty = type_of(arena, f_abs)
            g_abs_ty = type_of(arena, g_abs)
            {arena, res_ty} = intern_type(arena, {:arrow, var_ty, body_ty})
            {arena, s1} = intern_type(arena, {:arrow, g_abs_ty, res_ty})
            {arena, s_ty} = intern_type(arena, {:arrow, f_abs_ty, s1})
            {arena, s_node} = mk_comb(arena, :s, s_ty)
            {arena, sf} = mk_app(arena, s_node, f_abs)
            mk_app(arena, sf, g_abs)
        end
    end
  end

  @doc """
  Reduces combinator redexes (`I x -> x`, `K x y -> x`, `B f g x -> f (g x)`,
  `C f g x -> f x g`, `S f g x -> f x (g x)`) to normal form.
  """
  @spec comb_norm(t(), term_id()) :: {t(), term_id()}
  def comb_norm(%__MODULE__{} = arena, term_id) do
    {tag, _flags, _ty_id, left, right} = get_node(arena, term_id)

    case tag do
      @tag_app ->
        {arena, f} = comb_norm(arena, left)
        {arena, x} = comb_norm(arena, right)
        reduce_comb_spine(arena, f, x)

      @tag_eq ->
        {arena, l} = comb_norm(arena, left)
        {arena, r} = comb_norm(arena, right)
        mk_eq(arena, l, r)

      @tag_or ->
        {arena, l} = comb_norm(arena, left)
        {arena, r} = comb_norm(arena, right)
        mk_or(arena, l, r)

      @tag_not ->
        {arena, l} = comb_norm(arena, left)
        mk_not(arena, l)

      _ ->
        {arena, term_id}
    end
  end

  defp reduce_comb_spine(%__MODULE__{} = arena, f_id, x_id) do
    case get_node(arena, f_id) do
      # I @ x  ==>  x
      {@tag_comb, _, _, @comb_i, _} ->
        {arena, x_id}

      # (K @ a) @ x  ==>  a
      {@tag_app, _, _, k_id, a_id} ->
        case get_node(arena, k_id) do
          {@tag_comb, _, _, @comb_k, _} ->
            {arena, a_id}

          # ((C @ f) @ g) @ x  ==>  (f @ x) @ g
          # ((B @ f) @ g) @ x  ==>  f @ (g @ x)
          # ((S @ f) @ g) @ x  ==>  (f @ x) @ (g @ x)
          {@tag_app, _, _, comb_id, arg1_id} ->
            case get_node(arena, comb_id) do
              {@tag_comb, _, _, @comb_b, _} ->
                {arena, gx} = mk_app(arena, a_id, x_id)
                {arena, fgx} = mk_app(arena, arg1_id, gx)
                comb_norm(arena, fgx)

              {@tag_comb, _, _, @comb_c, _} ->
                {arena, fx} = mk_app(arena, arg1_id, x_id)
                {arena, fxg} = mk_app(arena, fx, a_id)
                comb_norm(arena, fxg)

              {@tag_comb, _, _, @comb_s, _} ->
                {arena, fx} = mk_app(arena, arg1_id, x_id)
                {arena, gx} = mk_app(arena, a_id, x_id)
                {arena, s_res} = mk_app(arena, fx, gx)
                comb_norm(arena, s_res)

              _ ->
                mk_app(arena, f_id, x_id)
            end

          _ ->
            mk_app(arena, f_id, x_id)
        end

      _ ->
        mk_app(arena, f_id, x_id)
    end
  end

  # ---------------------------------------------------------------------------
  # Reference Knuth-Bendix Ordering (KBO) & SIMD Feature Vector (FVIndex)
  # ---------------------------------------------------------------------------

  @doc """
  Computes the structural weight and free-variable multiset of `term_id` for KBO.
  """
  @spec term_weight_and_vars(t(), term_id()) :: {pos_integer(), %{non_neg_integer() => pos_integer()}}
  def term_weight_and_vars(%__MODULE__{} = arena, term_id) do
    {tag, _flags, _ty_id, left, right} = get_node(arena, term_id)

    case tag do
      @tag_fvar ->
        {1, %{left => 1}}

      @tag_bvar ->
        {1, %{}}

      t when t in [@tag_const, @tag_comb, @tag_skolem] ->
        {1, %{}}

      @tag_not ->
        {w, v} = term_weight_and_vars(arena, left)
        {1 + w, v}

      t when t in [@tag_lam, @tag_forall] ->
        {w, v} = term_weight_and_vars(arena, right)
        {1 + w, v}

      t when t in [@tag_app, @tag_eq, @tag_or] ->
        {wl, vl} = term_weight_and_vars(arena, left)
        {wr, vr} = term_weight_and_vars(arena, right)
        {1 + wl + wr, Map.merge(vl, vr, fn _k, c1, c2 -> c1 + c2 end)}
    end
  end

  @doc """
  Reference Knuth-Bendix Ordering comparison (`:gt | :lt | :eq | :inc`) between two
  terms `s_id` and `t_id`. Mirrors the native Rust KBO kernel for Gate 2 differential testing.
  """
  @spec kbo_compare(t(), term_id(), term_id()) :: :gt | :lt | :eq | :inc
  def kbo_compare(%__MODULE__{}, term_id, term_id), do: :eq

  def kbo_compare(%__MODULE__{} = arena, s_id, t_id) do
    {ws, vs} = term_weight_and_vars(arena, s_id)
    {wt, vt} = term_weight_and_vars(arena, t_id)

    s_ge_t = vars_dominate?(vs, vt)
    t_ge_s = vars_dominate?(vt, vs)

    cond do
      s_ge_t and ws > wt ->
        :gt

      t_ge_s and wt > ws ->
        :lt

      s_ge_t and t_ge_s and ws == wt ->
        kbo_lex(arena, s_id, t_id)

      true ->
        :inc
    end
  end

  defp vars_dominate?(v_big, v_small) do
    Enum.all?(v_small, fn {var, count} -> Map.get(v_big, var, 0) >= count end)
  end

  defp kbo_lex(%__MODULE__{} = arena, s_id, t_id) do
    {ts, _, _, ls, rs} = get_node(arena, s_id)
    {tt, _, _, lt, rt} = get_node(arena, t_id)

    cond do
      ts != tt ->
        if ts > tt, do: :gt, else: :lt

      ts in [@tag_const, @tag_comb, @tag_skolem, @tag_bvar] ->
        cond do
          ls > lt -> :gt
          ls < lt -> :lt
          true -> :eq
        end

      ts == @tag_not ->
        kbo_compare(arena, ls, lt)

      ts in [@tag_lam, @tag_forall] ->
        if ls != lt do
          if ls > lt, do: :gt, else: :lt
        else
          kbo_compare(arena, rs, rt)
        end

      ts in [@tag_app, @tag_eq, @tag_or] ->
        case kbo_compare(arena, ls, lt) do
          :eq -> kbo_compare(arena, rs, rt)
          other -> other
        end

      true ->
        :inc
    end
  end

  @doc """
  Computes a 16-lane u32 feature vector (`FVIndex`) for SIMD forward/backward
  subsumption filtering (Schulz 2013):
    lane 0: total node count (size)
    lane 1: tree depth
    lane 2..12: counts of node tags 1..11
    lane 13..15: hashed symbol signature buckets (mod 3)
  A clause/term with feature vector `fv_a` can subsume `fv_b` only if
  `forall i in 0..15: fv_a[i] <= fv_b[i]`.
  """
  @spec feature_vector(t(), term_id()) :: [non_neg_integer()]
  def feature_vector(%__MODULE__{} = arena, term_id) do
    counts = :counters.new(16, [:atomics])
    depth = walk_fv(arena, term_id, counts)
    :counters.put(counts, 2, depth)
    for i <- 1..16, do: :counters.get(counts, i)
  end

  @spec fv_subsumes?([non_neg_integer()], [non_neg_integer()]) :: boolean()
  def fv_subsumes?(fv_cand, fv_target) do
    Enum.zip_with(fv_cand, fv_target, fn a, b -> a <= b end)
    |> Enum.all?()
  end

  defp walk_fv(%__MODULE__{} = arena, term_id, counts) do
    {tag, _flags, _ty_id, left, right} = get_node(arena, term_id)
    # Lane 0 (index 1 in :counters): size
    :counters.add(counts, 1, 1)
    # Lanes 2..12 (indices 3..13 in :counters): tag counts for tags 1..11
    if tag >= 1 and tag <= 11 do
      :counters.add(counts, tag + 2, 1)
    end

    case tag do
      @tag_const ->
        bucket = 14 + rem(left, 3)
        :counters.add(counts, bucket, 1)
        1

      t when t in [@tag_bvar, @tag_fvar, @tag_comb, @tag_skolem] ->
        1

      @tag_not ->
        1 + walk_fv(arena, left, counts)

      t when t in [@tag_lam, @tag_forall] ->
        1 + walk_fv(arena, right, counts)

      t when t in [@tag_app, @tag_eq, @tag_or] ->
        dl = walk_fv(arena, left, counts)
        dr = walk_fv(arena, right, counts)
        1 + max(dl, dr)
    end
  end

  # ---------------------------------------------------------------------------
  # Content-Addressed Skolemization & Zero-Copy Binary Export
  # ---------------------------------------------------------------------------

  @doc """
  Serializes a term DAG rooted at `root_id` into a canonical structural binary
  (independent of arena insertion order) and computes its 32-bit content-addressed
  Skolem hash.
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

      @tag_fvar ->
        <<@tag_fvar::8, ty_bytes::binary, left::32-big>>

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

      @tag_forall ->
        dom_bytes = canonical_type_bytes(arena, left)

        <<@tag_forall::8, ty_bytes::binary, dom_bytes::binary,
          canonical_bytes(arena, right)::binary>>

      @tag_eq ->
        <<@tag_eq::8, canonical_bytes(arena, left)::binary, canonical_bytes(arena, right)::binary>>

      @tag_or ->
        <<@tag_or::8, canonical_bytes(arena, left)::binary, canonical_bytes(arena, right)::binary>>

      @tag_not ->
        <<@tag_not::8, canonical_bytes(arena, left)::binary>>
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
  Exports the entire arena node table as a contiguous big-endian binary buffer
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
