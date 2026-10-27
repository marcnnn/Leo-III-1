defmodule Astraea.Input.Arith do
  @moduledoc """
  TPTP arithmetic: numerals, the interpreted symbols' types, and ground evaluation
  (the counterpart of Leo-III's `GroundArithmeticEval`).

  ## Representation

  `$int`, `$rat` and `$real` are arena sorts of those names. A numeral is a
  constant of such a sort whose name is the canonical literal of its value: `-3`
  for integers, `2/3` (reduced, positive denominator) for rationals and a decimal
  without exponent such as `150.0` or `-0.25` for reals. Equal values therefore
  share one constant, and distinct numerals denote distinct numbers. User symbols
  can never look like numerals (`Astraea.Input.IR.user_name/1`). Interpreted
  operations are constants named like the TPTP symbol (`$sum`, `$less`, ...) at the
  monomorphic type of their operands.

  ## Evaluation and soundness

  `eval/2` rewrites, bottom-up, every application of an interpreted symbol to
  numerals (and every equation between numerals of one arithmetic sort) to its
  value: a numeral, or `$true`/`$false` for predicates. Values are computed exactly
  on rationals; a `$real` is a rational with a terminating decimal expansion, and a
  result without one is left unevaluated. Division and the integer quotients and
  remainders by zero, and `$round` exactly halfway between two integers, are left
  unevaluated as well.

  Every rewrite `t ~> v` replaces a closed term by a numeral with `t = v` true in
  the standard model of TPTP arithmetic, so it preserves the truth value of the
  enclosing formula in every interpretation that interprets arithmetic as TPTP
  prescribes. `eval_clause/2` then drops literals that became false in all such
  interpretations (`$false`, `~ $true`). The clause it returns is thus a logical
  consequence of its parent, which is what the `:arith_eval` kernel rule of
  `Astraea.ProofChecker` re-checks by recomputing it. Outside of evaluation the
  prover treats arithmetic symbols as uninterpreted, which can only lose proofs.
  """

  alias Astraea.Arena
  alias Astraea.Input.IR

  import IR, only: [reject!: 1]

  @tag_const 1
  @tag_app 4
  @tag_lam 5
  @tag_eq 6
  @tag_not 7
  @tag_or 8
  @tag_forall 9

  @int {:base, "$int"}
  @rat {:base, "$rat"}
  @real {:base, "$real"}
  @o IR.o()

  @predicates ~w($less $lesseq $greater $greatereq)
  @unary ~w($uminus $floor $ceiling $truncate $round)
  @binary ~w($sum $difference $product $quotient $quotient_e $quotient_t $quotient_f
             $remainder_e $remainder_t $remainder_f)
  @tests ~w($is_int $is_rat)
  @conversions %{"$to_int" => @int, "$to_rat" => @rat, "$to_real" => @real}
  @operators @predicates ++ @unary ++ @binary ++ @tests ++ Map.keys(@conversions)

  @type value :: {:int | :rat | :real, integer(), pos_integer()}

  @spec types() :: [IR.ty()]
  def types, do: [@int, @rat, @real]

  @spec operator?(String.t()) :: boolean()
  def operator?(name), do: name in @operators

  @doc "Arity and monomorphic type of an interpreted symbol at operand type `ty`."
  @spec signature!(String.t(), IR.ty()) :: {pos_integer(), IR.ty()}
  def signature!(op, ty) do
    unless ty in types(), do: reject!("#{op} applied to #{IR.show(ty)}")
    if op == "$quotient" and ty == @int, do: reject!("$quotient on $int")

    cond do
      op in @predicates -> {2, IR.arrows([ty, ty], @o)}
      op in @unary -> {1, {:fun, ty, ty}}
      op in @binary -> {2, IR.arrows([ty, ty], ty)}
      op in @tests -> {1, {:fun, ty, @o}}
      true -> {1, {:fun, ty, Map.fetch!(@conversions, op)}}
    end
  end

  # ---------------------------------------------------------------------------
  # Numerals
  # ---------------------------------------------------------------------------

  @doc "Parses a TPTP numeral token into its sort and canonical constant name."
  @spec parse_numeral!(:integer | :rational | :real, String.t()) :: {IR.ty(), String.t()}
  def parse_numeral!(:integer, text) do
    case Integer.parse(String.trim_leading(text, "+")) do
      {n, ""} -> {@int, name({:int, n, 1})}
      _ -> reject!("bad integer #{text}")
    end
  end

  def parse_numeral!(:rational, text) do
    with [n, d] <- String.split(String.trim_leading(text, "+"), "/"),
         {n, ""} <- Integer.parse(n),
         {d, ""} when d > 0 <- Integer.parse(d) do
      {@rat, name(value(:rat, n, d))}
    else
      _ -> reject!("bad rational #{text}")
    end
  end

  def parse_numeral!(:real, text) do
    case Regex.run(~r/^([+-]?)(\d+)(?:\.(\d+))?(?:[eE]([+-]?\d+))?$/, text) do
      [_, sign, whole | rest] ->
        frac = Enum.at(rest, 0, "")
        exp = String.to_integer(Enum.at(rest, 1, "") |> then(&if(&1 == "", do: "0", else: &1)))
        if abs(exp) > 512, do: reject!("real exponent out of range: #{text}")
        digits = String.to_integer(whole <> frac)
        digits = if sign == "-", do: -digits, else: digits
        shift = exp - String.length(frac)

        v =
          if shift >= 0,
            do: value(:real, digits * pow10(shift), 1),
            else: value(:real, digits, pow10(-shift))

        {@real, name(v)}

      _ ->
        reject!("bad real #{text}")
    end
  end

  @doc "Canonical constant name of a value (`nil` for a real without decimal expansion)."
  @spec name(value()) :: String.t() | nil
  def name({:int, n, 1}), do: Integer.to_string(n)
  def name({:rat, n, d}), do: "#{n}/#{d}"

  def name({:real, n, d}) do
    case decimal_places(d) do
      nil ->
        nil

      k ->
        digits =
          (abs(n) * div(pow10(k), d)) |> Integer.to_string() |> String.pad_leading(k + 1, "0")

        {whole, frac} = String.split_at(digits, String.length(digits) - k)
        frac = String.trim_trailing(frac, "0")
        sign = if n < 0, do: "-", else: ""
        "#{sign}#{whole}.#{if frac == "", do: "0", else: frac}"
    end
  end

  # Smallest k with d | 10^k, if d has no prime factors other than 2 and 5.
  defp decimal_places(d) do
    {twos, d} = strip(d, 2, 0)
    {fives, d} = strip(d, 5, 0)
    if d == 1, do: max(twos, fives)
  end

  defp strip(d, p, k) when rem(d, p) == 0, do: strip(div(d, p), p, k + 1)
  defp strip(d, _p, k), do: {k, d}

  defp pow10(k), do: Integer.pow(10, k)

  defp value(kind, n, d) do
    g = Integer.gcd(n, d)
    g = if d < 0, do: -g, else: g
    {kind, div(n, g), div(d, g)}
  end

  @doc "The value of a numeral constant in `arena`, or `nil`."
  @spec numeral_value(Arena.t(), Arena.term_id()) :: value() | nil
  def numeral_value(%Arena{} = arena, id) do
    with {@tag_const, _, ty, sym, _} <- Arena.get_node(arena, id),
         {:base, sort} <- Map.get(arena.type_table, ty),
         kind when kind != nil <- sort_kind(sort),
         name when is_binary(name) <- Map.get(arena.symbol_names, sym),
         {:ok, v} <- parse_canonical(kind, name) do
      v
    else
      _ -> nil
    end
  end

  defp sort_kind("$int"), do: :int
  defp sort_kind("$rat"), do: :rat
  defp sort_kind("$real"), do: :real
  defp sort_kind(_), do: nil

  defp parse_canonical(kind, name) do
    {_ty, canonical} =
      case kind do
        :int -> parse_numeral!(:integer, name)
        :rat -> parse_numeral!(:rational, name)
        :real -> parse_numeral!(:real, name)
      end

    if canonical == name, do: {:ok, parse_value(kind, name)}, else: :error
  rescue
    IR.Error -> :error
  end

  defp parse_value(:int, name), do: {:int, String.to_integer(name), 1}

  defp parse_value(:rat, name) do
    [n, d] = String.split(name, "/")
    {:rat, String.to_integer(n), String.to_integer(d)}
  end

  defp parse_value(:real, name) do
    [whole, frac] = String.split(name, ".")
    neg? = String.starts_with?(whole, "-")
    digits = String.to_integer(String.trim_leading(whole, "-") <> frac)
    value(:real, if(neg?, do: -digits, else: digits), pow10(String.length(frac)))
  end

  # ---------------------------------------------------------------------------
  # Evaluation of values
  # ---------------------------------------------------------------------------

  @doc """
  Evaluates an interpreted symbol on numeral values; `nil` when the result is
  unspecified by TPTP (division by zero) or not representable.
  """
  @spec apply_op(String.t(), [value()]) :: value() | boolean() | nil
  def apply_op(op, [{k, n1, d1}, {k, n2, d2}]) when op in @predicates do
    c = n1 * d2 - n2 * d1

    case op do
      "$less" -> c < 0
      "$lesseq" -> c <= 0
      "$greater" -> c > 0
      "$greatereq" -> c >= 0
    end
  end

  def apply_op(op, [{k, n1, d1}, {k, n2, d2}]) when op in @binary do
    case op do
      "$sum" -> value(k, n1 * d2 + n2 * d1, d1 * d2)
      "$difference" -> value(k, n1 * d2 - n2 * d1, d1 * d2)
      "$product" -> value(k, n1 * n2, d1 * d2)
      _ when n2 == 0 -> nil
      "$quotient" -> value(k, n1 * d2, d1 * n2)
      "$quotient_" <> mode -> {k, quotient(mode, n1 * d2, d1 * n2), 1}
      "$remainder_" <> mode -> remainder(k, mode, {n1, d1}, {n2, d2})
    end
    |> representable()
  end

  def apply_op("$uminus", [{k, n, d}]), do: {k, -n, d}
  def apply_op("$floor", [{k, n, d}]), do: {k, floor_div(n, d), 1}
  def apply_op("$ceiling", [{k, n, d}]), do: {k, -floor_div(-n, d), 1}
  def apply_op("$truncate", [{k, n, d}]), do: {k, div(n, d), 1}

  def apply_op("$round", [{k, n, d}]) do
    # Halfway cases are left alone.
    if d == 2, do: nil, else: {k, floor_div(2 * n + d, 2 * d), 1}
  end

  def apply_op("$is_int", [{_, _n, d}]), do: d == 1
  def apply_op("$is_rat", [{_, _, _}]), do: true
  def apply_op("$to_int", [{_, n, d}]), do: {:int, floor_div(n, d), 1}
  def apply_op("$to_rat", [{_, n, d}]), do: {:rat, n, d}
  def apply_op("$to_real", [{_, n, d}]), do: representable({:real, n, d})
  def apply_op(_op, _args), do: nil

  # Quotient of the rationals `n/d` (d may be negative) rounded per TPTP mode.
  defp quotient("t", n, d), do: div(n, d)
  defp quotient("f", n, d), do: floor_div(n, d)

  defp quotient("e", n, d) do
    q = floor_div(n, abs(d))
    if d < 0, do: -q, else: q
  end

  defp remainder(k, mode, {n1, d1}, {n2, d2}) do
    q = quotient(mode, n1 * d2, d1 * n2)
    value(k, n1 * d2 - q * n2 * d1, d1 * d2)
  end

  defp floor_div(n, d) do
    {n, d} = if d < 0, do: {-n, -d}, else: {n, d}
    Integer.floor_div(n, d)
  end

  defp representable(nil), do: nil
  defp representable({:real, _, d} = v), do: if(decimal_places(d), do: v)
  defp representable(v), do: v

  # ---------------------------------------------------------------------------
  # Evaluation of arena terms
  # ---------------------------------------------------------------------------

  @doc "Evaluates all ground arithmetic subterms of `term_id`."
  @spec eval(Arena.t(), Arena.term_id()) :: {Arena.t(), Arena.term_id()}
  def eval(%Arena{} = arena, term_id) do
    {arena, id, _memo} = eval(arena, term_id, %{})
    {arena, id}
  end

  defp eval(arena, id, memo) do
    case Map.fetch(memo, id) do
      {:ok, res} ->
        {arena, res, memo}

      :error ->
        {arena, res, memo} = eval_node(arena, id, Arena.get_node(arena, id), memo)
        {arena, res, Map.put(memo, id, res)}
    end
  end

  defp eval_node(arena, id, {tag, _, _, l, r}, memo) do
    case tag do
      @tag_app ->
        {arena, l2, memo} = eval(arena, l, memo)
        {arena, r2, memo} = eval(arena, r, memo)
        {arena, app} = if {l2, r2} == {l, r}, do: {arena, id}, else: Arena.mk_app(arena, l2, r2)
        {arena, res} = reduce_app(arena, app)
        {arena, res, memo}

      @tag_eq ->
        {arena, l2, memo} = eval(arena, l, memo)
        {arena, r2, memo} = eval(arena, r, memo)

        {arena, res} =
          case {numeral_value(arena, l2), numeral_value(arena, r2)} do
            {{k, _, _} = a, {k, _, _} = b} -> truth(arena, a == b)
            _ -> if {l2, r2} == {l, r}, do: {arena, id}, else: Arena.mk_eq(arena, l2, r2)
          end

        {arena, res, memo}

      @tag_or ->
        {arena, l2, memo} = eval(arena, l, memo)
        {arena, r2, memo} = eval(arena, r, memo)
        rebuild(arena, id, {l, r}, {l2, r2}, memo, &Arena.mk_or(&1, l2, r2))

      @tag_not ->
        {arena, l2, memo} = eval(arena, l, memo)
        rebuild(arena, id, l, l2, memo, &Arena.mk_not(&1, l2))

      @tag_lam ->
        {arena, r2, memo} = eval(arena, r, memo)
        rebuild(arena, id, r, r2, memo, &Arena.mk_lam(&1, l, r2))

      @tag_forall ->
        {arena, r2, memo} = eval(arena, r, memo)
        rebuild(arena, id, r, r2, memo, &Arena.mk_forall(&1, l, r2))

      _ ->
        {arena, id, memo}
    end
  end

  defp rebuild(arena, id, old, old, memo, _mk), do: {arena, id, memo}

  defp rebuild(arena, _id, _old, _new, memo, mk) do
    {arena, res} = mk.(arena)
    {arena, res, memo}
  end

  defp reduce_app(arena, app) do
    {head, args} = spine(arena, app, [])

    with {@tag_const, _, _, sym, _} <- Arena.get_node(arena, head),
         op when is_binary(op) <- Map.get(arena.symbol_names, sym),
         true <- op in @operators,
         values when is_list(values) <- numerals(arena, args),
         true <- length(values) == arity(op),
         result when not is_nil(result) <- apply_op(op, values) do
      result_term(arena, result)
    else
      _ -> {arena, app}
    end
  end

  defp arity(op) when op in @predicates or op in @binary, do: 2
  defp arity(_op), do: 1

  defp numerals(arena, args) do
    values = Enum.map(args, &numeral_value(arena, &1))
    if Enum.all?(values), do: values
  end

  defp result_term(arena, b) when is_boolean(b), do: truth(arena, b)

  defp result_term(arena, {kind, _, _} = v) do
    sort = %{int: "$int", rat: "$rat", real: "$real"} |> Map.fetch!(kind)
    {arena, ty} = Arena.intern_type(arena, {:base, sort})
    Arena.mk_const(arena, name(v), ty)
  end

  defp truth(arena, true), do: Arena.mk_const(arena, "$true", :o)
  defp truth(arena, false), do: Arena.mk_const(arena, "$false", :o)

  defp spine(arena, id, args) do
    case Arena.get_node(arena, id) do
      {@tag_app, _, _, f, a} -> spine(arena, f, [a | args])
      _ -> {id, args}
    end
  end

  # ---------------------------------------------------------------------------
  # Clauses (prover hook and kernel rule)
  # ---------------------------------------------------------------------------

  @doc """
  Evaluates every literal of a clause and drops the literals that became false.
  This is the conclusion the `:arith_eval` kernel rule accepts for a parent clause.
  """
  @spec eval_clause(Arena.t(), MapSet.t()) :: {Arena.t(), MapSet.t()}
  def eval_clause(%Arena{} = arena, clause) do
    {arena, true_id} = truth(arena, true)
    {arena, false_id} = truth(arena, false)

    Enum.reduce(clause, {arena, MapSet.new()}, fn {pol, atom}, {ar, acc} ->
      {ar, atom2} = eval(ar, atom)

      case {pol, atom2} do
        {:pos, ^false_id} -> {ar, acc}
        {:neg, ^true_id} -> {ar, acc}
        lit -> {ar, MapSet.put(acc, lit)}
      end
    end)
  end

  @doc """
  Prover-facing simplification: `{arena, :unchanged}`, `{arena, :tautology}` when
  evaluation made a literal true, or `{arena, {:simplified, clause}}`, to be
  justified by the kernel step `{:arith_eval, id, parent_id, clause}`.
  """
  @spec simplify_clause(Arena.t(), MapSet.t()) ::
          {Arena.t(), :unchanged | :tautology | {:simplified, MapSet.t()}}
  def simplify_clause(%Arena{} = arena, clause) do
    {arena, result} = eval_clause(arena, clause)
    {arena, true_id} = truth(arena, true)
    {arena, false_id} = truth(arena, false)

    cond do
      result == clause -> {arena, :unchanged}
      MapSet.member?(result, {:pos, true_id}) -> {arena, :tautology}
      MapSet.member?(result, {:neg, false_id}) -> {arena, :tautology}
      true -> {arena, {:simplified, result}}
    end
  end
end
