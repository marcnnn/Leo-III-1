defmodule Astraea.Input.IR do
  @moduledoc """
  Named, explicitly typed intermediate representation between the TPTP CST and the
  `Astraea.Arena`.

  Elaboration (`Astraea.Input.Elaborator`) produces it for every input language,
  the modal embedding and monomorphization rewrite it, and `Astraea.Input.Emitter`
  translates the result into de Bruijn arena terms.

  Types:
    * `{:base, name}` — `$o`, `$i`, `$int`, `$rat`, `$real` or a user/generated sort,
    * `{:tapp, name, [type]}` — an applied TH1 type constructor,
    * `{:fun, dom, cod}`, `{:tuple, [type]}`, and `{:tvar, id}`.

  Terms carry the types of their leaves; every binder has a unique integer id:
    * `{:const, name, type_args, type}` and `{:var, id, type}`,
    * `{:app, fun, arg}` and `{:lam, id, type, body}`,
    * `{:quant, :all | :ex, id, type, body}`, `{:not, t}`, `{:eq, l, r}`,
    * `{:bin, :and | :or | :imp | :iff, l, r}`, and
    * `{:modal, :box | :dia, index, t}` (removed by `Astraea.Input.Modal`).

  Constant names are final arena names. User symbols are mangled by `user_name/1`
  so that they can never collide with interpreted or generated names, all of
  which start with `$` or are numerals.
  """

  @type ty ::
          {:base, String.t()}
          | {:tapp, String.t(), [ty()]}
          | {:fun, ty(), ty()}
          | {:tuple, [ty()]}
          | {:tvar, non_neg_integer()}

  @type tm ::
          {:const, String.t(), [ty()], ty()}
          | {:var, non_neg_integer(), ty()}
          | {:app, tm(), tm()}
          | {:lam, non_neg_integer(), ty(), tm()}
          | {:quant, :all | :ex, non_neg_integer(), ty(), tm()}
          | {:not, tm()}
          | {:eq, tm(), tm()}
          | {:bin, :and | :or | :imp | :iff, tm(), tm()}
          | {:modal, :box | :dia, String.t() | nil, tm()}

  @o {:base, "$o"}
  @i {:base, "$i"}

  defmodule Error do
    @moduledoc "Raised for input that cannot be translated faithfully; the problem is rejected."
    defexception [:message]
  end

  @spec o() :: ty()
  def o, do: @o

  @spec i() :: ty()
  def i, do: @i

  @doc "Raises `Astraea.Input.IR.Error`, rejecting the problem."
  @spec reject!(String.t()) :: no_return()
  def reject!(message), do: raise(Error, message: message)

  @doc """
  Injective renaming of user symbols: names that could be read as a numeral, an
  interpreted `$` word, a distinct object or an already mangled name get a `~` prefix.
  """
  @spec user_name(String.t()) :: String.t()
  def user_name(name) do
    if name == "" or String.starts_with?(name, ["$", "~", "\"", "+", "-"]) or
         String.at(name, 0) in ~w(0 1 2 3 4 5 6 7 8 9) do
      "~" <> name
    else
      name
    end
  end

  # ---------------------------------------------------------------------------
  # Constructors
  # ---------------------------------------------------------------------------

  @spec true_() :: tm()
  def true_, do: {:const, "$true", [], @o}

  @spec false_() :: tm()
  def false_, do: {:const, "$false", [], @o}

  @spec app(tm(), [tm()]) :: tm()
  def app(fun, args), do: Enum.reduce(args, fun, &{:app, &2, &1})

  @spec arrows([ty()], ty()) :: ty()
  def arrows(doms, cod), do: List.foldr(doms, cod, &{:fun, &1, &2})

  @spec conj([tm()]) :: tm()
  def conj([]), do: true_()
  def conj(ts), do: Enum.reduce(tl(ts), hd(ts), &{:bin, :and, &2, &1})

  # ---------------------------------------------------------------------------
  # Typing
  # ---------------------------------------------------------------------------

  @doc "The type of a well-typed term; raises on ill-typed applications."
  @spec type_of(tm()) :: ty()
  def type_of({:const, _, _, ty}), do: ty
  def type_of({:var, _, ty}), do: ty
  def type_of({:lam, _, ty, body}), do: {:fun, ty, type_of(body)}

  def type_of({:app, f, _}) do
    case type_of(f) do
      {:fun, _, cod} -> cod
      other -> reject!("application of a term of non-function type #{show(other)}")
    end
  end

  def type_of(_formula), do: @o

  @doc "Checked application: the argument type must equal the domain."
  @spec apply_checked(tm(), tm()) :: tm()
  def apply_checked(f, a) do
    case type_of(f) do
      {:fun, dom, _} ->
        if dom == type_of(a),
          do: {:app, f, a},
          else: reject!("argument of type #{show(type_of(a))} where #{show(dom)} is expected")

      other ->
        reject!("cannot apply a term of type #{show(other)}")
    end
  end

  @spec has_o?(ty()) :: boolean()
  def has_o?(@o), do: true
  def has_o?({:fun, a, b}), do: has_o?(a) or has_o?(b)
  def has_o?({:tapp, _, args}), do: Enum.any?(args, &has_o?/1)
  def has_o?({:tuple, tys}), do: Enum.any?(tys, &has_o?/1)
  def has_o?(_), do: false

  @spec ground?(ty()) :: boolean()
  def ground?({:tvar, _}), do: false
  def ground?({:fun, a, b}), do: ground?(a) and ground?(b)
  def ground?({:tapp, _, args}), do: Enum.all?(args, &ground?/1)
  def ground?({:tuple, tys}), do: Enum.all?(tys, &ground?/1)
  def ground?({:base, _}), do: true

  # ---------------------------------------------------------------------------
  # Type substitution and traversal
  # ---------------------------------------------------------------------------

  @spec subst_ty(ty(), %{non_neg_integer() => ty()}) :: ty()
  def subst_ty({:tvar, id} = v, s), do: Map.get(s, id, v)
  def subst_ty({:fun, a, b}, s), do: {:fun, subst_ty(a, s), subst_ty(b, s)}
  def subst_ty({:tapp, n, args}, s), do: {:tapp, n, Enum.map(args, &subst_ty(&1, s))}
  def subst_ty({:tuple, tys}, s), do: {:tuple, Enum.map(tys, &subst_ty(&1, s))}
  def subst_ty(ty, _s), do: ty

  @doc "Applies `fun` to every type annotation in a term."
  @spec map_types(tm(), (ty() -> ty())) :: tm()
  def map_types({:const, n, args, ty}, f), do: {:const, n, Enum.map(args, f), f.(ty)}
  def map_types({:var, id, ty}, f), do: {:var, id, f.(ty)}
  def map_types({:app, a, b}, f), do: {:app, map_types(a, f), map_types(b, f)}
  def map_types({:lam, id, ty, b}, f), do: {:lam, id, f.(ty), map_types(b, f)}
  def map_types({:quant, q, id, ty, b}, f), do: {:quant, q, id, f.(ty), map_types(b, f)}
  def map_types({:not, a}, f), do: {:not, map_types(a, f)}
  def map_types({:eq, a, b}, f), do: {:eq, map_types(a, f), map_types(b, f)}
  def map_types({:bin, op, a, b}, f), do: {:bin, op, map_types(a, f), map_types(b, f)}
  def map_types({:modal, m, ix, a}, f), do: {:modal, m, ix, map_types(a, f)}

  @doc "Folds over every subterm (pre-order)."
  @spec reduce(tm(), acc, (tm(), acc -> acc)) :: acc when acc: var
  def reduce(t, acc, fun) do
    acc = fun.(t, acc)

    case t do
      {:app, a, b} -> reduce(b, reduce(a, acc, fun), fun)
      {:lam, _, _, b} -> reduce(b, acc, fun)
      {:quant, _, _, _, b} -> reduce(b, acc, fun)
      {:not, a} -> reduce(a, acc, fun)
      {:eq, a, b} -> reduce(b, reduce(a, acc, fun), fun)
      {:bin, _, a, b} -> reduce(b, reduce(a, acc, fun), fun)
      {:modal, _, _, a} -> reduce(a, acc, fun)
      _ -> acc
    end
  end

  @doc "Collects every type annotation occurring in a term."
  @spec types_in(tm()) :: [ty()]
  def types_in(t) do
    reduce(t, [], fn
      {:const, _, args, ty}, acc -> [ty | args ++ acc]
      {:var, _, ty}, acc -> [ty | acc]
      {:lam, _, ty, _}, acc -> [ty | acc]
      {:quant, _, _, ty, _}, acc -> [ty | acc]
      _, acc -> acc
    end)
  end

  @spec tvars(ty()) :: [non_neg_integer()]
  def tvars({:tvar, id}), do: [id]
  def tvars({:fun, a, b}), do: tvars(a) ++ tvars(b)
  def tvars({:tapp, _, args}), do: Enum.flat_map(args, &tvars/1)
  def tvars({:tuple, tys}), do: Enum.flat_map(tys, &tvars/1)
  def tvars(_), do: []

  @doc """
  Capture-free substitution of terms for variable ids. Binders inside the
  substituted terms are renamed with fresh ids drawn from `next_id`, so that every
  binder stays unique after duplication.
  """
  @spec subst(tm(), %{non_neg_integer() => tm()}, non_neg_integer()) ::
          {tm(), non_neg_integer()}
  def subst(t, s, next_id) do
    case t do
      {:var, id, _} ->
        case Map.fetch(s, id) do
          {:ok, rep} -> freshen(rep, %{}, next_id)
          :error -> {t, next_id}
        end

      {:const, _, _, _} ->
        {t, next_id}

      {:app, a, b} ->
        {a, n} = subst(a, s, next_id)
        {b, n} = subst(b, s, n)
        {{:app, a, b}, n}

      {:lam, id, ty, b} ->
        {b, n} = subst(b, Map.delete(s, id), next_id)
        {{:lam, id, ty, b}, n}

      {:quant, q, id, ty, b} ->
        {b, n} = subst(b, Map.delete(s, id), next_id)
        {{:quant, q, id, ty, b}, n}

      {:not, a} ->
        {a, n} = subst(a, s, next_id)
        {{:not, a}, n}

      {:eq, a, b} ->
        {a, n} = subst(a, s, next_id)
        {b, n} = subst(b, s, n)
        {{:eq, a, b}, n}

      {:bin, op, a, b} ->
        {a, n} = subst(a, s, next_id)
        {b, n} = subst(b, s, n)
        {{:bin, op, a, b}, n}

      {:modal, m, ix, a} ->
        {a, n} = subst(a, s, next_id)
        {{:modal, m, ix, a}, n}
    end
  end

  # Renames every binder of `t` to a fresh id.
  defp freshen(t, ren, n) do
    case t do
      {:var, id, ty} ->
        {{:var, Map.get(ren, id, id), ty}, n}

      {:const, _, _, _} ->
        {t, n}

      {:app, a, b} ->
        {a, n} = freshen(a, ren, n)
        {b, n} = freshen(b, ren, n)
        {{:app, a, b}, n}

      {:lam, id, ty, b} ->
        {b, n2} = freshen(b, Map.put(ren, id, n), n + 1)
        {{:lam, n, ty, b}, n2}

      {:quant, q, id, ty, b} ->
        {b, n2} = freshen(b, Map.put(ren, id, n), n + 1)
        {{:quant, q, n, ty, b}, n2}

      {:not, a} ->
        {a, n} = freshen(a, ren, n)
        {{:not, a}, n}

      {:eq, a, b} ->
        {a, n} = freshen(a, ren, n)
        {b, n} = freshen(b, ren, n)
        {{:eq, a, b}, n}

      {:bin, op, a, b} ->
        {a, n} = freshen(a, ren, n)
        {b, n} = freshen(b, ren, n)
        {{:bin, op, a, b}, n}

      {:modal, m, ix, a} ->
        {a, n} = freshen(a, ren, n)
        {{:modal, m, ix, a}, n}
    end
  end

  @doc "Readable rendering of a type, used in error messages."
  @spec show(ty()) :: String.t()
  def show({:base, n}), do: n
  def show({:tvar, id}), do: "T#{id}"
  def show({:fun, a, b}), do: "(#{show(a)} > #{show(b)})"
  def show({:tapp, n, args}), do: "#{n}(#{Enum.map_join(args, ",", &show/1)})"
  def show({:tuple, tys}), do: "[#{Enum.map_join(tys, ",", &show/1)}]"

  @doc """
  Unambiguous name of a ground non-arrow type, used for the arena sort of TH1 type
  constructor applications and tuples (`$$`-prefixed, so disjoint from user sorts).
  """
  @spec sort_name(ty()) :: String.t()
  def sort_name({:base, n}), do: quote_name(n)
  def sort_name({:fun, a, b}), do: "(#{sort_name(a)}>#{sort_name(b)})"

  def sort_name({:tapp, n, args}),
    do: "$$#{quote_name(n)}(#{Enum.map_join(args, ",", &sort_name/1)})"

  def sort_name({:tuple, tys}), do: "$$tuple(#{Enum.map_join(tys, ",", &sort_name/1)})"
  def sort_name({:tvar, _}), do: reject!("non-ground type reached the arena")

  defp quote_name(n) do
    if Regex.match?(~r/^\$*[A-Za-z0-9_]+$/, n),
      do: n,
      else: "'" <> String.replace(String.replace(n, "\\", "\\\\"), "'", "\\'") <> "'"
  end
end
