defmodule NimbleThf.Parser do
  @moduledoc """
  A THF parser written with NimbleParsec, as an experiment against `{:tptp, "~> 0.3"}`.

  Covers the THF language of the TPTP v9 BNF without the non-classical (`[.]`,
  `{$box}`), sequent (`-->`) and subtype (`<<`) extensions. Associative chains are
  left-nested and `>` is right-nested, matching the `Tptp` tree; parentheses leave
  no trace in the AST.

  ## AST

      {:thf, name, role, formula, annotations} | {:include, file, selection}

      formula ::= {:typing, atom, type}
                | {:quant, q, [{var_name, type}], body}   q in :forall :exists :lambda
                                                          :choice :description :pi :sigma :hash
                | {:binary, op, l, r}   op in :or :and :app :iff :implies :if :xor :nor
                                        :nand :eq :neq :map :xprod :union :identical :assign
                | {:not, f} | {:fun, head, args} | {:tuple, items}
                | {:conn, op}   op in the connectives above, or :all :ex :choose :describe
                                :typed_eq for `!!` `??` `@@+` `@@-` `@=`
                | {:var, x} | {:const, a} | {:defined, "$a"} | {:system, "$$a"}
                | {:number, n} | {:distinct, "\\"a\\""}

  Words are kept as written, so `'a'` and `a` stay distinct texts.
  """

  import NimbleParsec

  # Combinator helpers. They run at compile time, hence anonymous functions.
  op = fn spelling, name -> string(spelling) |> replace(name) end
  # Each token swallows the whitespace after it, so a failed alternative never rescans it.
  tok = fn combinator -> combinator |> parsec(:ws) end
  sym = fn spelling -> tok.(ignore(string(spelling))) end
  comma_list = fn item -> item |> repeat(sym.(",") |> concat(item)) end
  link = fn connective, operand -> tok.(connective) |> concat(operand) |> wrap() end
  chain = fn connective, operand -> times(link.(connective, operand), min: 1) end

  # -- Lexical ---------------------------------------------------------------

  alnum = ascii_string([?a..?z, ?A..?Z, ?0..?9, ?_], min: 1)
  word = fn first -> ascii_char(first) |> optional(alnum) |> reduce(:join) end

  lower_word = word.([?a..?z])
  upper_word = word.([?A..?Z])
  dollar_word = string("$") |> concat(lower_word) |> reduce(:join)
  dollar_dollar_word = string("$$") |> concat(lower_word) |> reduce(:join)

  quoted = fn quote, plain ->
    string(quote)
    |> times(choice([ascii_string(plain, min: 1), string("\\\\"), string("\\" <> quote)]), min: 1)
    |> string(quote)
    |> reduce(:join)
  end

  single_quoted = quoted.("'", [?\s..?&, ?(..?[, ?]..?~])
  distinct_object = quoted.("\"", [?\s..?!, ?#..?[, ?]..?~])
  atomic_word = choice([lower_word, single_quoted])

  digits = ascii_string([?0..?9], min: 1)
  sign = ascii_char([?+, ?-])
  exponent = ascii_char([?e, ?E]) |> optional(sign) |> concat(digits)

  number =
    optional(sign)
    |> concat(digits)
    |> optional(
      choice([
        string("/") |> concat(digits),
        string(".") |> concat(digits) |> optional(exponent),
        exponent
      ])
    )
    |> reduce(:join)

  block_comment =
    string("/*")
    |> repeat(choice([utf8_string([not: ?*], min: 1), string("*") |> lookahead_not(string("/"))]))
    |> string("*/")

  defcombinatorp(
    :ws,
    repeat(
      choice([
        ascii_string([?\s, ?\t, ?\n, ?\r, ?\f], min: 1),
        string("%") |> utf8_string([not: ?\n], min: 0),
        block_comment
      ])
    )
    |> ignore()
  )

  # -- Connectives -----------------------------------------------------------

  nonassoc =
    choice([
      op.("<=>", :iff),
      op.("<~>", :xor),
      op.("<=", :if),
      op.("=>", :implies),
      op.("~|", :nor),
      op.("~&", :nand)
    ])

  connective =
    choice([
      nonassoc,
      op.("!=", :neq),
      op.("|", :or),
      op.("&", :and),
      op.("=", :eq),
      op.("~", :not)
    ])

  th1_defined =
    choice([
      op.("!!", :all),
      op.("??", :ex),
      op.("@@+", :choose),
      op.("@@-", :describe),
      op.("@=", :typed_eq)
    ])

  quantifier =
    choice([
      op.("!>", :pi),
      op.("?*", :sigma),
      op.("!", :forall),
      op.("?", :exists),
      op.("^", :lambda),
      op.("@+", :choice),
      op.("@-", :description),
      op.("#", :hash)
    ])

  # `=` but not `=>` or `==`
  infix = choice([op.("!=", :neq), op.("=", :eq) |> lookahead_not(ascii_char([?>, ?=]))])

  # -- Terms and formulas ----------------------------------------------------

  variable = unwrap_and_tag(upper_word, :var)

  arguments = sym.("(") |> concat(comma_list.(parsec(:formula))) |> concat(sym.(")")) |> wrap()

  head =
    choice([
      unwrap_and_tag(dollar_dollar_word, :system),
      unwrap_and_tag(dollar_word, :defined),
      unwrap_and_tag(atomic_word, :const)
    ])

  atomic =
    choice([
      sym.("(") |> concat(tok.(connective)) |> concat(sym.(")")) |> unwrap_and_tag(:conn),
      sym.("[") |> optional(comma_list.(parsec(:formula))) |> concat(sym.("]")) |> tag(:tuple),
      tok.(th1_defined) |> unwrap_and_tag(:conn),
      tok.(number) |> unwrap_and_tag(:number),
      tok.(distinct_object) |> unwrap_and_tag(:distinct),
      tok.(head) |> optional(arguments) |> reduce(:fun),
      tok.(variable)
    ])

  defcombinatorp(
    :unitary_term,
    choice([atomic, sym.("(") |> parsec(:logic_formula) |> concat(sym.(")"))])
  )

  typed_variable = tok.(variable) |> concat(sym.(":")) |> parsec(:logic_formula) |> reduce(:typed)

  defcombinatorp(
    :quantified,
    tok.(quantifier)
    |> concat(sym.("["))
    |> wrap(comma_list.(typed_variable))
    |> concat(sym.("]"))
    |> concat(sym.(":"))
    |> parsec(:unit)
    |> reduce(:quant)
  )

  defcombinatorp(
    :prefix_unary,
    sym.("~")
    |> lookahead_not(ascii_char([?|, ?&]))
    |> choice([parsec(:prefix_unary), parsec(:quantified), parsec(:unitary_term)])
    |> unwrap_and_tag(:not)
  )

  defcombinatorp(
    :unit,
    choice([
      parsec(:prefix_unary),
      parsec(:quantified),
      parsec(:unitary_term) |> optional(tok.(infix) |> parsec(:unitary_term)) |> reduce(:infix)
    ])
  )

  unitary = choice([parsec(:quantified), parsec(:unitary_term)])

  defcombinatorp(
    :logic_formula,
    parsec(:unit)
    |> optional(
      choice([
        link.(nonassoc, parsec(:unit)),
        chain.(op.("|", :or), parsec(:unit)),
        chain.(op.("&", :and), parsec(:unit)),
        chain.(op.("@", :app), parsec(:unit)),
        chain.(op.(">", :map), unitary),
        chain.(op.("*", :xprod), unitary),
        chain.(op.("+", :union), unitary),
        link.(op.("==", :identical), parsec(:logic_formula)),
        link.(op.(":=", :assign), parsec(:logic_formula))
      ])
    )
    |> reduce(:binary)
  )

  typeable =
    choice([unwrap_and_tag(atomic_word, :const), unwrap_and_tag(distinct_object, :distinct)])

  typing = tok.(typeable) |> concat(sym.(":")) |> parsec(:logic_formula) |> reduce(:typing)

  defcombinatorp(
    :formula,
    choice([
      typing,
      sym.("(") |> concat(typing) |> concat(sym.(")")),
      parsec(:logic_formula)
    ])
  )

  # -- Annotations -----------------------------------------------------------

  general_data =
    choice([
      sym.("$thf")
      |> concat(sym.("("))
      |> parsec(:formula)
      |> concat(sym.(")"))
      |> unwrap_and_tag(:formula_data),
      tok.(atomic_word)
      |> optional(
        sym.("(")
        |> concat(comma_list.(parsec(:general_term)))
        |> concat(sym.(")"))
        |> wrap()
      )
      |> reduce(:general_function),
      tok.(variable),
      tok.(number) |> unwrap_and_tag(:number),
      tok.(distinct_object) |> unwrap_and_tag(:distinct)
    ])

  defcombinatorp(
    :general_term,
    choice([
      sym.("[")
      |> optional(comma_list.(parsec(:general_term)))
      |> concat(sym.("]"))
      |> tag(:list),
      general_data |> optional(sym.(":") |> parsec(:general_term)) |> reduce(:colon)
    ])
  )

  # -- Statements ------------------------------------------------------------

  annotated =
    sym.("thf")
    |> concat(sym.("("))
    |> concat(tok.(choice([atomic_word, digits])))
    |> concat(sym.(","))
    |> concat(tok.(lower_word) |> optional(sym.("-") |> parsec(:general_term)) |> reduce(:role))
    |> concat(sym.(","))
    |> parsec(:formula)
    |> optional(
      sym.(",")
      |> parsec(:general_term)
      |> optional(sym.(",") |> parsec(:general_term))
      |> wrap()
    )
    |> concat(sym.(")"))
    |> concat(sym.("."))
    |> reduce(:annotated)

  include =
    sym.("include")
    |> concat(sym.("("))
    |> concat(tok.(single_quoted))
    |> optional(
      sym.(",")
      |> choice([
        sym.("[") |> wrap(comma_list.(tok.(choice([atomic_word, digits])))) |> concat(sym.("]")),
        tok.(string("*"))
      ])
    )
    |> concat(sym.(")"))
    |> concat(sym.("."))
    |> reduce(:include)

  defparsecp(:file, parsec(:ws) |> repeat(choice([annotated, include])) |> eos())

  @doc """
  Parses a THF file into a list of statements.

      iex> NimbleThf.Parser.parse("thf(a, axiom, p & q).")
      {:ok, [{:thf, "a", "axiom", {:binary, :and, {:const, "p"}, {:const, "q"}}, nil}]}
  """
  @spec parse(binary()) :: {:ok, list()} | {:error, String.t(), non_neg_integer()}
  def parse(source) when is_binary(source) do
    case file(source) do
      {:ok, statements, "", _context, _line, _offset} -> {:ok, statements}
      {:error, message, _rest, _context, _line, offset} -> {:error, message, offset}
    end
  end

  # -- AST construction ------------------------------------------------------

  defp join(parts), do: IO.iodata_to_binary(parts)

  defp fun([head]), do: head
  defp fun([head, args]), do: {:fun, head, args}

  defp typed([{:var, name}, type]), do: {name, type}
  defp quant([q, vars, body]), do: {:quant, q, vars, body}
  defp typing([atom, type]), do: {:typing, atom, type}

  defp infix([term]), do: term
  defp infix([l, op, r]), do: {:binary, op, l, r}

  defp binary([formula]), do: formula

  defp binary([head | [[:map, _] | _] = links]) do
    [last | rest] = Enum.reverse([head | Enum.map(links, fn [_, r] -> r end)])
    Enum.reduce(rest, last, &{:binary, :map, &1, &2})
  end

  defp binary([head | links]) do
    Enum.reduce(links, head, fn [op, r], l -> {:binary, op, l, r} end)
  end

  defp general_function([word]), do: {:word, word}
  defp general_function([word, args]), do: {:general_function, word, args}

  defp colon([data]), do: data
  defp colon([data, term]), do: {:colon, data, term}

  defp role([role]), do: role
  defp role([role, subrole]), do: {role, subrole}

  defp annotated([name, role, formula]), do: {:thf, name, role, formula, nil}
  defp annotated([name, role, formula, annotations]), do: {:thf, name, role, formula, annotations}

  defp include([file]), do: {:include, file, nil}
  defp include([file, selection]), do: {:include, file, selection}
end
