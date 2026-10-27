defmodule NimbleThf.ParserTest do
  use ExUnit.Case, async: true

  alias NimbleThf.{Oracle, Parser, Printer}

  doctest Parser

  # Constructs that the THF0 corpus does not exercise.
  @sources [
    "thf(a, axiom, p & q & r).",
    "thf(a, axiom, p | (q | r)).",
    "thf(a, axiom, f @ a = b).",
    "thf(a, axiom, ~ ~ p).",
    "thf(a, axiom, ~ (p) <~> (q ~| r)).",
    "thf(a, axiom, (p ~& q) <= r).",
    "thf(a, axiom, ![X: $i]: p @ X).",
    "thf(a, axiom, (=) @ a @ b).",
    "thf(a, axiom, (~) @ ((&) @ p @ q)).",
    "thf(t, type, f: $i > $i > $o).",
    "thf(t, type, (f: ($i > $i) > $o)).",
    "thf(t, type, g: ($i * $i) > $o).",
    "thf(t, type, list: $tType > $tType).",
    "thf(a, axiom, !>[A: $tType]: ![X: A]: (X = X)).",
    "thf(a, axiom, !! @ (^[X: $i]: (X != a))).",
    "thf(a, axiom, @@+ @ $i @ p).",
    "thf(a, axiom, ?*[A: $tType]: (@= @ A)).",
    "thf(a, axiom, @+[X: $i]: (p @ X)).",
    "thf(a, axiom, @-[X: $i]: (p @ X)).",
    "thf(a, axiom, $ite(p, a, b) = c).",
    "thf(a, axiom, $let(c: $i, c := d, p @ c)).",
    "thf(a, axiom, f(a, g(b)) = $$sys).",
    "thf(a, axiom, [a, b] = [] ).",
    "thf(a, axiom, ($less @ -1 @ 2.5e-3) & ($less @ 1/3 @ 7)).",
    "thf(a, axiom, \"distinct\" != 'quoted \\' word').",
    "thf(d, definition, c == ^[X: $i]: X).",
    "thf(1, axiom, p, file('f.p', a), [status(thm), x:y:[1]]).",
    "thf(a, lemma, p, inference(r, [status(thm)], [a, b])).",
    "thf(a, axiom-sub, p).",
    "include('Axioms/X.ax'). include('Axioms/Y.ax', [a, 'b', 1]). include('Z', *).",
    "% comment\n/* block * comment */ thf( a ,axiom,p/*x*/&q ) . % trailing"
  ]

  for source <- @sources do
    test "agrees with Tptp on #{inspect(source)}" do
      assert Oracle.check(unquote(source)) == :ok
    end
  end

  test "the oracle rejects a wrongly associated tree" do
    {:ok, [{:thf, name, role, {:binary, :and, {:binary, :and, p, q}, r}, nil}]} =
      Parser.parse("thf(a, axiom, p & q & r).")

    wrong = {:thf, name, role, {:binary, :and, p, {:binary, :and, q, r}}, nil}
    {:ok, expected, []} = Tptp.Parser.statement_from_string("thf(a, axiom, p & q & r).")
    {:ok, reprinted, []} = Tptp.Parser.statement_from_string(Printer.to_string(wrong))

    refute Oracle.shape(expected) == Oracle.shape(reprinted)
  end

  test "binders take a unit formula as body, as in the v9 BNF" do
    assert {:ok,
            [{:thf, _, _, {:binary, :app, {:quant, :forall, _, {:const, "p"}}, {:var, "X"}}, _}]} =
             Parser.parse("thf(a, axiom, ![X: $i]: p @ X).")
  end

  # The BNF admits formula data in annotations, but `Tptp` 0.3 rejects it.
  test "accepts $thf formula data in annotations" do
    assert {:ok,
            [
              {:thf, _, _, _,
               [{:general_function, "inference", [_, _, {:list, [formula_data: _]}]}]}
            ]} =
             Parser.parse("thf(a, lemma, p, inference(r, [], [$thf(p & q)])).")
  end

  test "reports the offset of a syntax error" do
    assert {:error, _message, offset} = Parser.parse("thf(a, axiom, p).\nthf(b, axiom, p & | q).")
    assert offset == 18
  end
end
