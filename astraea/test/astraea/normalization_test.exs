defmodule Astraea.NormalizationTest do
  use ExUnit.Case, async: true

  alias Astraea.{Normalization, Prover, TptpLower}

  # Small theorems: first-order with an existential, higher-order with a lambda
  # argument (needs extensionality), Boolean arguments, and one where formula
  # renaming kicks in.
  @theorems %{
    syllogism: """
    fof(all_men_mortal, axiom, ! [X]: (man(X) => mortal(X))).
    fof(socrates_man, axiom, man(socrates)).
    fof(some_mortal, conjecture, ? [X]: mortal(X)).
    """,
    lambda_arg: """
    thf(q_type, type, q: ($i > $i) > $o).
    thf(p_type, type, p: $i > $o).
    thf(g_type, type, g: $i > $i).
    thf(a_type, type, a: $i).
    thf(ax_pa, axiom, p @ a).
    thf(ax_cond_id, axiom, ! [X: $i]: ((p @ a) => ((g @ X) = X))).
    thf(ax_q_id, axiom, q @ (^ [X: $i]: X)).
    thf(conj_qg, conjecture, q @ g).
    """,
    boolean_arg: """
    thf(p_type, type, p: $o > $o).
    thf(a_type, type, a: $o).
    thf(b_type, type, b: $o).
    thf(ax, axiom, p @ (a & b)).
    thf(conj, conjecture, p @ (~ ((~ a) | (~ b)))).
    """,
    renaming: """
    thf(a_t, type, a: $o). thf(b_t, type, b: $o). thf(c_t, type, c: $o).
    thf(d_t, type, d: $o). thf(e_t, type, e: $o).
    thf(ax, axiom, (a & b & c) | (d & e)).
    thf(not_a, axiom, ~ a).
    thf(conj, conjecture, e).
    """
  }

  @counter_satisfiable """
  thf(p_type, type, p: $i > $o).
  thf(a_type, type, a: $i).
  thf(ax_pa, axiom, p @ a).
  thf(conj_invalid, conjecture, ! [X: $i]: (p @ X)).
  """

  @modes [
    [],
    [cnf: true],
    [cnf: true, renaming: false],
    [cnf: true, extraction: :boolean],
    [extraction: false],
    [extract_local: true],
    [cnf: true, extract_local: true]
  ]

  defp normalize!(src, opts) do
    assert {:ok, text} = Normalization.normalize_string(src, opts)
    text
  end

  for {name, _src} <- @theorems, mode <- @modes do
    test "#{name} stays a theorem after normalization with #{inspect(mode)}" do
      text = normalize!(@theorems[unquote(name)], unquote(mode))
      assert {:ok, %TptpLower{}} = TptpLower.from_string(text)
      assert {:proved, _steps, _stats} = Prover.prove_string(text, timeout_ms: 3_000)
    end
  end

  test "a non-theorem is not proved after normalization" do
    for mode <- [[], [cnf: true]] do
      text = normalize!(@counter_satisfiable, mode)
      assert {:ok, _} = TptpLower.from_string(text)
      refute match?({:proved, _, _}, Prover.prove_string(text, timeout_ms: 1_000))
    end
  end

  test "cnf mode clausifies assumptions but keeps the conjecture" do
    text = normalize!(@theorems.syllogism, cnf: true)
    statements = text |> String.split("\n") |> Enum.filter(&String.starts_with?(&1, "thf("))
    {conj, assumptions} = Enum.split_with(statements, &(&1 =~ ", conjecture, "))

    assert [conj] = conj
    assert conj =~ "(~ (! ["

    for line <- assumptions, line =~ ", axiom, " do
      refute line =~ "(! [B", "assumption still has a quantifier: #{line}"
      refute line =~ "=>"
    end
  end

  test "renaming and extraction introduce declared, content-addressed symbols" do
    renamed = normalize!(@theorems.renaming, cnf: true)
    assert renamed =~ ~r/type, def_[0-9a-f]{16}: \$o\)/

    extracted = normalize!(@theorems.boolean_arg, [])
    assert [_ | _] = Regex.scan(~r/type, xarg_[0-9a-f]{16}: \$o\)/, extracted)
    refute normalize!(@theorems.boolean_arg, extraction: false) =~ "xarg_"
  end

  test "output is deterministic" do
    for mode <- @modes do
      assert normalize!(@theorems.lambda_arg, mode) == normalize!(@theorems.lambda_arg, mode)
    end
  end

  test "input that uses the reserved symbol shapes is rejected" do
    src = """
    thf(c_t, type, xarg_0123456789abcdef: $o).
    thf(ax, axiom, xarg_0123456789abcdef).
    """

    assert {:error, {:reserved_symbols, ["xarg_0123456789abcdef"]}} =
             Normalization.normalize_string(src)
  end

  test "input lowered unfaithfully needs allow_incomplete" do
    src = """
    thf(p_type, type, p: $i > $o).
    thf(ax, axiom, ? [X: $i]: (p @ X)).
    thf(c, conjecture, p @ (@+[X: $i]: (p @ X))).
    """

    assert {:error, {:unfaithful_input, [caveat]}} = Normalization.normalize_string(src)
    assert caveat =~ "choice"
    assert {:ok, text} = Normalization.normalize_string(src, allow_incomplete: true)
    assert text =~ "% Caveat: "
  end

  test "to_thf prints the lowered problem without normalizing it" do
    {:ok, lowered} = TptpLower.from_string(@theorems.syllogism)
    text = Normalization.to_thf(lowered)
    assert text =~ "Leo-III --toTHF"
    refute text =~ "sk_"
    assert {:proved, _, _} = Prover.prove_string(text, timeout_ms: 3_000)
  end
end
