defmodule Astraea.InputTest do
  use ExUnit.Case, async: true

  alias Astraea.{Arena, ProofChecker, Prover, TptpCorpus, TptpLower}
  alias Astraea.Input.{Arith, IR}

  defp lower!(src, opts \\ []) do
    assert {:ok, lowered} = TptpLower.from_string(src, opts)
    lowered
  end

  defp prove(src, opts) do
    Prover.prove_string(src, Keyword.merge([timeout_ms: 3_000], opts))
  end

  defp assert_proved(src, opts \\ []) do
    assert {:proved, steps, stats} = prove(src, opts)
    assert :ok == ProofChecker.verify_refutation(stats.arena, steps)
  end

  defp refute_proved(src, opts \\ []) do
    refute match?({:proved, _, _}, prove(src, Keyword.merge([timeout_ms: 1_500], opts)))
  end

  defp symbols(lowered), do: Map.values(lowered.arena.symbol_names)

  # ---------------------------------------------------------------------------
  # First-order input
  # ---------------------------------------------------------------------------

  describe "FOF, TFF and CNF" do
    test "FOF problems are lowered with default first-order types and proved" do
      src = """
      fof(a1, axiom, ![X]: (p(X) => q(f(X)))).
      fof(a2, axiom, p(a)).
      fof(c, conjecture, ?[Y]: q(Y)).
      """

      lowered = lower!(src)
      assert :fof in lowered.fragments
      assert_proved(src)
    end

    test "CNF negated conjectures are assumptions and free variables are universal" do
      src = """
      cnf(a1, axiom, ~p(X) | q(X)).
      cnf(a2, axiom, p(a)).
      cnf(c, negated_conjecture, ~q(a)).
      """

      lowered = lower!(src)
      assert lowered.conjectures == []
      assert Enum.any?(lowered.axioms, &match?({"c", "negated_conjecture", _}, &1))
      assert_proved(src)
    end

    test "a satisfiable CNF set is not refuted" do
      refute_proved("""
      cnf(a1, axiom, ~p(X) | q(X)).
      cnf(c, negated_conjecture, p(a)).
      """)
    end

    test "TFF declarations, n-ary functions and $distinct" do
      src = """
      tff(t, type, s: $tType).
      tff(f, type, f: (s * s) > s).
      tff(a, type, a: s).
      tff(b, type, b: s).
      tff(d, axiom, $distinct(a, b)).
      tff(c, conjecture, f(a, b) != f(a, a) | a != b).
      """

      assert_proved(src)
    end

    test "distinct objects are pairwise unequal" do
      assert_proved(~s|fof(c, conjecture, "Alice" != "Bob").|)
    end

    test "several conjectures are conjoined" do
      lowered =
        lower!("""
        fof(c1, conjecture, p).
        fof(c2, conjecture, q).
        """)

      assert [{"c1&c2", _}] = lowered.conjectures
    end
  end

  # ---------------------------------------------------------------------------
  # TH1 polymorphism
  # ---------------------------------------------------------------------------

  describe "TH1 monomorphization" do
    @lists """
    thf(list, type, list: $tType > $tType).
    thf(nil, type, nil: !>[A: $tType]: (list @ A)).
    thf(cons, type, cons: !>[A: $tType]: (A > (list @ A) > (list @ A))).
    thf(a, type, a: $i).
    thf(distinct, axiom, ![A: $tType, X: A, L: list @ A]: ((cons @ A @ X @ L) != L)).
    """

    test "polymorphic axioms are instantiated at the ground types of the problem" do
      src = @lists <> "thf(c, conjecture, (cons @ $i @ a @ (nil @ $i)) != (nil @ $i))."
      lowered = lower!(src)
      assert :th1 in lowered.fragments
      assert lowered.incomplete == []
      assert "$$cons($i)" in symbols(lowered)

      assert Enum.any?(lowered.axioms, fn {name, _, _} ->
               String.starts_with?(name, "distinct@")
             end)

      assert_proved(src)
    end

    test "alpha-equivalent polymorphic redeclarations are accepted" do
      lower!("""
      thf(d1, type, id: !>[A: $tType]: (A > A)).
      thf(d2, type, id: !>[B: $tType]: (B > B)).
      thf(c, conjecture, ![A: $tType, X: A]: ((id @ A @ X) = (id @ A @ X))).
      """)
    end

    test "type-quantified conjectures are proved for a fresh sort" do
      assert_proved("thf(c, conjecture, ![A: $tType, X: A]: (X = X)).")
    end

    test "TF1 syntax" do
      src = """
      tff(list, type, list: $tType > $tType).
      tff(nil, type, nil: !>[A: $tType]: list(A)).
      tff(cons, type, cons: !>[A: $tType]: ((A * list(A)) > list(A))).
      tff(ax, axiom, ![A: $tType, X: A, L: list(A)]: cons(A, X, L) != nil(A)).
      tff(c, conjecture, cons($int, 1, nil($int)) != nil($int)).
      """

      assert_proved(src)
    end

    test "a monomorphization cut-off is reported" do
      src = """
      thf(list, type, list: $tType > $tType).
      thf(q, type, q: !>[A: $tType]: (A > $o)).
      thf(wrap, type, wrap: !>[A: $tType]: (A > (list @ A))).
      thf(a, type, a: $i).
      thf(up, axiom, ![A: $tType, X: A]: ((q @ A @ X) => (q @ (list @ A) @ (wrap @ A @ X)))).
      thf(c, conjecture, q @ $i @ a).
      """

      assert lower!(src, monomorphization: [rounds: 2]).incomplete == [
               {:monomorphization, :round_limit}
             ]
    end
  end

  # ---------------------------------------------------------------------------
  # Arithmetic
  # ---------------------------------------------------------------------------

  describe "arithmetic" do
    test "numerals are canonical" do
      assert Arith.parse_numeral!(:integer, "+007") == {{:base, "$int"}, "7"}
      assert Arith.parse_numeral!(:rational, "-4/6") == {{:base, "$rat"}, "-2/3"}
      assert Arith.parse_numeral!(:real, "1.50") == {{:base, "$real"}, "1.5"}
      assert Arith.parse_numeral!(:real, "-3.0E2") == {{:base, "$real"}, "-300.0"}
      assert Arith.parse_numeral!(:real, "25e-3") == {{:base, "$real"}, "0.025"}
    end

    test "operations follow the TPTP definitions" do
      i = &{:int, &1, 1}
      assert Arith.apply_op("$quotient_e", [i.(-7), i.(2)]) == i.(-4)
      assert Arith.apply_op("$quotient_t", [i.(-7), i.(2)]) == i.(-3)
      assert Arith.apply_op("$quotient_f", [i.(-7), i.(2)]) == i.(-4)
      assert Arith.apply_op("$quotient_e", [i.(7), i.(-2)]) == i.(-3)
      assert Arith.apply_op("$remainder_e", [i.(-7), i.(2)]) == i.(1)
      assert Arith.apply_op("$remainder_t", [i.(-7), i.(2)]) == i.(-1)
      assert Arith.apply_op("$quotient_t", [i.(7), i.(0)]) == nil
      assert Arith.apply_op("$quotient", [{:rat, 1, 1}, {:rat, 3, 1}]) == {:rat, 1, 3}
      assert Arith.apply_op("$quotient", [{:real, 1, 1}, {:real, 3, 1}]) == nil
      assert Arith.apply_op("$round", [{:rat, 5, 2}]) == nil
      assert Arith.apply_op("$round", [{:rat, -7, 3}]) == {:rat, -2, 1}
      assert Arith.apply_op("$to_int", [{:real, -3, 2}]) == i.(-2)
      assert Arith.apply_op("$lesseq", [{:rat, 2, 4}, {:rat, 1, 2}]) == true
    end

    test "ground arithmetic in the input is evaluated" do
      assert_proved("tff(c, conjecture, $less(2, $sum(1, 2)) & $product(2.5, 2.0) = 5.0).")
      assert_proved("thf(c, conjecture, ($greater @ ($uminus @ 1/2) @ -1/1)).")
    end

    test "false ground arithmetic is not proved" do
      refute_proved("tff(c, conjecture, $sum(1, 2) = 4).")
      refute_proved("tff(c, conjecture, $is_int(2.5)).")
    end

    test "ill-typed arithmetic is rejected" do
      assert {:error, _} = TptpLower.from_string("tff(c, conjecture, $sum(1, 2.0) = 3).")
      assert {:error, _} = TptpLower.from_string("tff(c, conjecture, $quotient(1, 2) = 3).")
      assert {:error, _} = TptpLower.from_string("fof(c, conjecture, p(1)).")
    end

    test "the :arith_eval kernel rule recomputes evaluations and rejects forgeries" do
      arena = Arena.new()
      {arena, int} = Arena.intern_type(arena, {:base, "$int"})
      {arena, int2} = Arena.intern_type(arena, {:arrow, int, int})
      {arena, int3} = Arena.intern_type(arena, {:arrow, int, int2})
      {arena, int_o} = Arena.intern_type(arena, {:arrow, int, :o})
      {arena, int_int_o} = Arena.intern_type(arena, {:arrow, int, int_o})
      {arena, p} = Arena.mk_const(arena, "p", int_o)
      {arena, sum} = Arena.mk_const(arena, "$sum", int3)
      {arena, less} = Arena.mk_const(arena, "$less", int_int_o)
      {arena, n1} = Arena.mk_const(arena, "1", int)
      {arena, n2} = Arena.mk_const(arena, "2", int)
      {arena, n3} = Arena.mk_const(arena, "3", int)
      {arena, n4} = Arena.mk_const(arena, "4", int)

      app = fn ar, f, args ->
        Enum.reduce(args, {ar, f}, fn a, {ar, f} -> Arena.mk_app(ar, f, a) end)
      end

      {arena, s12} = app.(arena, sum, [n1, n2])
      {arena, p_s12} = app.(arena, p, [s12])
      {arena, p3} = app.(arena, p, [n3])
      {arena, p4} = app.(arena, p, [n4])
      {arena, less12} = app.(arena, less, [n1, n2])
      {arena, less21} = app.(arena, less, [n2, n1])

      parent = MapSet.new([{:pos, p_s12}])
      ok = [{:axiom, 1, parent}, {:arith_eval, 2, 1, MapSet.new([{:pos, p3}])}]
      forged = [{:axiom, 1, parent}, {:arith_eval, 2, 1, MapSet.new([{:pos, p4}])}]

      assert {:error, {:not_empty_clause, _}} = ProofChecker.verify_refutation(arena, ok)
      assert {:error, {:invalid_arith_eval, 2, 1}} = ProofChecker.verify_refutation(arena, forged)

      # `~ $less(1, 2)` evaluates to the empty clause; `~ $less(2, 1)` does not.
      refutation = [{:axiom, 1, MapSet.new([{:neg, less12}])}, {:arith_eval, 2, 1, MapSet.new()}]
      assert :ok == ProofChecker.verify_refutation(arena, refutation)

      bogus = [{:axiom, 1, MapSet.new([{:neg, less21}])}, {:arith_eval, 2, 1, MapSet.new()}]
      assert {:error, {:invalid_arith_eval, 2, 1}} = ProofChecker.verify_refutation(arena, bogus)

      assert {_, %{2 => %MapSet{}}} = Astraea.Tstp.replay(arena, refutation)
      assert ProofChecker.step_parents({:arith_eval, 2, 1, MapSet.new()}) == [1]

      assert {_, :tautology} = Arith.simplify_clause(arena, MapSet.new([{:pos, less12}]))
      assert {_, :unchanged} = Arith.simplify_clause(arena, MapSet.new([{:pos, p3}]))
    end
  end

  # ---------------------------------------------------------------------------
  # Choice, $let, $ite, tuples
  # ---------------------------------------------------------------------------

  describe "choice, $let, $ite and tuples" do
    test "@+ and @- become $choice and $description applied to the predicate" do
      lowered =
        lower!("""
        thf(p, type, p: $i > $o).
        thf(c, conjecture, (@+[X: $i]: (p @ X)) = (@-[X: $i]: (p @ X))).
        """)

      {arena, _} = {lowered.arena, nil}
      {:ok, pred_i} = Map.fetch(arena.types, {:arrow, Arena.ty_i(), Arena.ty_o()})
      {:ok, choice_ty} = Map.fetch(arena.types, {:arrow, pred_i, Arena.ty_i()})
      assert lowered.const_types["$choice"] == choice_ty
      assert lowered.const_types["$description"] == choice_ty
      assert [:choice, :description, :thf] -- lowered.fragments == []
    end

    test "a problem using @+ is proved and rendered as a TSTP derivation" do
      src = """
      thf(p, type, p: $i > $o).
      thf(a, type, a: $i).
      thf(ax, axiom, p @ a).
      thf(c, conjecture, p @ (@+[X: $i]: (p @ X))).
      """

      lowered = lower!(src)
      assert {:proved, steps, stats} = Astraea.Portfolio.prove_lowered(lowered, timeout_ms: 3_000)
      assert :ok == ProofChecker.verify_refutation(stats.arena, steps)
      assert Enum.any?(steps, &match?({:choice, _, _, _}, &1))

      tstp = Astraea.Tstp.derivation(lowered, steps, stats, problem: "choice.p")
      assert {:ok, derivation, []} = Tptp.Derivation.from_string(IO.iodata_to_binary(tstp))
      assert Tptp.Derivation.acyclic?(derivation)
      assert IO.iodata_to_binary(tstp) =~ "axiom_of_choice"
    end

    test "$let is expanded by substitution" do
      assert_proved("""
      tff(p, type, p: $i > $o).
      tff(f, type, f: ($i * $i) > $i).
      tff(ax, axiom, p(f(a, a))).
      tff(c, conjecture, $let(g: $i > $i, g(X) := f(X, X), p(g(a)))).
      """)

      assert_proved("""
      thf(p, type, p: $i > $o).
      thf(a, type, a: $i).
      thf(ax, axiom, p @ a).
      thf(c, conjecture, $let(x: $i, x := a, p @ x)).
      """)
    end

    test "$ite on formulas and terms" do
      assert_proved("""
      tff(c, conjecture, (p & q) => $ite(p, q, r)).
      """)

      lowered = lower!("tff(c, conjecture, f($ite(p, a, b)) = f(a) | ~p).")
      assert "$$ite" in symbols(lowered)

      assert Enum.any?(lowered.axioms, fn {name, _, _} ->
               String.starts_with?(name, "$$ite_def")
             end)
    end

    test "tuples get constructor and projection axioms" do
      lowered = lower!("thf(c, conjecture, [a, b] = [a, b]).")
      assert "$$tuple" in symbols(lowered)

      assert Enum.count(lowered.axioms, fn {n, _, _} -> String.starts_with?(n, "$$tuple_def") end) ==
               2
    end
  end

  # ---------------------------------------------------------------------------
  # Modal logic
  # ---------------------------------------------------------------------------

  describe "modal embedding" do
    @spec_k "thf(s, logic, $modal == [$domains == $constant, $designation == $rigid, $terms == $local, $modalities == $modal_system_K])."
    @spec_t "thf(s, logic, $modal == [$domains == $constant, $designation == $rigid, $terms == $local, $modalities == $modal_system_T])."

    test "the K axiom holds in every frame" do
      assert_proved(
        @spec_k <>
          "thf(c, conjecture, ![A: $o, B: $o]: (([.] (A => B)) => (([.] A) => ([.] B))))."
      )
    end

    test "the T axiom needs reflexive frames" do
      conj = "thf(c, conjecture, ![A: $o]: (({$box} @ A) => A))."
      assert_proved(@spec_t <> conj)
      refute_proved(@spec_k <> conj)
    end

    test "axioms are global, hypotheses local" do
      p = "thf(p, type, p: $o)."
      assert_proved(@spec_k <> p <> "thf(a, axiom, p). thf(c, conjecture, [.] p).")
      refute_proved(@spec_k <> p <> "thf(a, hypothesis, p). thf(c, conjecture, [.] p).")
    end

    test "the Barcan formula needs decreasing (or constant) domains" do
      barcan =
        "thf(f, type, f: $i > $o). thf(c, conjecture, (![X: $i]: [.] (f @ X)) => ([.] ![X: $i]: (f @ X)))."

      decreasing =
        "thf(s, logic, $modal == [$domains == $decreasing, $designation == $rigid, $terms == $local, $modalities == $modal_system_K])."

      cumulative =
        "thf(s, logic, $modal == [$domains == $cumulative, $designation == $rigid, $terms == $local, $modalities == $modal_system_K])."

      assert_proved(decreasing <> barcan, timeout_ms: 5_000)
      refute_proved(cumulative <> barcan)
    end

    test "predicate definitions are accepted only at the top of global statements" do
      decls = "thf(p, type, p: $i > $o). thf(q, type, q: $i > $o)."

      assert_proved(
        @spec_k <>
          decls <>
          "thf(d, definition, p = (^[X: $i]: [.] (q @ X))). thf(c, conjecture, ![X: $i]: ((p @ X) => [.] (q @ X)))."
      )

      assert {:error, _} = TptpLower.from_string(@spec_k <> decls <> "thf(h, hypothesis, p = q).")
    end

    test "unsupported semantics and modal operators without a specification are rejected" do
      assert {:error, _} = TptpLower.from_string("thf(c, conjecture, [.] $true).")

      flexible =
        "thf(s, logic, $modal == [$domains == $constant, $designation == $flexible, $terms == $local, $modalities == $modal_system_K])."

      assert {:error, _} = TptpLower.from_string(flexible <> "thf(c, conjecture, [.] $true).")
    end
  end

  # ---------------------------------------------------------------------------
  # Conservative rejection
  # ---------------------------------------------------------------------------

  describe "rejection" do
    test "parse errors, unknown interpreted symbols and free variables are rejected" do
      assert {:error, {:parse, _}} = TptpLower.from_string("thf(c, conjecture, p @@ q).")
      assert {:error, _} = TptpLower.from_string("tff(c, conjecture, $frobnicate(a)).")
      assert {:error, _} = TptpLower.from_string("thf(c, conjecture, p @ X).")
      assert {:error, _} = TptpLower.from_string("thf(c, conjecture, ?*[A: $tType]: $true).")
    end

    test "user symbols never collide with interpreted names or numerals" do
      assert IR.user_name("p") == "p"
      assert IR.user_name("$true") == "~$true"
      assert IR.user_name("12") == "~12"
      assert IR.user_name("~12") == "~~12"
      refute_proved("fof(c, conjecture, '$true').")
    end
  end

  # ---------------------------------------------------------------------------
  # Extended evaluation split
  # ---------------------------------------------------------------------------

  test "the extended split is locked, disjoint from the THF0 splits, and covers the new fragments" do
    extended = TptpCorpus.load_split(:extended)
    assert length(extended) == 150
    assert extended == Enum.sort(Enum.uniq(extended))

    # Holdout is drawn from the strict THF0 pool only, so non-strict problems are
    # disjoint from it without consulting its manifest.
    for tier <- [:smoke, :dev] do
      assert MapSet.disjoint?(MapSet.new(extended), MapSet.new(TptpCorpus.load_split(tier)))
    end

    entries = TptpCorpus.load_split_entries(:extended)
    refute Enum.any?(entries, & &1.strict_thf0)

    assert Enum.all?(
             entries,
             &(&1.has_th1 or &1.has_arith or &1.has_choice or &1.has_modal or &1.has_let_ite)
           )
  end
end
