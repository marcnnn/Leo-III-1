defmodule Astraea.SineLeo3Test do
  use ExUnit.Case, async: true

  alias Astraea.{Clausifier, ProblemStatistics, ProofChecker, Prover, Sine, TptpLower}

  defp lower(src) do
    {:ok, lowered} = TptpLower.from_string(src)
    lowered
  end

  defp dropped(src, opts) do
    {_arena, _clauses, info} = Clausifier.clausify_with_info(lower(src), opts)
    info.axioms_dropped
  end

  # `junk` unrelated axioms, the chain `c @ a`, `c => h1`, `h1 => h2`, `h2 => g`
  # proving `g @ a`, and `extra` further axioms.
  defp chain_problem(junk, extra \\ "") do
    decls = for s <- ~w(c h1 h2 g k1), do: "thf(#{s}_decl, type, #{s}: $i > $o).\n"

    junk =
      for i <- 1..junk//1 do
        "thf(j#{i}_decl, type, j#{i}: $i > $o).\n" <>
          "thf(junk#{i}, axiom, ! [X: $i]: ((j#{i} @ X) => (j#{rem(i, junk) + 1} @ X))).\n"
      end

    Enum.join(decls) <>
      "thf(a_decl, type, a: $i).\n" <>
      Enum.join(junk) <>
      extra <>
      """
      thf(r1, axiom, c @ a).
      thf(r2, axiom, ! [X: $i]: ((c @ X) => (h1 @ X))).
      thf(r3, axiom, ! [X: $i]: ((h1 @ X) => (h2 @ X))).
      thf(r4, axiom, ! [X: $i]: ((h2 @ X) => (g @ X))).
      thf(goal, conjecture, g @ a).
      """
  end

  describe "configuration" do
    test "Leo-III's table by internal and external axiom counts" do
      assert Sine.table_id(500, 8000) == 21
      assert Sine.table_config(21) == %{tolerance: 1.0, max_size: 200, max_depth: 5}
      assert Sine.guess(500, 8000) == %{tolerance: 1.0, max_size: 200, max_depth: 5}

      assert Sine.table_id(100, 50_000) == 36
      assert Sine.guess(100, 50_000) == %{tolerance: 1.0, max_size: 999_999_999, max_depth: 2}

      assert Sine.table_id(50, 4000) == 13
      assert Sine.guess(50, 4000) == %{tolerance: 2.0, max_size: 200, max_depth: 2}

      assert Sine.table_id(40, 40) == 1
      assert Sine.guess(40, 40) == %{tolerance: 1.0, max_size: 200, max_depth: -1}

      # First matching row wins: (366..935, 48429..54878) is shadowed by
      # (34..511, 45455..54878) for 400 internal axioms
      assert Sine.table_id(400, 50_000) == 36
      assert Sine.table_id(3800, 50_640) == 6
    end

    test "no table row, or --standard-sine, takes the default by total count" do
      assert Sine.table_id(50, 0) == 0
      assert Sine.guess(50, 0) == %{tolerance: 3.5, max_size: 1000, max_depth: -1}
      assert Sine.guess(300, 0).tolerance == 2.5
      assert Sine.guess(700, 0).tolerance == 2.0
      assert Sine.guess(5000, 0).tolerance == 1.5

      assert Sine.guess(500, 8000, true) == Sine.default_config(8500)
      assert Sine.default_config(8500).tolerance == 1.5
      assert Sine.guess(40, 40, true).tolerance == 3.5
      assert Sine.config(:auto, internal: 40, external: 40, standard: true).tolerance == 3.5
      assert Sine.config(:auto, internal: 40, external: 40).tolerance == 1.0
    end

    test "--sine string parsing and its fallback" do
      assert Sine.parse("1.5;200;2") == {:ok, %{tolerance: 1.5, max_size: 200, max_depth: 2}}
      assert Sine.parse("2;10;-1") == {:ok, %{tolerance: 2.0, max_size: 10, max_depth: -1}}
      assert Sine.parse(".5;10;1") == {:ok, %{tolerance: 0.5, max_size: 10, max_depth: 1}}
      assert Sine.parse("1.5;200") == :error
      assert Sine.parse("x;200;2") == :error
      assert Sine.parse("1.5;2.5;2") == :error
      assert Sine.parse("") == :error

      assert Sine.config("3.0;50;1") == %{tolerance: 3.0, max_size: 50, max_depth: 1}
      assert Sine.config("bogus", internal: 500, external: 8000) == Sine.table_config(21)

      assert Sine.config("bogus", internal: 500, external: 8000, standard: true) ==
               Sine.default_config(8500)

      assert Sine.config(%{threshold: 2, max_size: 7, max_depth: 3}) ==
               %{tolerance: 2.0, max_size: 7, max_depth: 3}
    end
  end

  describe "selection" do
    test "the guessed configuration keeps the chain and yields a checked proof" do
      lowered = lower(chain_problem(30))
      {arena, clauses, info} = Clausifier.clausify_with_info(lowered, sine: :auto)

      assert info.axioms_dropped == 30

      assert {:proved, steps, stats} = Prover.prove_clauses(arena, clauses, timeout_ms: 3_000)
      assert :ok = ProofChecker.verify_refutation(stats.arena, steps)

      # Unchanged behaviour without the option
      assert dropped(chain_problem(30), sine_limit: nil) == 0
    end

    test "the depth limit cuts the chain" do
      src = chain_problem(30)
      assert dropped(src, sine: %{threshold: 1.0, max_size: 1000, max_depth: 1}) == 32
      assert dropped(src, sine: "1.0;1000;2") == 30
      assert dropped(src, sine: "1.0;1000;-1") == 30

      lowered = lower(src)
      {arena, clauses} = Clausifier.clausify(lowered, sine: "1.0;1000;1")
      refute match?({:proved, _, _}, Prover.prove_clauses(arena, clauses, timeout_ms: 1_000))
    end

    test "the threshold decides which symbols trigger an axiom" do
      # `a` occurs in the conjecture, `r1` and `k1`: three formulas. `k1 @ a` is
      # triggered by `a` iff 3 <= tolerance * occ(k1) = tolerance.
      src = chain_problem(30, "thf(extra, axiom, k1 @ a).\n")
      assert dropped(src, sine: "3.0;1000;-1") == 30
      assert dropped(src, sine: "2.9;1000;-1") == 31

      # The guess: (40, 40) is table entry 1 (tolerance 1.0); --standard-sine and
      # the default counts (all 35 internal, no table row) take tolerance 3.5.
      assert dropped(src, sine: :auto, axiom_counts: {40, 40}) == 31
      assert dropped(src, sine: :auto, axiom_counts: {40, 40}, standard_sine: true) == 30
      assert dropped(src, sine: :auto) == 30
    end

    test "the size limit caps the selection" do
      assert dropped(chain_problem(30), sine: "1.0;2;-1") == 32
      assert dropped(chain_problem(30), sine: "1.0;3;-1") == 31
    end

    test "small problems and problems without conjecture pass whole" do
      # 21 + 4 = 25 axioms pass whole, 26 do not
      assert dropped(chain_problem(21), sine: "1.0;1000;1") == 0
      assert dropped(chain_problem(22), sine: "1.0;1000;1") == 24

      no_goal = String.replace(chain_problem(30), "thf(goal, conjecture, g @ a).", "")
      assert dropped(no_goal, sine: "1.0;1000;1") == 0
    end

    test "negated conjectures seed the selection and are kept" do
      src =
        String.replace(
          chain_problem(30),
          "thf(goal, conjecture, g @ a).",
          "thf(goal, negated_conjecture, ~ (g @ a))."
        )

      {arena, clauses, info} = Clausifier.clausify_with_info(lower(src), sine: :auto)
      assert info.axioms_dropped == 30
      assert {:proved, steps, stats} = Prover.prove_clauses(arena, clauses, timeout_ms: 3_000)
      assert :ok = ProofChecker.verify_refutation(stats.arena, steps)
    end

    test "defined symbols trigger their bodies' symbols" do
      src =
        chain_problem(30)
        |> String.replace("thf(r4, axiom, ! [X: $i]: ((h2 @ X) => (g @ X))).", """
        thf(gg_decl, type, gg: $i > $o).
        thf(gg_def, definition, gg = (^ [X: $i]: (g @ X))).
        thf(r4, axiom, ! [X: $i]: ((h2 @ X) => (g @ X))).
        """)
        |> String.replace("thf(goal, conjecture, g @ a).", "thf(goal, conjecture, gg @ a).")

      {arena, clauses, info} = Clausifier.clausify_with_info(lower(src), sine: :auto)
      assert info.axioms_dropped == 30
      assert {:proved, steps, stats} = Prover.prove_clauses(arena, clauses, timeout_ms: 3_000)
      assert :ok = ProofChecker.verify_refutation(stats.arena, steps)
    end

    test "takes precedence over the relevance filter and Astraea's SInE" do
      src = chain_problem(30)
      assert dropped(src, sine: "1.0;1000;1", relevance_filter: %{}, sine_limit: 5) == 32
    end

    test "internal and external counts come from ProblemStatistics" do
      stats = %ProblemStatistics{local_axioms: 40, included_axioms: 40}
      src = chain_problem(30, "thf(extra, axiom, k1 @ a).\n")
      assert dropped(src, sine: :auto, axiom_counts: stats) == 31
    end
  end
end
