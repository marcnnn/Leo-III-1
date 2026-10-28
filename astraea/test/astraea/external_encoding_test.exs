defmodule Astraea.ExternalEncodingTest do
  use ExUnit.Case, async: true

  alias Astraea.{Clausifier, External, ProofChecker, Prover, TptpLower}

  alias Astraea.External.{
    FofPrinter,
    FolEncoding,
    Monotonicity,
    Reconstruct,
    SZS,
    TffPrinter
  }

  # Lambdas (with and without free variables), partial application, Boolean
  # terms in argument positions, and a quantifier in term position.
  @ho_src """
  thf(q_type, type, q: ($i > $i) > $o).
  thf(p_type, type, p: $i > $o).
  thf(r_type, type, r: $o > $o).
  thf(g_type, type, g: $i > $i).
  thf(f_type, type, f: $i > $i > $i).
  thf(a_type, type, a: $i).
  thf(ax_pa, axiom, p @ a).
  thf(ax_lam, axiom, ! [Y: $i]: (q @ (^ [X: $i]: (f @ X @ Y)))).
  thf(ax_partial, axiom, q @ (f @ a)).
  thf(ax_id, axiom, q @ (^ [X: $i]: X)).
  thf(ax_not, axiom, ! [X: $i]: (r @ (~ (p @ X)))).
  thf(ax_all, axiom, r @ (! [X: $i]: (p @ X))).
  thf(ax_eq, axiom, r @ ((g @ a) = a)).
  thf(conj_qg, conjecture, q @ g).
  """

  # Unsatisfiable after any encoding: the lambda and Boolean terms that must
  # match are closed and identical, the rest is first-order reasoning.
  @closed_src """
  thf(q_type, type, q: ($i > $i) > $o).
  thf(r_type, type, r: $o > $o).
  thf(p_type, type, p: $i > $o).
  thf(s_type, type, s: $i > $o).
  thf(f_type, type, f: $i > $i > $i).
  thf(a_type, type, a: $i).
  thf(ax_q, axiom, q @ (^ [X: $i]: (f @ X @ a))).
  thf(ax_r, axiom, r @ (~ (p @ a))).
  thf(ax_s, axiom, ! [Y: $i]: (((q @ (^ [X: $i]: (f @ X @ a))) & (r @ (~ (p @ a)))) => (s @ Y))).
  thf(conj, conjecture, s @ a).
  """

  # Needs the free variable `Y` and `Z` instantiated inside a lambda and a
  # Boolean term: refutable through SKI combinators and proxies (Leo-III's
  # encoding), but not through lifting, which would need extensionality.
  @open_src """
  thf(q_type, type, q: ($i > $i) > $o).
  thf(r_type, type, r: $o > $o).
  thf(p_type, type, p: $i > $o).
  thf(f_type, type, f: $i > $i > $i).
  thf(a_type, type, a: $i).
  thf(ax_q, axiom, ! [Y: $i]: (q @ (^ [X: $i]: (f @ X @ Y)))).
  thf(ax_r, axiom, ! [Z: $i]: (r @ (~ (p @ Z)))).
  thf(conj, conjecture, (q @ (^ [X: $i]: (f @ X @ a))) & (r @ (~ (p @ a)))).
  """

  @fo_src """
  tff(p_type, type, p: $i > $o).
  tff(f_type, type, f: ($i * $i) > $i).
  tff(a_type, type, a: $i).
  tff(ax, axiom, ! [X: $i]: p(f(X, a))).
  tff(conj, conjecture, ? [Y: $i]: p(Y)).
  """

  @tff_variants for lambda <- [:lambda_lifting, :ski],
                    arity <- [:applicative, :min_arity],
                    booleans <- [:lift, :proxies],
                    do: [lambda: lambda, arity: arity, booleans: booleans, types: :mono_native]

  @fof_variants for base <- [:default, :leo3],
                    types <- [:mono_guards, :mono_guards_light],
                    do: [base: base, types: types]

  defp clausify(src) do
    {:ok, lowered} = TptpLower.from_string(src)
    Clausifier.clausify(lowered)
  end

  defp tptp_errors(source) do
    {:ok, _unit, diagnostics} =
      Tptp.Unit.from_string(source,
        resolver: {Tptp.Resolver.Fs, root: System.tmp_dir!()},
        max_concurrency: 1
      )

    Enum.filter(diagnostics, &(&1.severity == :error))
  end

  defp print(arena, clauses, enc) do
    if FolEncoding.untyped?(enc),
      do: FofPrinter.problem(arena, clauses, encoding: enc),
      else: TffPrinter.problem(arena, clauses, encoding: enc)
  end

  defp formula_names(printed) do
    ~r/^(?:tff|fof)\(([a-z0-9_]+), /m
    |> Regex.scan(printed, capture: :all_but_first)
    |> List.flatten()
  end

  # Re-proves the printed problem with Astraea itself (as a first-order input).
  defp reprove(printed) do
    {:ok, lowered} = TptpLower.from_string(printed)
    Prover.prove_lowered(lowered, timeout_ms: 5_000, sine_limit: nil)
  end

  describe "options" do
    test "normalizes presets and keyword lists, rejecting unknown values" do
      assert FolEncoding.normalize!(nil) == FolEncoding.default()
      assert FolEncoding.normalize!(:leo3)[:lambda] == :ski
      assert FolEncoding.normalize!(lambda: :ski)[:arity] == :applicative
      assert FolEncoding.normalize!(base: :leo3, types: :mono_guards)[:booleans] == :proxies

      assert {:error, {:invalid_encoding, _}} = FolEncoding.normalize(lambda: :turner)
      assert {:error, {:invalid_encoding, _}} = FolEncoding.normalize(colour: :red)

      assert_raise ArgumentError, fn ->
        TffPrinter.problem(Astraea.Arena.new(), [], encoding: [types: :mono_guards])
      end

      assert_raise ArgumentError, fn ->
        FofPrinter.problem(Astraea.Arena.new(), [], encoding: [types: :mono_native])
      end
    end

    test "the default encoding is the historical applicative one with lambda lifting" do
      {arena, clauses} = clausify(@ho_src)

      assert TffPrinter.problem(arena, clauses) ==
               TffPrinter.problem(arena, clauses, encoding: :default)

      printed = TffPrinter.problem(arena, clauses)

      assert printed =~
               ~r/astraea_app_\d+\(astraea_lift_\d+\(V\d+\), B0\) = astraea_app_\d+\(astraea_app_\d+\(f, B0\), V\d+\)/

      assert printed =~ ~r/astraea_holds\(astraea_lift_\d+\(V\d+\)\) <=> \(~ astraea_holds/
      refute printed =~ "astraea_comb_"
    end
  end

  describe "printed problems" do
    test "every TFF variant is well-formed and keeps the clause names" do
      {arena, clauses} = clausify(@ho_src)
      clause_names = Enum.map(0..(length(clauses) - 1), &"c#{&1}")

      for enc <- @tff_variants do
        printed = TffPrinter.problem(arena, clauses, encoding: enc)
        assert tptp_errors(printed) == [], "#{inspect(enc)}:\n#{printed}"
        refute printed =~ "thf("
        refute printed =~ "^"
        names = formula_names(printed)
        assert Enum.filter(names, &String.starts_with?(&1, "c")) == clause_names
        assert names -- clause_names == Enum.filter(names, &(&1 =~ ~r/^(d\d+|sort_\d+|sym_\d+)$/))

        assert Reconstruct.clause_indices(MapSet.new(names)) ==
                 Enum.to_list(0..(length(clauses) - 1))
      end
    end

    test "every FOF variant is well-formed, untyped and keeps the clause names" do
      {arena, clauses} = clausify(@ho_src)

      for enc <- @fof_variants do
        printed = FofPrinter.problem(arena, clauses, encoding: enc)
        assert tptp_errors(printed) == [], "#{inspect(enc)}:\n#{printed}"
        refute printed =~ "tff("
        refute printed =~ "$tType"
        assert length(Regex.scan(~r/^fof\(c\d+, axiom/m, printed)) == length(clauses)
      end
    end

    test "SKI emits typed combinators with their defining equations" do
      {arena, clauses} = clausify(@ho_src)
      printed = TffPrinter.problem(arena, clauses, encoding: [lambda: :ski, booleans: :proxies])

      refute printed =~ "astraea_lift_"
      # ^[X]: X is I, ^[X]: f @ X @ Y is C f Y, f @ a stays a partial application
      assert printed =~
               ~r/tff\(d\d+, axiom, \(! \[A0: \$i\]: \(astraea_app_\d+\(astraea_comb_i_\d+, A0\) = A0\)\)\)/

      assert printed =~ ~r/astraea_comb_c_\d+/
      assert printed =~ ~r/astraea_app_\d+\(f, a\)/
    end

    test "minimal arity passes arguments directly and keeps predicates" do
      {arena, clauses} = clausify(@ho_src)
      printed = TffPrinter.problem(arena, clauses, encoding: [arity: :min_arity])

      # `f` occurs partially applied (`f @ a`), so it takes one argument directly.
      assert printed =~ ~r/type, f: \$i > astraea_fun_\d+\)/
      # `q` and `r` only occur in formula positions: predicates over encoded arguments.
      assert printed =~ ~r/type, q: astraea_fun_\d+ > \$o\)/
      assert printed =~ ~r/type, r: astraea_bool > \$o\)/
      # `p` also occurs unapplied inside the quantifier proxy only with proxies;
      # with lifting it stays a predicate.
      assert printed =~ ~r/type, p: \$i > \$o\)/
      assert printed =~ "p(a)"
    end

    test "proxies replace Boolean terms by connective symbols with axioms" do
      {arena, clauses} = clausify(@ho_src)
      printed = TffPrinter.problem(arena, clauses, encoding: :leo3)

      assert printed =~ ~r/r\(astraea_not\(/
      assert printed =~ ~r/r\(astraea_forall_\d+\(p\)\)/
      assert printed =~ ~r/r\(astraea_eq_\d+\(/
      assert printed =~ ~r/astraea_holds\(astraea_not\(A0\)\) <=> \(~ astraea_holds\(A0\)\)/
      assert printed =~ ~r/astraea_holds\(astraea_eq_\d+\(A0, A1\)\) <=> \(A0 = A1\)/
      assert printed =~ ~r/<=> \(! \[A1: \$i\]: astraea_holds\(astraea_app_\d+\(A0, A1\)\)\)/
      refute printed =~ "astraea_lift_"
    end

    test "light guards only guard sorts with naked variables" do
      {arena, clauses} = clausify(@ho_src)
      full = FofPrinter.problem(arena, clauses, encoding: [types: :mono_guards])
      light = FofPrinter.problem(arena, clauses, encoding: [types: :mono_guards_light])

      guards = fn printed ->
        ~r/^% (astraea_is_\d+) guards/m
        |> Regex.scan(printed, capture: :all_but_first)
        |> List.flatten()
      end

      # `^[X]: X` is defined by `lift @ B0 = B0` (lifting) or `I @ A0 = A0` (SKI):
      # a naked variable of sort `$i`. No other sort has one.
      assert guards.(light) == ["astraea_is_1"]

      assert light =~
               ~r/\(! \[B0\]: \(\(astraea_is_1\(B0\)\) => \(astraea_app_\d+\(astraea_lift_\d+, B0\) = B0\)\)\)/

      ski = FofPrinter.problem(arena, clauses, encoding: [lambda: :ski])
      assert guards.(ski) == ["astraea_is_1"]
      assert ski =~ ~r/\(! \[A0\]: \(\(astraea_is_1\(A0\)\) => /

      # Without `^[X]: X` every sort is monotonic and nothing is guarded.
      {arena2, clauses2} = clausify(@closed_src)
      assert guards.(FofPrinter.problem(arena2, clauses2)) == []

      # Full guards guard every sort and type every symbol.
      assert length(guards.(full)) > 1
      assert full =~ ~r/\(! \[V\d+\]: \(\(astraea_is_1\(V\d+\)\) => /
      assert full =~ ~r/fof\(ty\d+, axiom, astraea_is_1\(a\)\)/
      assert full =~ ~r/fof\(ty\d+, axiom, \(\? \[X\]: astraea_is_1\(X\)\)\)/
    end
  end

  describe "monotonicity" do
    test "naked variables in positive equations make a sort non-monotonic" do
      x = {:var, "X", 1}
      y = {:var, "Y", 2}
      c = {:fn, "c", []}

      assert Monotonicity.nonmonotonic_sorts([{:all, [{"X", 1}], {:eq, x, c}}]) == MapSet.new([1])
      assert Monotonicity.monotone?(1, [{:all, [{"X", 1}], {:not, {:eq, x, c}}}])
      assert Monotonicity.monotone?(1, [{:eq, {:fn, "f", [x]}, c}])
      assert Monotonicity.nonmonotonic_sorts([{:not, {:not, {:eq, c, y}}}]) == MapSet.new([2])

      assert Monotonicity.nonmonotonic_sorts([{:iff, {:pred, "p", []}, {:not, {:eq, x, y}}}]) ==
               MapSet.new([1, 2])
    end
  end

  describe "round trip" do
    test "encodings of an unsatisfiable problem are refuted again" do
      {arena, clauses} = clausify(@closed_src)

      for enc <- @tff_variants ++ @fof_variants do
        printed = print(arena, clauses, enc)
        assert {:proved, steps, stats} = reprove(printed), "#{inspect(enc)}:\n#{printed}"
        assert :ok == ProofChecker.verify_refutation(stats.arena, steps)
      end
    end

    test "Leo-III's encoding instantiates variables inside lambdas and Boolean terms" do
      {arena, clauses} = clausify(@open_src)

      for enc <- [
            :leo3,
            [base: :leo3, types: :mono_guards_light],
            [base: :leo3, types: :mono_guards]
          ] do
        printed = print(arena, clauses, enc)
        assert {:proved, _steps, _stats} = reprove(printed), "#{inspect(enc)}:\n#{printed}"
      end

      # Lifting introduces distinct symbols for `^[X]: f @ X @ Y` and `^[X]: f @ X @ a`;
      # identifying them would need extensionality, which no encoding adds.
      refute match?({:proved, _, _}, reprove(TffPrinter.problem(arena, clauses)))
    end

    test "combinator nodes become combinator constants with their equations" do
      alias Astraea.Arena
      arena = Arena.new()
      {arena, p} = Arena.mk_const(arena, "p", {:arrow, :i, :o})
      {arena, a} = Arena.mk_const(arena, "a", :i)
      {arena, b} = Arena.mk_const(arena, "b", :i)
      {arena, k} = Arena.mk_comb(arena, :k, {:arrow, :i, {:arrow, :i, :i}})
      {arena, ka} = Arena.mk_app(arena, k, a)
      {arena, kab} = Arena.mk_app(arena, ka, b)
      {arena, p_kab} = Arena.mk_app(arena, p, kab)
      {arena, p_a} = Arena.mk_app(arena, p, a)
      clauses = [MapSet.new([{:neg, p_kab}]), MapSet.new([{:pos, p_a}])]

      for enc <- @tff_variants ++ @fof_variants do
        printed = print(arena, clauses, enc)
        assert printed =~ ~r/astraea_comb_k_\d+/
        assert tptp_errors(printed) == [], "#{inspect(enc)}:\n#{printed}"
        assert {:proved, _steps, _stats} = reprove(printed), "#{inspect(enc)}:\n#{printed}"
      end
    end

    test "first-order clause sets are encoded completely" do
      {arena, clauses} = clausify(@fo_src)
      assert FolEncoding.first_order?(arena, clauses)
      assert FolEncoding.complete?(arena, clauses, :leo3)

      printed = TffPrinter.problem(arena, clauses, encoding: [arity: :min_arity])
      refute printed =~ "astraea_app_"
      refute printed =~ "astraea_holds"
      assert printed =~ ~r/type, f: \(\$i \* \$i\) > \$i\)/

      {ho_arena, ho_clauses} = clausify(@ho_src)
      refute FolEncoding.complete?(ho_arena, ho_clauses)
    end
  end

  describe "External integration" do
    @describetag :external

    setup do
      dir =
        Path.join(
          System.tmp_dir!(),
          "astraea_encoding_test_#{System.unique_integer([:positive])}"
        )

      File.mkdir_p!(dir)
      on_exit(fn -> File.rm_rf(dir) end)
      {:ok, dir: dir}
    end

    # A stand-in prover citing every clause `c<i>` and definition `d<k>` of its input
    # as unsat core, like E's `file(_, Name)` source annotations.
    defp citing_prover(dir, formats) do
      path = Path.join(dir, "cite_all")

      File.write!(path, """
      #!/bin/sh
      echo "% SZS status Unsatisfiable"
      echo "% SZS output start CNFRefutation"
      grep -o '^[a-z][a-z][a-z](\\(c\\|d\\|ty\\)[0-9]*' "$1" | sed 's/^...(//' | while read n; do
        echo "cnf($n, axiom, \\$false, file('input.p', $n))."
      done
      echo "% SZS output end CNFRefutation"
      """)

      File.chmod!(path, 0o755)

      %{
        name: :cite_all,
        executables: [path],
        formats: formats,
        args: fn _limits, file -> [file] end
      }
    end

    test "encoding options reach the printed problem and cores map back to clauses", %{dir: dir} do
      {arena, clauses} = clausify(@open_src)
      spec = citing_prover(dir, [:tff])
      indices = Enum.to_list(0..(length(clauses) - 1))

      for {opts, header} <- [
            {[], "TffPrinter (lambda: lambda_lifting"},
            {[encoding: :leo3], "TffPrinter (lambda: ski, arity: min_arity, booleans: proxies"},
            {[encoding: [types: :mono_guards]], "FofPrinter"},
            {[format: :fof], "types: mono_guards_light"}
          ] do
        assert {:ok, source} = External.clause_problem(spec, arena, clauses, opts)
        assert source =~ header

        assert {:ok, %External.Result{status: :unsatisfiable, proof: proof}} =
                 External.prove_clauses(spec, arena, clauses, [tmp_dir: dir] ++ opts)

        assert SZS.classify(:unsatisfiable) == :unsat
        assert proof |> Reconstruct.core_names() |> Reconstruct.clause_indices() == indices

        assert {:proved, steps, stats} =
                 Reconstruct.clauses(arena, clauses, Reconstruct.core_names(proof))

        assert :ok == ProofChecker.verify_refutation(stats.arena, steps)
      end

      assert {:error, {:invalid_encoding, _}} =
               External.prove_clauses(spec, arena, clauses,
                 tmp_dir: dir,
                 encoding: [lambda: :none]
               )
    end
  end
end
