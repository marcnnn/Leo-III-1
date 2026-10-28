defmodule Astraea.ClausifierLeoTest do
  use ExUnit.Case, async: true

  alias Astraea.{Arena, Clausifier, ProofChecker, Prover, TptpLower}
  alias Astraea.External.{TffPrinter, ThfPrinter}

  defp lower(src) do
    {:ok, lowered} = TptpLower.from_string(src)
    lowered
  end

  defp def_names(arena, clauses) do
    for clause <- clauses,
        {_pol, atom} <- clause,
        name <- consts(arena, atom),
        String.starts_with?(name, "def_"),
        uniq: true,
        do: name
  end

  defp consts(arena, id) do
    case Arena.get_node(arena, id) do
      {1, _, _, sym, _} -> [Map.fetch!(arena.symbol_names, sym)]
      {7, _, _, l, _} -> consts(arena, l)
      {t, _, _, l, r} when t in [4, 6, 8] -> consts(arena, l) ++ consts(arena, r)
      {t, _, _, _, r} when t in [5, 9] -> consts(arena, r)
      _ -> []
    end
  end

  defp assert_kernel_refutation(arena, clauses, opts \\ []) do
    assert {:proved, steps, stats} =
             Prover.prove_clauses(arena, clauses, [timeout_ms: 3_000] ++ opts)

    assert :ok = ProofChecker.verify_refutation(stats.arena, steps)
  end

  defp refute_refutation(arena, clauses) do
    result = Prover.prove_clauses(arena, clauses, timeout_ms: 1_500)
    refute match?({:proved, _, _}, result)
  end

  # Without renaming, the axiom distributes to 3 * 3 * 3 = 27 clauses.
  @dnf """
  thf(p_decl, type, p: $i > $o). thf(q_decl, type, q: $i > $o).
  thf(r_decl, type, r: $i > $o). thf(s_decl, type, s: $i > $o).
  thf(t_decl, type, t: $i > $o). thf(u_decl, type, u: $i > $o).
  thf(v_decl, type, v: $i > $o). thf(w_decl, type, w: $i > $o).
  thf(z_decl, type, z: $i > $o). thf(a_decl, type, a: $i).
  thf(ax, axiom, ! [X: $i]: (((p @ X) & (q @ X) & (r @ X)) | ((s @ X) & (t @ X) & (u @ X))
                              | ((v @ X) & (w @ X) & (z @ X)))).
  thf(n1, axiom, ~ (p @ a)). thf(n2, axiom, ~ (t @ a)).
  """

  describe "formula renaming" do
    test "is off by default and shrinks the CNF when enabled" do
      lowered = lower(@dnf)
      {arena0, plain} = Clausifier.clausify(lowered)
      {arena, renamed, info} = Clausifier.clausify_with_info(lowered, renaming: true)

      assert length(plain) == 27 + 2
      assert length(renamed) < length(plain)
      assert info.definitions > 0 and info.cnf_truncated == 0
      assert [_ | _] = def_names(arena, renamed)
      assert def_names(arena0, plain) == []
    end

    test "a threshold above the gain disables renaming" do
      lowered = lower(@dnf)

      {_arena, _cls, info} =
        Clausifier.clausify_with_info(lowered, renaming: true, renaming_threshold: 1_000)

      assert info.definitions == 0
    end

    test "definition symbols are content-addressed and shared" do
      twice =
        String.replace(
          @dnf,
          "thf(n1,",
          "thf(ax2, axiom, ! [Y: $i]: (((p @ Y) & (q @ Y) & (r @ Y)) | ((s @ Y) & (t @ Y) & (u @ Y)) | ((v @ Y) & (w @ Y) & (z @ Y)))).\nthf(n1,"
        )

      {arena1, cls1, info1} = Clausifier.clausify_with_info(lower(@dnf), renaming: true)
      {arena2, cls2, info2} = Clausifier.clausify_with_info(lower(twice), renaming: true)

      # a variant of the same formula reuses the symbols and adds no definitions
      assert Enum.sort(def_names(arena1, cls1)) == Enum.sort(def_names(arena2, cls2))
      assert info1.definitions == info2.definitions

      # a different problem order (other symbol ids) yields the same names
      shuffled =
        String.replace(@dnf, "thf(p_decl, type, p: $i > $o).", "") <>
          "thf(p_decl, type, p: $i > $o).\n"

      {arena3, cls3} = Clausifier.clausify(lower(shuffled), renaming: true)
      assert Enum.sort(def_names(arena1, cls1)) == Enum.sort(def_names(arena3, cls3))
      assert Enum.all?(def_names(arena1, cls1), &(&1 =~ ~r/^def_[0-9a-f]{16}$/))
    end

    test "renamed refutation passes the kernel; satisfiable input stays unrefuted" do
      unsat = @dnf <> "thf(n3, axiom, ~ (w @ a)).\n"
      {arena, clauses} = Clausifier.clausify(lower(unsat), renaming: true)
      assert def_names(arena, clauses) != []
      assert_kernel_refutation(arena, clauses)

      {arena, clauses} = Clausifier.clausify(lower(@dnf), renaming: true)
      refute_refutation(arena, clauses)
    end

    test "conjectures are renamed too and prove through prove_clauses" do
      src = """
      thf(p_decl, type, p: $o). thf(q_decl, type, q: $o). thf(r_decl, type, r: $o).
      thf(s_decl, type, s: $o). thf(t_decl, type, t: $o). thf(u_decl, type, u: $o).
      thf(a1, axiom, ~ p). thf(a2, axiom, ~ s). thf(a3, axiom, ~ t).
      thf(c, conjecture, ((~ p) | (~ q)) & ((~ r) | (~ s)) & ((~ t) | (~ u))).
      """

      {arena, clauses, info} = Clausifier.clausify_with_info(lower(src), renaming: true)
      assert info.definitions > 0
      assert_kernel_refutation(arena, clauses)
    end

    test "definition names print as valid TPTP and re-lower" do
      {arena, clauses} = Clausifier.clausify(lower(@dnf), renaming: true)
      [name | _] = def_names(arena, clauses)

      thf = ThfPrinter.problem(arena, clauses)
      assert thf =~ ~r/type, #{name}: \(?\$i > \$o/
      assert {:ok, relowered} = TptpLower.from_string(thf)
      assert length(relowered.axioms) == length(clauses)

      assert TffPrinter.problem(arena, clauses) =~ name
    end
  end

  describe "Andrews equality" do
    @andrews """
    thf(a_decl, type, a: $i). thf(b_decl, type, b: $i).
    thf(c, conjecture, ! [Q: $i > $i > $o]: ((! [X: $i]: (Q @ X @ X)) => (Q @ a @ b))).
    """

    test "rewrites the formula to an equation" do
      {arena, clauses} = Clausifier.clausify(lower(@andrews))
      a = Arena.lookup_const(arena, "a", :i)
      b = Arena.lookup_const(arena, "b", :i)

      eqs =
        for {:neg, atom} <- Enum.concat(clauses),
            match?({6, _, _, _, _}, Arena.get_node(arena, atom)),
            do: atom

      assert [eq] = eqs
      assert {6, _, _, l, r} = Arena.get_node(arena, eq)
      assert Enum.sort([l, r]) == Enum.sort([a, b])

      {arena0, clauses0} = Clausifier.clausify(lower(@andrews), andrews_eq: false)

      refute Enum.any?(Enum.concat(clauses0), fn {_p, atom} ->
               match?({6, _, _, _, _}, Arena.get_node(arena0, atom))
             end)
    end

    test "refutation with a = b passes the kernel; without it nothing is refuted" do
      {arena, clauses} = Clausifier.clausify(lower(@andrews <> "thf(ab, axiom, a = b).\n"))
      assert_kernel_refutation(arena, clauses)

      {arena, clauses} = Clausifier.clausify(lower(@andrews))
      refute_refutation(arena, clauses)
    end

    test "clause-level rewrite adds the instance and keeps the clause" do
      src = """
      thf(c_decl, type, c: $i). thf(d_decl, type, d: $i). thf(e_decl, type, e: $i).
      thf(ax, axiom, ! [X: $i > $i > $o]: ((X @ c @ c) => (X @ d @ e))).
      thf(ne, axiom, d != e).
      """

      {arena, clauses, info} = Clausifier.clausify_with_info(lower(src))
      assert info.andrews_instances == 1
      {_arena, clauses0} = Clausifier.clausify(lower(src), andrews_eq: false)
      assert Enum.all?(clauses0, &(&1 in clauses))
      assert_kernel_refutation(arena, clauses)
    end

    test "the instance alone would lose the refutation, so the original stays" do
      # `X := ^ [Y, Z]: Y = c & Z = c` refutes this; the Andrews instance `d = d` is valid.
      src = """
      thf(c_decl, type, c: $i). thf(d_decl, type, d: $i).
      thf(ax, axiom, ! [X: $i > $i > $o]: ((X @ c @ c) => (X @ d @ d))).
      thf(ne, axiom, c != d).
      """

      {_arena, clauses, info} = Clausifier.clausify_with_info(lower(src))
      {_arena, clauses0} = Clausifier.clausify(lower(src), andrews_eq: false)
      assert info.andrews_instances == 0
      assert Enum.all?(clauses0, &(&1 in clauses))
      assert length(clauses) == length(clauses0)
    end
  end

end
