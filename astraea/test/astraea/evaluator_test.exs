defmodule Astraea.EvaluatorTest do
  use ExUnit.Case, async: true

  alias Astraea.{Arena, Evaluator, ProofChecker}

  setup do
    arena = Arena.new()
    {arena, c_id} = Arena.mk_const(arena, "c", :i)
    {arena, d_id} = Arena.mk_const(arena, "d", :i)
    {arena, f_id} = Arena.mk_const(arena, "f", {:arrow, :i, :i})
    {arena, true_id} = Arena.mk_const(arena, "$true", :o)
    {arena, false_id} = Arena.mk_const(arena, "$false", :o)

    %{
      arena: arena,
      c: c_id,
      d: d_id,
      f: f_id,
      true_const: true_id,
      false_const: false_id
    }
  end

  describe "eval/4 beta-reduction and lambda calculus" do
    test "identity lambda reduces to its argument", %{arena: arena, c: c} do
      # (^ [X: i]: X) @ c  ->  c
      {arena, x_bvar} = Arena.mk_bvar(arena, 0, :i)
      {arena, id_lam} = Arena.mk_lam(arena, :i, x_bvar)
      {arena, app} = Arena.mk_app(arena, id_lam, c)

      {_arena, result} = Evaluator.eval(arena, app)
      assert result == c
    end

    test "higher-order lambda self-application reduces correctly", %{arena: arena, f: f, c: c} do
      # (^ [F: i > i]: ^ [X: i]: F @ (F @ X)) @ f @ c  ->  f @ (f @ c)
      {arena, f_bvar} = Arena.mk_bvar(arena, 1, {:arrow, :i, :i})
      {arena, x_bvar} = Arena.mk_bvar(arena, 0, :i)
      {arena, fx} = Arena.mk_app(arena, f_bvar, x_bvar)
      {arena, ffx} = Arena.mk_app(arena, f_bvar, fx)
      {arena, inner_lam} = Arena.mk_lam(arena, :i, ffx)
      {arena, outer_lam} = Arena.mk_lam(arena, {:arrow, :i, :i}, inner_lam)

      {arena, app1} = Arena.mk_app(arena, outer_lam, f)
      {arena, app2} = Arena.mk_app(arena, app1, c)

      {arena, result} = Evaluator.eval(arena, app2)

      # Expect f @ (f @ c)
      {arena, expected_fc} = Arena.mk_app(arena, f, c)
      {_arena, expected_ffc} = Arena.mk_app(arena, f, expected_fc)
      assert result == expected_ffc
    end
  end

  describe "eval/4 combinator reduction" do
    test "I combinator: I x -> x", %{arena: arena, c: c} do
      {arena, comb_i} = Arena.mk_comb(arena, :i, {:arrow, :i, :i})
      {arena, app} = Arena.mk_app(arena, comb_i, c)

      {_arena, result} = Evaluator.eval(arena, app)
      assert result == c
    end

    test "K combinator: K a x -> a", %{arena: arena, c: c, d: d} do
      ty_k = {:arrow, :i, {:arrow, :i, :i}}
      {arena, comb_k} = Arena.mk_comb(arena, :k, ty_k)
      {arena, app1} = Arena.mk_app(arena, comb_k, c)
      {arena, app2} = Arena.mk_app(arena, app1, d)

      {_arena, result} = Evaluator.eval(arena, app2)
      assert result == c
    end

    test "B combinator: B f g x -> f (g x)", %{arena: arena, f: f, c: c} do
      ty_f = {:arrow, :i, :i}
      ty_b = {:arrow, ty_f, {:arrow, ty_f, ty_f}}
      {arena, comb_b} = Arena.mk_comb(arena, :b, ty_b)

      {arena, app1} = Arena.mk_app(arena, comb_b, f)
      {arena, app2} = Arena.mk_app(arena, app1, f)
      {arena, app3} = Arena.mk_app(arena, app2, c)

      {_arena, result} = Evaluator.eval(arena, app3)

      {arena, fc} = Arena.mk_app(arena, f, c)
      {_arena, expected} = Arena.mk_app(arena, f, fc)
      assert result == expected
    end

    test "C combinator: C f g x -> f x g", %{arena: arena, c: c, d: d} do
      {arena, rel} = Arena.mk_const(arena, "r", {:arrow, :i, {:arrow, :i, :o}})
      ty_c = {:arrow, {:arrow, :i, {:arrow, :i, :o}}, {:arrow, :i, {:arrow, :i, :o}}}
      {arena, comb_c} = Arena.mk_comb(arena, :c, ty_c)

      {arena, app1} = Arena.mk_app(arena, comb_c, rel)
      {arena, app2} = Arena.mk_app(arena, app1, c)
      {arena, app3} = Arena.mk_app(arena, app2, d)

      {_arena, result} = Evaluator.eval(arena, app3)

      {arena, rc} = Arena.mk_app(arena, rel, d)
      {_arena, expected} = Arena.mk_app(arena, rc, c)
      assert result == expected
    end

    test "S combinator: S f g x -> (f x) (g x)", %{arena: arena, f: f, c: c} do
      {arena, h} = Arena.mk_const(arena, "h", {:arrow, :i, {:arrow, :i, :i}})
      ty_s = {:arrow, {:arrow, :i, {:arrow, :i, :i}}, {:arrow, {:arrow, :i, :i}, {:arrow, :i, :i}}}
      {arena, comb_s} = Arena.mk_comb(arena, :s, ty_s)

      {arena, app1} = Arena.mk_app(arena, comb_s, h)
      {arena, app2} = Arena.mk_app(arena, app1, f)
      {arena, app3} = Arena.mk_app(arena, app2, c)

      {_arena, result} = Evaluator.eval(arena, app3)

      {arena, hc} = Arena.mk_app(arena, h, c)
      {arena, fc} = Arena.mk_app(arena, f, c)
      {_arena, expected} = Arena.mk_app(arena, hc, fc)
      assert result == expected
    end
  end

  describe "eval/4 boolean connectives and equality" do
    test "boolean negation", %{arena: arena, true_const: t, false_const: f} do
      {arena, not_t} = Arena.mk_not(arena, t)
      {arena, not_f} = Arena.mk_not(arena, f)

      {_arena, res1} = Evaluator.eval(arena, not_t)
      assert res1 == f

      {_arena, res2} = Evaluator.eval(arena, not_f)
      assert res2 == t
    end

    test "boolean disjunction", %{arena: arena, true_const: t, false_const: f} do
      {arena, tf} = Arena.mk_or(arena, t, f)
      {arena, ff} = Arena.mk_or(arena, f, f)

      {_arena, res1} = Evaluator.eval(arena, tf)
      assert res1 == t

      {_arena, res2} = Evaluator.eval(arena, ff)
      assert res2 == f
    end

    test "equality reflection", %{arena: arena, c: c, true_const: t, false_const: f} do
      {arena, eq_same} = Arena.mk_eq(arena, c, c)
      {arena, eq_bool_diff} = Arena.mk_eq(arena, t, f)

      {_arena, res1} = Evaluator.eval(arena, eq_same)
      assert res1 == t

      {_arena, res2} = Evaluator.eval(arena, eq_bool_diff)
      assert res2 == f
    end

    test "universal quantification over booleans", %{
      arena: arena,
      true_const: t,
      false_const: f
    } do
      # ! [X: $o]: X | ~X  (Law of Excluded Middle)
      {arena, x} = Arena.mk_bvar(arena, 0, :o)
      {arena, not_x} = Arena.mk_not(arena, x)
      {arena, lem} = Arena.mk_or(arena, x, not_x)
      {arena, forall_lem} = Arena.mk_forall(arena, :o, lem)

      {_arena, res1} = Evaluator.eval(arena, forall_lem)
      assert res1 == t

      # ! [X: $o]: X  (False)
      {arena, forall_false} = Arena.mk_forall(arena, :o, x)
      {_arena, res2} = Evaluator.eval(arena, forall_false)
      assert res2 == f
    end
  end

  describe "eval_sandboxed/4 safety on BEAM" do
    test "evaluates successfully within budget", %{arena: arena, c: c} do
      {arena, x_bvar} = Arena.mk_bvar(arena, 0, :i)
      {arena, id_lam} = Arena.mk_lam(arena, :i, x_bvar)
      {arena, app} = Arena.mk_app(arena, id_lam, c)

      assert {:ok, _arena, result} = Evaluator.eval_sandboxed(arena, app, %{}, 100)
      assert result == c
    end
  end

  describe "simplify_clause/4" do
    test "detects tautology with positive $true", %{arena: arena, true_const: t, c: c} do
      {arena, atom} = Arena.mk_eq(arena, c, c)
      clause = MapSet.new([{:pos, atom}, {:pos, t}])

      {_arena, status} = Evaluator.simplify_clause(arena, clause)
      assert status == :tautology
    end

    test "drops false literals and derives empty clause when all refuted", %{
      arena: arena,
      false_const: f
    } do
      clause = MapSet.new([{:pos, f}])

      {_arena, {:simplified, new_clause}} = Evaluator.simplify_clause(arena, clause)
      assert MapSet.size(new_clause) == 0
    end
  end

  describe "find_counterexample/4 and filter_candidate_lambda/4" do
    test "finds counterexample for P | Q => P", %{
      arena: arena,
      true_const: t,
      false_const: f
    } do
      # Conjecture: (P | Q) => P  (free vars P=1, Q=2 of type $o)
      {arena, p} = Arena.mk_fvar(arena, 1, :o)
      {arena, q} = Arena.mk_fvar(arena, 2, :o)
      {arena, p_or_q} = Arena.mk_or(arena, p, q)
      {arena, conj} = Arena.mk_imp(arena, p_or_q, p)

      result = Evaluator.find_counterexample(arena, conj, [])
      assert {:counterexample, env} = result
      assert Map.get(env, 1) == f
      assert Map.get(env, 2) == t
    end

    test "filters candidate lambda against example input-outputs", %{
      arena: arena,
      true_const: t,
      false_const: f
    } do
      # Candidate 1: ^ [X: $o]: $true
      {arena, cand_always_true} = Arena.mk_lam(arena, :o, t)
      # Candidate 2: ^ [X: $o]: X (identity)
      {arena, x} = Arena.mk_bvar(arena, 0, :o)
      {arena, cand_id} = Arena.mk_lam(arena, :o, x)

      # Examples: input $true -> $true, input $false -> $false
      examples = [{t, t}, {f, f}]

      assert Evaluator.filter_candidate_lambda(arena, cand_id, examples) == true
      assert Evaluator.filter_candidate_lambda(arena, cand_always_true, examples) == false
    end
  end
  describe "reduction count metric and determinism" do
    test "reduction step budget stops evaluation deterministically", %{arena: arena, c: c} do
      # Set up an evaluation with a tiny budget of 0 steps
      {arena, x_bvar} = Arena.mk_bvar(arena, 0, :i)
      {arena, id_lam} = Arena.mk_lam(arena, :i, x_bvar)
      {arena, app} = Arena.mk_app(arena, id_lam, c)

      # With max_steps: 0, it halts without reducing
      {_arena, unreduced} = Evaluator.eval(arena, app, %{}, max_steps: 0)
      assert unreduced == app
    end

    test "Prover respects max_reductions budget and reports reductions in stats" do
      src = """
      thf(i_type, type, i: $tType).
      thf(a_decl, type, a: i).
      thf(b_decl, type, b: i).
      thf(f_decl, type, f: i > i).
      thf(p_decl, type, p: i > $o).
      thf(ax1, axiom, ! [X: i]: (p @ (f @ X))).
      thf(conj, conjecture, p @ a).
      """

      # Run with an extremely small reduction budget
      res = Astraea.Prover.prove_string(src, max_reductions: 50, timeout_ms: 5_000)
      assert {:resource_out, stats} = res
      assert is_integer(stats.reductions)
      assert stats.reductions >= 50
    end
  end

  describe "ProofChecker LCF verification of {:eval, ...} rule" do
    test "verifies clausal evaluation step deriving empty clause", %{arena: arena, false_const: f} do
      # Axiom 1: {pos: $false}
      # Eval 2: evaluates {pos: $false} to {} (empty clause)
      clause1 = MapSet.new([{:pos, f}])
      steps = [
        {:axiom, 1, clause1},
        {:eval, 2, 1, MapSet.new()}
      ]

      assert ProofChecker.verify_refutation(arena, steps) == :ok
    end

    test "rejects invalid {:eval, ...} claim", %{arena: arena, c: c} do
      # Axiom 1: {pos: c = c}
      {arena, eq} = Arena.mk_eq(arena, c, c)
      clause1 = MapSet.new([{:pos, eq}])

      # Claiming eval derived empty clause from {pos: c = c} is false (it is a tautology, not empty)
      steps = [
        {:axiom, 1, clause1},
        {:eval, 2, 1, MapSet.new()}
      ]

      assert {:error, {:invalid_eval, 2, 1}} = ProofChecker.verify_refutation(arena, steps)
    end
  end
end
