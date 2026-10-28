defmodule Astraea.Leo3WiringTest do
  @moduledoc """
  Leo-III features reached through the prover options: the CPO term ordering in
  demodulation.
  """
  use ExUnit.Case, async: true

  alias Astraea.{Arena, ProofChecker, Prover}
  alias Astraea.Engine.Demodulator

  @thm_src """
  thf(q_type, type, q: ($i > $i) > $o).
  thf(p_type, type, p: $i > $o).
  thf(g_type, type, g: $i > $i).
  thf(a_type, type, a: $i).
  thf(ax_pa, axiom, p @ a).
  thf(ax_cond_id, axiom, ! [X: $i]: ((p @ a) => ((g @ X) = X))).
  thf(ax_q_id, axiom, q @ (^ [X: $i]: X)).
  thf(conj_qg, conjecture, q @ g).
  """

  defp assert_verified({:proved, steps, stats}) do
    assert :ok = ProofChecker.verify_refutation(stats.arena, steps)
  end

  describe "CPO term ordering" do
    test "demodulation rules keep the ordering they were oriented with" do
      arena = Arena.new()
      {arena, i} = Arena.intern_type(arena, :i)
      {arena, fi} = Arena.intern_type(arena, {:arrow, i, i})
      {arena, f} = Arena.mk_const(arena, "f", fi)
      {arena, a} = Arena.mk_const(arena, "a", i)
      {arena, fa} = Arena.mk_app(arena, f, a)
      {arena, eq} = Arena.mk_eq(arena, fa, a)
      item = %{id: 1, lits: MapSet.new([{:pos, eq}])}

      for ord <- [:kbo, :cpo] do
        assert [%{lhs: ^fa, rhs: ^a, ordering: ^ord}] =
                 Demodulator.rules(arena, item, term_ordering: ord)
      end
    end

    test "Leo-III's CPO strategies prove an equational theorem with verified proofs" do
      assert {:proved, _, _} =
               result = Prover.prove_string(@thm_src, ordered: true, term_ordering: :cpo)

      assert_verified(result)
    end
  end
end
