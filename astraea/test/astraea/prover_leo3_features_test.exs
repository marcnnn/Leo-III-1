defmodule Astraea.ProverLeo3FeaturesTest do
  use ExUnit.Case, async: true

  alias Astraea.{Arena, ProofChecker, Prover, TptpLower}

  defp prove(src, opts) do
    Prover.prove_string(src, Keyword.merge([timeout_ms: 1_500], opts))
  end

  defp fvars(arena, n) do
    Enum.map_reduce(1..n, arena, fn i, ar ->
      {ar, v} = Arena.mk_fvar(ar, i, :i)
      {v, ar}
    end)
  end

  defp assert_kernel_proof(result) do
    assert {:proved, steps, stats} = result
    assert :ok == ProofChecker.verify_refutation(stats.arena, steps)
    steps
  end

  describe "set of support (Leo-III sos)" do
    @sos_thm """
    thf(p_t, type, p: $o). thf(q_t, type, q: $o). thf(r_t, type, r: $o).
    thf(a1, axiom, p). thf(a2, axiom, p => q). thf(a3, axiom, q => r).
    thf(c, conjecture, r).
    """

    @sos_csa """
    thf(p_t, type, p: $i > $o). thf(a_t, type, a: $i).
    thf(ax, axiom, p @ a). thf(c, conjecture, ! [X: $i]: (p @ X)).
    """

    test "proves through the conjecture and passes the kernel" do
      assert_kernel_proof(prove(@sos_thm, sos: true))
    end

    test "marks the run incomplete, so a saturation is no model answer" do
      assert {:saturated, stats} = prove(@sos_csa, sos: true)
      assert :sos in stats.incomplete_reasons
      assert {:saturated, %{complete: true}} = prove(@sos_csa, [])
    end

    test "only conjecture clauses are in the set of support" do
      {:ok, lowered} = TptpLower.from_string(@sos_thm)
      # Without the conjecture the axioms alone do not refute, and nothing is marked.
      no_conj = %{lowered | conjectures: []}
      assert {:saturated, stats} = Prover.prove_lowered(no_conj, sos: true)
      refute :sos in stats.incomplete_reasons
    end
  end

end
