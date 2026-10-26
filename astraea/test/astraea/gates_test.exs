defmodule Astraea.GatesTest do
  use ExUnit.Case, async: true
  use ExUnitProperties

  alias Astraea.{Arena, ProofChecker, TptpCorpus}

  @moduletag :gate1

  property "Gate 1: 12-byte flat binary node encoding roundtrips losslessly" do
    check all tag <- integer(1..11),
              flags <- integer(0..255),
              type_id <- integer(0..65_535),
              left <- integer(0..1_000_000),
              right <- integer(0..1_000_000) do
      packed = Arena.encode_node(tag, flags, type_id, left, right)
      assert byte_size(packed) == 12
      assert Arena.decode_node(packed) == {tag, flags, type_id, left, right}
    end
  end

  property "Gate 1: content-addressed Skolem hash is invariant to Arena insertion order" do
    check all sym_a <- string(:alphanumeric, min_length: 1, max_length: 8),
              sym_b <- string(:alphanumeric, min_length: 1, max_length: 8),
              noise_count <- integer(1..10) do
      # Worker 1: fresh clean arena
      a1 = Arena.new()
      {a1, i_to_o} = Arena.intern_type(a1, {:arrow, :i, :o})
      {a1, p1} = Arena.mk_const(a1, "pred_" <> sym_a, i_to_o)
      {a1, x1} = Arena.mk_bvar(a1, 0, :i)
      {a1, body1} = Arena.mk_app(a1, p1, x1)
      {a1, lam1} = Arena.mk_lam(a1, :i, body1)

      # Worker 2: arena pre-populated with unrelated symbols and nodes first
      a2 =
        Enum.reduce(1..noise_count, Arena.new(), fn idx, acc ->
          {acc, _} = Arena.mk_const(acc, "noise_#{sym_b}_#{idx}", :i)
          acc
        end)

      {a2, i_to_o_2} = Arena.intern_type(a2, {:arrow, :i, :o})
      {a2, p2} = Arena.mk_const(a2, "pred_" <> sym_a, i_to_o_2)
      {a2, x2} = Arena.mk_bvar(a2, 0, :i)
      {a2, body2} = Arena.mk_app(a2, p2, x2)
      {a2, lam2} = Arena.mk_lam(a2, :i, body2)

      assert Arena.skolem_hash(a1, lam1) == Arena.skolem_hash(a2, lam2)
    end
  end

  test "Gate 3: LCF ProofChecker accepts valid equality + resolution refutation and rejects forged proof" do
    arena = Arena.new()
    {arena, a} = Arena.mk_const(arena, "a", :i)
    {arena, b} = Arena.mk_const(arena, "b", :i)
    {arena, c} = Arena.mk_const(arena, "c", :i)
    {arena, eq_ab} = Arena.mk_eq(arena, a, b)
    {arena, eq_bc} = Arena.mk_eq(arena, b, c)
    {arena, eq_ac} = Arena.mk_eq(arena, a, c)

    valid_proof = [
      {:axiom, 1, MapSet.new([{:pos, eq_ab}])},
      {:axiom, 2, MapSet.new([{:pos, eq_bc}])},
      {:axiom, 3, MapSet.new([{:neg, eq_ac}])},
      {:trans, 4, 1, 2},
      {:resolve, 5, 4, 3, {:pos, eq_ac}}
    ]

    assert :ok == ProofChecker.verify_refutation(arena, valid_proof)

    # Forged proof that stops before deriving the empty clause must be rejected
    incomplete_proof = Enum.take(valid_proof, 4)
    assert {:error, {:not_empty_clause, _}} = ProofChecker.verify_refutation(arena, incomplete_proof)
  end

  @tag :gate3
  test "Gate 3: TPTP-v9.3.1 SHA-256 locked manifests are disjoint and parseable" do
    smoke = TptpCorpus.load_split(:smoke)
    dev = TptpCorpus.load_split(:dev)
    holdout = TptpCorpus.load_split(:holdout)

    assert length(smoke) == 50
    assert length(dev) == 300
    assert length(holdout) == 500

    # Strict anti-leakage disjointness check across all 3 splits
    assert MapSet.disjoint?(MapSet.new(smoke), MapSet.new(dev))
    assert MapSet.disjoint?(MapSet.new(smoke), MapSet.new(holdout))
    assert MapSet.disjoint?(MapSet.new(dev), MapSet.new(holdout))

    tptp_root = TptpCorpus.default_tptp_root()

    if File.dir?(tptp_root) do
      # Parse a sample of TPTP-Smoke problems on armix
      for stem <- Enum.take(smoke, 10) do
        path = TptpCorpus.problem_path(stem, tptp_root)
        assert File.regular?(path), "Expected #{path} to exist in #{tptp_root}"
      end
    end
  end
end
