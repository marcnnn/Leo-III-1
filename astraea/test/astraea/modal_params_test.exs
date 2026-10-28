defmodule Astraea.ModalParamsTest do
  use ExUnit.Case, async: true

  alias Astraea.{ProofChecker, Prover, TptpLower}
  alias Astraea.Input.{Elaborator, Modal}

  # Leo-III's `--embedding-param` values for the modal embedding.

  defp spec(system, domains \\ "$constant") do
    "thf(s, logic, $modal == [$domains == #{domains}, $designation == $rigid, " <>
      "$terms == $local, $modalities == $modal_system_#{system}])."
  end

  # The embedded statements, as `TptpLower.lower_unit/2` computes them.
  defp embed(src, params \\ []) do
    {:ok, unit, _} =
      Tptp.Unit.from_string(src, resolver: {Tptp.Resolver.Fs, root: "."}, max_concurrency: 1)

    {stmts, ctx} =
      unit |> Tptp.Unit.statements() |> Enum.map(&elem(&1, 1)) |> Elaborator.elaborate()

    {[{:logic, spec}], stmts} = Enum.split_with(stmts, &match?({:logic, _}, &1))
    {:ok, params} = Modal.parse_params(params)
    {stmts, _} = Modal.embed(stmts, Modal.parse_spec(spec), ctx.next_id, params)
    stmts
  end

  defp extra(src, params) do
    for {:formula, "$$modal_" <> _ = n, "axiom", [], ir} <- embed(src, params),
        into: %{},
        do: {n, ir}
  end

  defp names(src, params \\ []), do: src |> extra(params) |> Map.keys() |> Enum.sort()

  defp assert_proved(src, params, opts \\ []) do
    opts = Keyword.merge([timeout_ms: 5_000, embedding_params: params], opts)
    assert {:proved, steps, stats} = Prover.prove_string(src, opts)
    assert :ok == ProofChecker.verify_refutation(stats.arena, steps)
  end

  @f "thf(f, type, f: $i > $o)."
  @barcan "thf(c, conjecture, (![X: $i]: [.] (f @ X)) => ([.] ![X: $i]: (f @ X)))."
  @cbf "thf(c, conjecture, ([.] ![X: $i]: (f @ X)) => (![X: $i]: [.] (f @ X)))."

  describe "parameter names" do
    test "Leo-III's names are accepted as strings or atoms in any case" do
      assert {:ok, [:modalities_syntactical, :silent]} =
               Modal.parse_params(["MODALITIES_SYNTACTICAL", :silent, "Silent"])

      assert length(Modal.param_names()) == 10
      assert {:ok, _} = Modal.parse_params(Modal.param_names())
    end

    test "unknown names are rejected" do
      assert {:error, {:unknown_embedding_param, "FOO"}} =
               Modal.parse_params(["SILENT", "FOO"])

      assert {:error, {:unknown_embedding_param, "FOO"}} =
               TptpLower.from_string("thf(c, conjecture, $true).", embedding_params: ["FOO"])
    end
  end

  describe "embedding" do
    test "defaults and no-op parameters reproduce the plain embedding" do
      src = spec("S5", "$cumulative") <> @f <> @cbf
      plain = embed(src)

      assert plain == embed(src, [])

      for p <- ~w(MONOMORPHIC POLYMORPHIC MODALITIES_SEMANTICAL DOMAINS_SEMANTICAL
                  FORCE_HIGHERORDER SILENT NO_UNIVERSAL_S5) do
        assert embed(src, [p]) == plain, p
      end

      assert names(src) == [
               "$$modal_domain_$i_cumulative",
               "$$modal_domain_$i_nonempty",
               "$$modal_frame_five",
               "$$modal_frame_t"
             ]
    end

    test "MODALITIES_SYNTACTICAL replaces frame conditions by axiom schemas" do
      src = spec("S4") <> "thf(c, conjecture, $true)."
      axioms = extra(src, ["MODALITIES_SYNTACTICAL"])
      assert Map.keys(axioms) |> Enum.sort() == ["$$modal_schema_four", "$$modal_schema_t"]

      # ![Phi: $$mworld > $o, W: $$mworld]: (![V]: (W R V => Phi @ V)) => Phi @ W
      assert {:quant, :all, p, {:fun, {:base, "$$mworld"}, {:base, "$o"}},
              {:quant, :all, w, {:base, "$$mworld"},
               {:bin, :imp, {:quant, :all, _, _, {:bin, :imp, _, _}},
                {:app, {:var, p, _}, {:var, w, _}}}}} = axioms["$$modal_schema_t"]

      # Semantical stays the default even when named explicitly.
      assert names(src, ["MODALITIES_SEMANTICAL"]) == ["$$modal_frame_four", "$$modal_frame_t"]

      # Syntactical takes precedence, as in Leo-III.
      assert names(src, ["MODALITIES_SEMANTICAL", "MODALITIES_SYNTACTICAL"]) ==
               ["$$modal_schema_four", "$$modal_schema_t"]
    end

    test "every frame condition has a schema, indexed modalities included" do
      src =
        "thf(s, logic, $modal == [$domains == $constant, $designation == $rigid, " <>
          "$terms == $local, $modalities == [$modal_axiom_B, $modal_axiom_D, " <>
          "$modal_axiom_5, $modal_axiom_CD, $modal_axiom_C4]])." <>
          "thf(c, conjecture, {$box(#a)} @ $true)."

      assert names(src, ["MODALITIES_SYNTACTICAL"]) ==
               Enum.sort(
                 for(c <- ~w(b d five cd c4), ix <- ["", "#a"], do: "$$modal_schema_#{c}#{ix}")
               )
    end

    test "S5U becomes an equivalence relation under NO_UNIVERSAL_S5 and syntactical modalities" do
      src = spec("S5U") <> "thf(c, conjecture, $true)."
      assert names(src) == ["$$modal_frame_universal"]
      assert names(src, ["NO_UNIVERSAL_S5"]) == ["$$modal_frame_five", "$$modal_frame_t"]

      assert names(src, ["MODALITIES_SYNTACTICAL"]) ==
               ["$$modal_schema_five", "$$modal_schema_t"]
    end

    test "DOMAINS_SYNTACTICAL uses the (converse) Barcan formula" do
      cumulative = spec("K", "$cumulative") <> @f <> @cbf
      decreasing = spec("K", "$decreasing") <> @f <> @cbf
      varying = spec("K", "$varying") <> @f <> @cbf

      assert names(cumulative, ["DOMAINS_SYNTACTICAL"]) ==
               ["$$modal_domain_$i_cbf", "$$modal_domain_$i_nonempty"]

      assert names(decreasing, ["DOMAINS_SYNTACTICAL"]) ==
               ["$$modal_domain_$i_bf", "$$modal_domain_$i_nonempty"]

      assert names(varying, ["DOMAINS_SYNTACTICAL"]) == names(varying)

      # ![P: $i > $$mworld > $o, W]: ([] ![X]: (exists X => P X)) => ![Y]: (exists Y => [] P Y)
      assert {:quant, :all, _, {:fun, {:base, "$i"}, {:fun, {:base, "$$mworld"}, {:base, "$o"}}},
              {:quant, :all, _, {:base, "$$mworld"},
               {:bin, :imp, {:quant, :all, _, {:base, "$$mworld"}, _},
                {:quant, :all, _, {:base, "$i"}, {:bin, :imp, _, _}}}}} =
               extra(cumulative, ["DOMAINS_SYNTACTICAL"])["$$modal_domain_$i_cbf"]
    end

    test "ALLOW_EMPTY_DOMAINS drops the non-emptiness axioms" do
      src = spec("K", "$cumulative") <> @f <> @cbf
      assert names(src, ["ALLOW_EMPTY_DOMAINS"]) == ["$$modal_domain_$i_cumulative"]

      assert names(src, ["ALLOW_EMPTY_DOMAINS", "DOMAINS_SYNTACTICAL"]) ==
               ["$$modal_domain_$i_cbf"]
    end
  end

  describe "proofs under the syntactical variants" do
    # Schemas with a flexible head make search harder than frame conditions (T
    # together with 4 or 5 times out), so each theorem uses a small system.
    test "T, 4, B and D theorems follow from the schemas" do
      params = ["MODALITIES_SYNTACTICAL"]
      p = "thf(p, type, p: $o)."
      assert_proved(spec("T") <> "thf(c, conjecture, ![A: $o]: (([.] A) => A)).", params)
      assert_proved(spec("K4") <> p <> "thf(c, conjecture, ([.] p) => ([.] [.] p)).", params)
      assert_proved(spec("B") <> p <> "thf(c, conjecture, p => ([.] <.> p)).", params)
      assert_proved(spec("D") <> p <> "thf(c, conjecture, ([.] p) => (<.> p)).", params)
    end

    test "a local T instance follows from the global schema" do
      src =
        spec("T") <>
          "thf(p, type, p: $o). thf(h, hypothesis, [.] p). thf(c, conjecture, p)."

      assert_proved(src, ["MODALITIES_SYNTACTICAL"])
    end

    test "S5U theorems that hold on equivalence frames are still proved" do
      assert_proved(
        spec("S5U") <> "thf(c, conjecture, ![A: $o]: (([.] A) => A)).",
        ["MODALITIES_SYNTACTICAL"]
      )

      assert_proved(
        spec("S5U") <> "thf(c, conjecture, ![A: $o]: ((<.> A) => ([.] <.> A))).",
        ["NO_UNIVERSAL_S5"]
      )
    end

    test "the Barcan formulas follow under syntactical domains" do
      # About 4 s on an M-series core, more on slower machines.
      params = ["DOMAINS_SYNTACTICAL"]
      assert_proved(spec("K", "$decreasing") <> @f <> @barcan, params, timeout_ms: 20_000)
      assert_proved(spec("K", "$cumulative") <> @f <> @cbf, params, timeout_ms: 20_000)
    end

    test "both syntactical variants together" do
      src =
        spec("T", "$cumulative") <>
          @f <> "thf(c, conjecture, ([.] ![X: $i]: (f @ X)) => ![X: $i]: (f @ X))."

      assert_proved(src, ["MODALITIES_SYNTACTICAL", "DOMAINS_SYNTACTICAL", "ALLOW_EMPTY_DOMAINS"])
    end
  end
end
