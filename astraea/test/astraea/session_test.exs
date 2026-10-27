defmodule Astraea.SessionTest do
  use ExUnit.Case, async: true

  alias Astraea.Session
  alias Astraea.Session.{Interactive, Ltb}

  @theory_src """
  thf(i_type, type, i: $tType).
  thf(f_type, type, f: i > i > i).
  thf(e_type, type, e: i).
  thf(a_type, type, a: i).
  thf(b_type, type, b: i).

  % Left identity axiom
  thf(left_id, axiom, ! [X: i]: ( (f @ e @ X) = X )).

  % Associativity axiom
  thf(assoc, axiom, ! [X: i, Y: i, Z: i]: ( (f @ (f @ X @ Y) @ Z) = (f @ X @ (f @ Y @ Z)) )).
  """

  @goal1_src """
  thf(goal1, conjecture, (f @ e @ a) = a).
  """

  @goal2_src """
  thf(goal2, conjecture, (f @ (f @ e @ a) @ b) = (f @ a @ b)).
  """

  describe "Astraea.Session core GenServer" do
    test "initializes background theory and accumulates rewrite rules across goals" do
      {:ok, session} = Session.start_link()

      # 1. Initialize theory
      assert {:ok, init_info} = Session.init_theory(session, {:string, @theory_src})
      assert init_info.background_clauses >= 2
      assert init_info.demod_rules >= 1

      # 2. Prove Goal 1
      assert {:ok, res1} = Session.prove(session, {:string, @goal1_src}, timeout_ms: 2000)
      assert res1.szs == :theorem
      assert res1.proof_length > 0

      # 3. Prove Goal 2 with accumulated theory state
      assert {:ok, res2} = Session.prove(session, {:string, @goal2_src}, timeout_ms: 2000)
      assert res2.szs == :theorem

      # 4. Check session telemetry
      stats = Session.stats(session)
      assert stats.queries_attempted == 2
      assert stats.queries_proved == 2
      assert stats.solve_rate_pct == 100.0

      Session.stop(session)
    end
  end

  describe "Astraea.Session.Interactive JSON-RPC protocol" do
    test "processes init_theory and prove_goal JSON-RPC requests" do
      {:ok, session} = Session.start_link()

      # 1. init_theory
      init_req = Jason.encode!(%{
        "jsonrpc" => "2.0",
        "method" => "init_theory",
        "params" => %{"source" => @theory_src},
        "id" => 1
      })

      resp1 = Interactive.handle_message(session, init_req)
      assert {:ok, decoded1} = Jason.decode(resp1)
      assert decoded1["id"] == 1
      assert decoded1["result"]["status"] == "ok"
      assert decoded1["result"]["background_clauses"] >= 2

      # 2. prove_goal
      prove_req = Jason.encode!(%{
        "jsonrpc" => "2.0",
        "method" => "prove_goal",
        "params" => %{"source" => @goal1_src, "timeout_ms" => 2000},
        "id" => 2
      })

      resp2 = Interactive.handle_message(session, prove_req)
      assert {:ok, decoded2} = Jason.decode(resp2)
      assert decoded2["id"] == 2
      assert decoded2["result"]["szs"] == "Theorem"

      # 3. session_stats
      stats_req = Jason.encode!(%{
        "jsonrpc" => "2.0",
        "method" => "session_stats",
        "params" => %{},
        "id" => 3
      })

      resp3 = Interactive.handle_message(session, stats_req)
      assert {:ok, decoded3} = Jason.decode(resp3)
      assert decoded3["id"] == 3
      assert decoded3["result"]["queries_proved"] == 1

      Session.stop(session)
    end
  end

  describe "Astraea.Session.Ltb CASC batch protocol parser" do
    test "parses batch configuration, includes, and problem pairs" do
      spec_content = """
      division.category LTB.HOL_Isabelle
      % SZS start BatchConfiguration
      execution.order ordered
      output.required Proof
      limit.time.problem.wc 15
      limit.time.overall.wc 7200
      % SZS end BatchConfiguration
      % SZS start BatchIncludes
      include('Axioms/LCL013^0.ax').
      include('Axioms/LCL013^6.ax').
      % SZS end BatchIncludes
      % SZS start BatchProblems
      Problems/AGT/AGT037^2.p /tmp/out/AGT037^2.out
      Problems/AGT/AGT033^2.p /tmp/out/AGT033^2.out
      % SZS end BatchProblems
      """

      tmp_file = Path.join(System.tmp_dir!(), "test_batch_#{:rand.uniform(1_000_000)}.spec")
      File.write!(tmp_file, spec_content)

      assert {:ok, config} = Ltb.parse_spec(tmp_file)
      assert config.category == "LTB.HOL_Isabelle"
      assert config.order == :ordered
      assert config.timeout_problem == 15
      assert config.timeout_overall == 7200
      assert length(config.includes) == 2
      assert length(config.problems) == 2
      assert hd(config.problems) == {"Problems/AGT/AGT037^2.p", "/tmp/out/AGT037^2.out"}

      File.rm(tmp_file)
    end
  end
end
