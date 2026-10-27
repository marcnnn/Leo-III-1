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

  describe "Astraea.Session.Ltb CASC batch protocol parser and runner" do
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

    test "executes batch with checkpointing, result generation, and recovery" do
      tmp_dir = Path.join(System.tmp_dir!(), "ltb_test_#{:rand.uniform(1_000_000)}")
      File.mkdir_p!(tmp_dir)

      theory_file = Path.join(tmp_dir, "theory.ax")
      File.write!(theory_file, @theory_src)

      prob1 = Path.join(tmp_dir, "p1.p")
      File.write!(prob1, @goal1_src)

      prob2 = Path.join(tmp_dir, "p2.p")
      File.write!(prob2, @goal2_src)

      out1 = Path.join(tmp_dir, "p1.out")
      out2 = Path.join(tmp_dir, "p2.out")

      spec_content = """
      division.category LTB.Test
      % SZS start BatchConfiguration
      execution.order ordered
      output.required Proof
      limit.time.problem.wc 2
      limit.time.overall.wc 60
      % SZS end BatchConfiguration
      % SZS start BatchIncludes
      include('theory.ax').
      % SZS end BatchIncludes
      % SZS start BatchProblems
      #{prob1} #{out1}
      #{prob2} #{out2}
      % SZS end BatchProblems
      """

      spec_path = Path.join(tmp_dir, "batch.spec")
      File.write!(spec_path, spec_content)

      checkpoint_path = Path.join(tmp_dir, "checkpoint.json")

      # 1. Run batch
      assert {:ok, report} = Ltb.run_batch(spec_path, checkpoint_file: checkpoint_path, timeout_ms: 2000)
      assert report.total_problems == 2
      assert report.solved == 2
      assert report.solve_rate_pct == 100.0
      assert File.exists?(out1)
      assert File.exists?(out2)
      assert File.exists?(checkpoint_path)

      # Verify SZS status in output file
      assert File.read!(out1) =~ "% SZS status Theorem"

      # 2. Re-run batch with checkpoint (should use cached results)
      assert {:ok, report2} = Ltb.run_batch(spec_path, checkpoint_file: checkpoint_path, timeout_ms: 2000)
      assert report2.solved == 2

      File.rm_rf!(tmp_dir)
    end
  end
end
