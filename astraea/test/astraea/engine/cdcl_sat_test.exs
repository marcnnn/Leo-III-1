defmodule Astraea.Engine.CdclSatTest do
  use ExUnit.Case, async: true
  alias Astraea.Engine.CdclSat

  describe "basic solving" do
    test "solves empty formula as SAT" do
      solver = CdclSat.new()
      assert {:sat, _model, _} = CdclSat.solve(solver)
    end

    test "solves simple SAT clause" do
      {:ok, solver} =
        CdclSat.new()
        |> CdclSat.add_clause([1, 2])

      assert {:sat, model, _} = CdclSat.solve(solver)
      assert model[1] or model[2]
    end

    test "solves single unit clause" do
      {:ok, solver} =
        CdclSat.new()
        |> CdclSat.add_clause([1])

      assert {:sat, model, _} = CdclSat.solve(solver)
      assert model[1] == true
    end

    test "solves negative unit clause" do
      {:ok, solver} =
        CdclSat.new()
        |> CdclSat.add_clause([-1])

      assert {:sat, model, _} = CdclSat.solve(solver)
      assert model[1] == false
    end

    test "detects immediate UNSAT on contradicting unit clauses" do
      {:ok, solver} =
        CdclSat.new()
        |> CdclSat.add_clause([1])

      assert {:unsat, _} = CdclSat.add_clause(solver, [-1])
    end

    test "detects UNSAT on 2-variable contradictory set" do
      # (x1 or x2) and (-x1 or x2) and (x1 or -x2) and (-x1 or -x2) -> UNSAT
      solver = CdclSat.new()
      {:ok, solver} = CdclSat.add_clause(solver, [1, 2])
      {:ok, solver} = CdclSat.add_clause(solver, [-1, 2])
      {:ok, solver} = CdclSat.add_clause(solver, [1, -2])
      {:ok, solver} = CdclSat.add_clause(solver, [-1, -2])

      assert {:unsat, _} = CdclSat.solve(solver)
    end

    test "detects UNSAT on Pigeonhole Principle PHP(3 pigeons into 2 holes)" do
      # Pigeons: 1, 2, 3. Holes: A, B.
      # Vars: p1A=1, p1B=2, p2A=3, p2B=4, p3A=5, p3B=6.
      # Each pigeon in at least one hole:
      # [1, 2], [3, 4], [5, 6]
      # No two pigeons in hole A: [-1, -3], [-1, -5], [-3, -5]
      # No two pigeons in hole B: [-2, -4], [-2, -6], [-4, -6]
      solver = CdclSat.new()
      {:ok, solver} = CdclSat.add_clause(solver, [1, 2])
      {:ok, solver} = CdclSat.add_clause(solver, [3, 4])
      {:ok, solver} = CdclSat.add_clause(solver, [5, 6])
      {:ok, solver} = CdclSat.add_clause(solver, [-1, -3])
      {:ok, solver} = CdclSat.add_clause(solver, [-1, -5])
      {:ok, solver} = CdclSat.add_clause(solver, [-3, -5])
      {:ok, solver} = CdclSat.add_clause(solver, [-2, -4])
      {:ok, solver} = CdclSat.add_clause(solver, [-2, -6])
      {:ok, solver} = CdclSat.add_clause(solver, [-4, -6])

      assert {:unsat, _} = CdclSat.solve(solver)
    end

    test "handles tautological clauses cleanly" do
      # (x1 or -x1) is a tautology, should be dropped
      {:ok, solver} =
        CdclSat.new()
        |> CdclSat.add_clause([1, -1])

      assert {:sat, _, _} = CdclSat.solve(solver)
    end
  end

  describe "incremental assumption solving" do
    test "solves under satisfying assumptions" do
      solver = CdclSat.new()
      {:ok, solver} = CdclSat.add_clause(solver, [1, 2])
      {:ok, solver} = CdclSat.add_clause(solver, [-1, 3])

      assert {:sat, model, _} = CdclSat.solve_under_assumptions(solver, [1])
      assert model[1] == true
      assert model[3] == true
    end

    test "detects UNSAT under contradictory assumptions and extracts core" do
      solver = CdclSat.new()
      # (x1 or x2) and (-x1 or -x2)
      {:ok, solver} = CdclSat.add_clause(solver, [1, 2])
      {:ok, solver} = CdclSat.add_clause(solver, [-1, -2])

      # Formula is SAT globally (e.g. x1=true, x2=false)
      assert {:sat, _, solver} = CdclSat.solve(solver)

      # Under assumptions x1=true, x2=true -> UNSAT
      assert {:unsat, core, solver} = CdclSat.solve_under_assumptions(solver, [1, 2])
      assert 1 in core or 2 in core

      # Solver can still solve under other assumptions without corruption
      assert {:sat, model, _} = CdclSat.solve_under_assumptions(solver, [1, -2])
      assert model[1] == true
      assert model[2] == false
    end

    test "solves 3-variable chain problem under assumptions" do
      # x1 -> x2 -> x3 -> x4
      solver = CdclSat.new()
      {:ok, solver} = CdclSat.add_clause(solver, [-1, 2])
      {:ok, solver} = CdclSat.add_clause(solver, [-2, 3])
      {:ok, solver} = CdclSat.add_clause(solver, [-3, 4])

      # Under assumption x1=true and x4=false -> UNSAT
      assert {:unsat, core, solver} = CdclSat.solve_under_assumptions(solver, [1, -4])
      assert 1 in core or -4 in core

      # Under assumption x1=true -> SAT with x2=x3=x4=true
      assert {:sat, model, _} = CdclSat.solve_under_assumptions(solver, [1])
      assert model[1] == true and model[2] == true and model[3] == true and model[4] == true
    end

    test "incremental learning: learns conflict and stays valid when adding new clauses" do
      solver = CdclSat.new()
      {:ok, solver} = CdclSat.add_clause(solver, [1, 2])

      # Check SAT with assumption 1
      assert {:sat, _, solver} = CdclSat.solve_under_assumptions(solver, [1])

      # Add clause [-1]
      {:ok, solver} = CdclSat.add_clause(solver, [-1])

      # Now assumption 1 must fail
      assert {:unsat, _core, solver} = CdclSat.solve_under_assumptions(solver, [1])

      # But assumption 2 must succeed (1 is forced false, so 2 must be true)
      assert {:sat, model, _} = CdclSat.solve_under_assumptions(solver, [2])
      assert model[1] == false
      assert model[2] == true
    end
  end
end
