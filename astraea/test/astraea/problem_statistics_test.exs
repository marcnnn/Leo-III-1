defmodule Astraea.ProblemStatisticsTest do
  use ExUnit.Case, async: true

  alias Astraea.{ProblemStatistics, TptpLower}

  @src """
  thf(p_type, type, p: $i > $o).
  thf(h_type, type, h: ($i > $o) > $o).
  thf(a_type, type, a: $i).
  thf(ax1, axiom, p @ a).
  thf(hyp, hypothesis, ! [X: $i]: (p @ X)).
  thf(ax2, axiom, h @ (^ [X: $i]: ((p @ X) = (p @ a)))).
  thf(c, conjecture, ? [X: $i]: (p @ X)).
  """

  setup do
    root = Path.join(System.tmp_dir!(), "astraea_stats_#{System.unique_integer([:positive])}")
    File.mkdir_p!(Path.join(root, "Axioms"))

    File.write!(Path.join(root, "Axioms/TST001+0.ax"), """
    fof(inc1, axiom, q(b)).
    fof(inc2, axiom, ! [X]: (q(X) => r(X))).
    fof(inc3, lemma, r(b)).
    """)

    on_exit(fn -> File.rm_rf(root) end)
    {:ok, root: root}
  end

  test "counts the lowered problem" do
    {:ok, lowered} = TptpLower.from_string(@src)
    stats = ProblemStatistics.from_lowered(lowered)

    assert stats.assumptions == 3
    assert stats.conjectures == 1
    assert stats.roles == %{"axiom" => 2, "hypothesis" => 1, "conjecture" => 1}
    assert stats.symbols == 3
    assert stats.base_types == 0
    assert stats.max_order == 2
    assert stats.higher_order
    assert stats.lambdas == 1
    assert stats.equations == 1
    assert stats.quantifiers == 2
    assert stats.size > 0 and stats.max_depth > 0
  end

  test "Leo-III's parse-time counts separate local and included formulas", %{root: root} do
    src = """
    include('Axioms/TST001+0.ax').
    fof(local, axiom, q(c)).
    fof(goal, conjecture, r(c)).
    """

    {:ok, stats} = ProblemStatistics.from_string(src, tptp_root: root)

    assert stats.includes == 1
    assert stats.immediate_formulas == 2
    assert stats.included_formulas == 3
    assert ProblemStatistics.formulas(stats) == 5
    assert stats.local_axioms == 1
    assert stats.included_axioms == 2
    assert ProblemStatistics.axioms(stats) == 3
    assert stats.assumptions == 4
    refute stats.higher_order
    assert stats.fragments == [:fof]

    comment = ProblemStatistics.to_comment(stats)
    assert comment =~ "% formulas: 5\n"
    assert comment =~ "% included_axioms: 2\n"
  end

  test "reports parse errors" do
    assert {:error, {:parse, [_ | _]}} = ProblemStatistics.from_string("fof(broken, axiom, ).")
  end
end
