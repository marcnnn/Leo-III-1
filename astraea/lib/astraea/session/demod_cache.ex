defmodule Astraea.Session.DemodCache do
  @moduledoc """
  Maintains an indexed cache of KBO-oriented rewrite rules harvested from
  conjecture-free sub-proofs.

  To prevent clause swamping (the utility problem), equational lemmas are
  converted into directed rewrite rules in the Demodulator rather than
  arbitrary generating clauses in the given-clause queue.
  """

  alias Astraea.{Arena, Engine.Demodulator, Engine.HeadIndex, Session.Lineage}

  @type t :: %__MODULE__{
          rules: [map()],
          rule_index: HeadIndex.t(),
          thf_rules: [String.t()],
          count: non_neg_integer()
        }

  defstruct rules: [],
            rule_index: HeadIndex.new(),
            thf_rules: [],
            count: 0

  @doc """
  Creates a new empty demodulator rule cache.
  """
  @spec new() :: t()
  def new do
    %__MODULE__{}
  end

  @doc """
  Filters orientable unit equational lemmas from harvested lineage lemmas,
  constructs Demodulator rule records, and installs them into the `HeadIndex`.
  """
  @spec insert_lemmas(t(), Arena.t(), [Lineage.lemma()]) :: {t(), non_neg_integer()}
  def insert_lemmas(%__MODULE__{} = cache, %Arena{} = arena, lemmas) when is_list(lemmas) do
    new_rules =
      lemmas
      |> Enum.filter(&(&1.is_equality and not is_nil(&1.lhs) and not is_nil(&1.rhs)))
      |> Enum.flat_map(fn lem ->
        orient_equation(arena, lem)
      end)

    if new_rules == [] do
      {cache, 0}
    else
      valid_new_thf =
        new_rules
        |> Enum.map(& &1.thf)
        |> Enum.reject(&(&1 == "" or is_nil(&1)))

      updated_rules = cache.rules ++ new_rules
      updated_thf = cache.thf_rules ++ valid_new_thf
      updated_index = Demodulator.add_rules(cache.rule_index, arena, new_rules)

      new_cache = %__MODULE__{
        rules: updated_rules,
        rule_index: updated_index,
        thf_rules: Enum.uniq(updated_thf),
        count: length(updated_rules)
      }

      {new_cache, length(new_rules)}
    end
  end

  defp orient_equation(%Arena{} = arena, lem) do
    lhs = lem.lhs
    rhs = lem.rhs

    cond do
      var?(arena, lhs) and var?(arena, rhs) ->
        []

      true ->
        directions =
          case Arena.kbo_compare(arena, lhs, rhs) do
            :gt -> [{lhs, rhs}]
            :lt -> [{rhs, lhs}]
            :inc ->
              case {var?(arena, lhs), var?(arena, rhs)} do
                {false, false} -> [{lhs, rhs}, {rhs, lhs}]
                {false, true} -> [{lhs, rhs}]
                {true, false} -> [{rhs, lhs}]
                _ -> []
              end

            :eq ->
              []
          end

        for {l, r} <- directions, not var?(arena, l) do
          %{
            id: lem.id,
            eq: nil,
            lhs: l,
            rhs: r,
            kind: :eq,
            thf: lem.thf
          }
        end
    end
  end

  defp var?(arena, term_id) do
    case Arena.get_node(arena, term_id) do
      {3, _, _, _, _} -> true  # @tag_fvar
      {2, _, _, _, _} -> true  # @tag_bvar
      _ -> false
    end
  end
end
