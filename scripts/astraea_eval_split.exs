# Usage: mix run eval.exs smoke|dev|extended [concurrency]
alias Astraea.{Portfolio, TptpCorpus}
args = System.argv()
split = String.to_existing_atom(Enum.at(args, 0, "smoke"))
conc = case Enum.at(args, 1) do
  nil -> 3
  s -> String.to_integer(s)
end
root = TptpCorpus.default_tptp_root()
entries = TptpCorpus.load_split_entries(split)
results =
  entries
  |> Task.async_stream(fn e ->
    {e, Portfolio.prove_file(Path.join(root, e.rel_path), tptp_root: root, timeout_ms: 2_500)}
  end, max_concurrency: conc, timeout: 30_000, on_timeout: :kill_task)
  |> Enum.zip(entries)
  |> Enum.map(fn {{:ok, r}, _} -> r; {{:exit, _}, e} -> {e, :timeout} end)
thm = ["Theorem", "ContradictoryAxioms"]
csa = ["CounterSatisfiable", "Satisfiable"]
proved = for {e, {:proved, _, _}} <- results, do: e
lower_err = for {e, {:error, r}} <- results, not match?({:lcf_verification_failed, _, _}, r), do: {e.problem, r |> inspect() |> String.slice(0, 60)}
IO.puts("#{split}: total=#{length(entries)} thm=#{Enum.count(entries, &(&1.status in thm))} theorem_status=#{Enum.count(entries, &(&1.status == "Theorem"))}")
IO.puts("solved(Theorem)=#{Enum.count(proved, &(&1.status == "Theorem"))} solved(THM+CA)=#{Enum.count(proved, &(&1.status in thm))}")
IO.puts("false proofs=#{inspect(for e <- proved, e.status in csa, do: e.problem)}")
IO.puts("lcf failures=#{inspect(for {e, {:error, {:lcf_verification_failed, _, _}}} <- results, do: e.problem)}")
IO.puts("errors=#{length(lower_err)} #{inspect(lower_err |> Enum.group_by(&elem(&1, 1)) |> Enum.map(fn {k, v} -> {k, length(v)} end))}")
for flag <- [:has_th1, :has_arith, :has_choice, :has_modal] do
  sub = Enum.filter(entries, &Map.get(&1, flag))
  IO.puts("  #{flag}: #{Enum.count(proved, &Map.get(&1, flag))}/#{Enum.count(sub, &(&1.status in thm))}")
end
