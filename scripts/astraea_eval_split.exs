# Usage: mix run ../scripts/astraea_eval_split.exs smoke|dev|extended [concurrency] [--competitive] [--width N] [--csv PATH]
alias Astraea.{Portfolio, TptpCorpus}
args = System.argv()
split = String.to_existing_atom(Enum.at(args, 0, "smoke"))
conc = case Enum.at(args, 1) do
  nil -> 3
  s -> case Integer.parse(s) do
    {n, _} -> n
    :error -> 3
  end
end
competitive? = Enum.any?(args, &(&1 in ["--competitive", "competitive"]))
# `--width N` races `Portfolio.wide_strategies(N)` instead of the four defaults.
width = case Enum.find_index(args, &(&1 == "--width")) do
  nil -> nil
  i -> args |> Enum.at(i + 1) |> String.to_integer()
end
csv = case Enum.find_index(args, &(&1 == "--csv")) do
  nil -> nil
  i -> Enum.at(args, i + 1)
end
root = TptpCorpus.default_tptp_root()
entries = TptpCorpus.load_split_entries(split)
total = length(entries)
counter = :atomics.new(1, [])

results =
  entries
  |> Task.async_stream(fn e ->
    opts = [tptp_root: root, timeout_ms: 2_500, competitive: competitive?]
    opts = if width, do: Keyword.put(opts, :strategies, Portfolio.wide_strategies(width)), else: opts
    t0 = System.monotonic_time(:millisecond)
    res = Portfolio.prove_file(Path.join(root, e.rel_path), opts)
    ms = System.monotonic_time(:millisecond) - t0
    idx = :atomics.add_get(counter, 1, 1)
    if rem(idx, 25) == 0 or idx == total do
      status_tag = if is_tuple(res), do: elem(res, 0), else: res
      IO.puts("Progress: #{idx}/#{total} (last: #{e.problem} -> #{status_tag})")
    end
    {e, res, ms}
  end, max_concurrency: conc, timeout: 35_000, on_timeout: :kill_task)
  |> Enum.zip(entries)
  |> Enum.map(fn {{:ok, {e, r, ms}}, _} -> {e, r, ms}; {{:exit, _}, e} -> {e, :timeout, 35_000} end)

if csv do
  rows = for {e, r, ms} <- results do
    {tag, stats} = case r do
      {t, _steps, s} when is_map(s) -> {t, s}
      {t, s} when is_map(s) -> {t, s}
      {t, _} -> {t, %{}}
      t -> {t, %{}}
    end
    Enum.join([e.problem, e.status, tag, stats |> Map.get(:winning_strategy) |> inspect() |> String.replace(",", ";"), ms], ",")
  end
  File.write!(csv, "problem,status,result,winner,ms\n" <> Enum.join(rows, "\n") <> "\n")
end

results = Enum.map(results, fn {e, r, _ms} -> {e, r} end)

thm = ["Theorem", "ContradictoryAxioms"]
csa = ["CounterSatisfiable", "Satisfiable"]
proved_lcf = for {e, {:proved, _, _}} <- results, do: e
proved_ext = for {e, {:proved_external, _}} <- results, do: e
proved_all = proved_lcf ++ proved_ext

lower_err = for {e, {:error, r}} <- results, not match?({:lcf_verification_failed, _, _}, r), do: {e.problem, r |> inspect() |> String.slice(0, 60)}

IO.puts("#{split} (competitive=#{competitive?}): total=#{length(entries)} thm=#{Enum.count(entries, &(&1.status in thm))} theorem_status=#{Enum.count(entries, &(&1.status == "Theorem"))}")
IO.puts("solved(Theorem LCF)=#{Enum.count(proved_lcf, &(&1.status == "Theorem"))} solved(THM+CA LCF)=#{Enum.count(proved_lcf, &(&1.status in thm))}")
if competitive? do
  IO.puts("solved(Theorem Total)=#{Enum.count(proved_all, &(&1.status == "Theorem"))} solved(THM+CA Total)=#{Enum.count(proved_all, &(&1.status in thm))}")
end
IO.puts("false proofs=#{inspect(for e <- proved_all, e.status in csa, do: e.problem)}")
IO.puts("lcf failures=#{inspect(for {e, {:error, {:lcf_verification_failed, _, _}}} <- results, do: e.problem)}")
IO.puts("errors=#{length(lower_err)} #{inspect(lower_err |> Enum.group_by(&elem(&1, 1)) |> Enum.map(fn {k, v} -> {k, length(v)} end))}")
for flag <- [:has_th1, :has_arith, :has_choice, :has_modal] do
  sub = Enum.filter(entries, &Map.get(&1, flag))
  IO.puts("  #{flag}: #{Enum.count(proved_lcf, &Map.get(&1, flag))}/#{Enum.count(sub, &(&1.status in thm))}")
end
