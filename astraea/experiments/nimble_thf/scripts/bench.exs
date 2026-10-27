root = System.get_env("TPTP_SUBSET", "/tmp/tptp_np/TPTP")

sources =
  (Path.wildcard(Path.join(root, "Problems/*/*.p")) ++
     Path.wildcard(Path.join(root, "Axioms/**/*.ax")))
  |> Enum.map(&{Path.relative_to(&1, root), File.read!(&1)})
  |> Enum.sort_by(fn {_, s} -> byte_size(s) end)

bytes = sources |> Enum.map(fn {_, s} -> byte_size(s) end) |> Enum.sum()
statements = Enum.sum(for {_, s} <- sources, {:ok, l} = NimbleThf.Parser.parse(s), do: length(l))

parsers = %{
  "Tptp (lexer + splitter + yecc)" => fn s -> {:ok, _, []} = Tptp.from_string(s) end,
  "NimbleThf (NimbleParsec)" => fn s -> {:ok, _} = NimbleThf.Parser.parse(s) end
}

IO.puts(
  "Corpus: #{length(sources)} files, #{Float.round(bytes / 1_000_000, 1)} MB, #{statements} statements\n"
)

IO.puts("Whole corpus, one process, best of 3:")

for {name, parse} <- Enum.sort(parsers) do
  best =
    for _ <- 1..3, reduce: :infinity do
      best ->
        :erlang.garbage_collect()
        {us, _} = :timer.tc(fn -> Enum.each(sources, fn {_, s} -> parse.(s) end) end)
        min(best, us)
    end

  IO.puts(
    "  #{String.pad_trailing(name, 32)} #{Float.round(best / 1_000_000, 2)} s  " <>
      "#{Float.round(bytes / best, 1)} MB/s  #{round(statements / (best / 1_000_000))} stmts/s"
  )
end

pick = fn q -> Enum.at(sources, round(q * (length(sources) - 1))) end

inputs =
  for q <- [0.1, 0.5, 1.0],
      {name, src} = pick.(q),
      into: %{},
      do: {"#{name} (#{div(byte_size(src), 1024)} KiB)", src}

IO.puts("\nResult size (words, :erts_debug.size) on the median file:")
{_, median} = pick.(0.5)
{:ok, file, []} = Tptp.from_string(median)
{:ok, ast} = NimbleThf.Parser.parse(median)

IO.puts(
  "  Tptp.File statements: #{:erts_debug.size(file.statements)}   NimbleThf AST: #{:erts_debug.size(ast)}"
)

if System.get_env("BENCHEE") do
  Benchee.run(
    Map.new(parsers, fn {name, parse} -> {name, fn s -> parse.(s) end} end),
    inputs: inputs,
    time: 3,
    warmup: 1,
    memory_time: 1,
    print: [configuration: false]
  )
end
