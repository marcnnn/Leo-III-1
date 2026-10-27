root = System.get_env("TPTP_SUBSET", "/tmp/tptp_np/TPTP")
files = Path.wildcard(Path.join(root, "Problems/*/*.p")) ++ Path.wildcard(Path.join(root, "Axioms/**/*.ax"))

results =
  files
  |> Task.async_stream(fn f -> {f, NimbleThf.Oracle.check(File.read!(f))} end,
    timeout: :infinity, ordered: false)
  |> Enum.map(fn {:ok, r} -> r end)

failures = Enum.reject(results, fn {_, r} -> r == :ok end)
IO.puts("#{length(files) - length(failures)}/#{length(files)} files agree with Tptp")

for {f, r} <- Enum.take(failures, 10) do
  IO.puts(Path.relative_to(f, root))
  IO.inspect(r, limit: 8, printable_limit: 300)
end
