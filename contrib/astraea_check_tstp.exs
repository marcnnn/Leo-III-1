# Usage (from astraea/): mix run ../contrib/astraea_check_tstp.exs proof.s ...
# Provers: $EPROVER_HO (default ~/tools/eprover-ho/bin/eprover-ho), $VAMPIRE (default ~/tools/vampire/bin/vampire).
# GDV-style semantic check of Astraea TSTP proofs: every `status(thm)` inference is
# re-proved from its parents by E (eprover-ho), falling back to Vampire.
alias Tptp.Printer.Canonical
eprover = System.get_env("EPROVER_HO", Path.expand("~/tools/eprover-ho/bin/eprover-ho"))
vampire = System.get_env("VAMPIRE", Path.expand("~/tools/vampire/bin/vampire"))

check = fn path ->
  {:ok, der, []} = Tptp.Derivation.from_string(File.read!(path))

  decls =
    for n <- der.order,
        node = der.nodes[n],
        Tptp.Node.value(node.statement.role) == "type",
        do: node.statement

  decl_src = Enum.map(decls, &[Canonical.to_iodata(&1), "\n"])

  steps =
    for name <- der.order,
        node = der.nodes[name],
        node.origin == :inference,
        [[step | _] | _] = node.steps,
        step.status == :theorem,
        do: {name, node, step}

  results =
    for {name, node, step} <- steps do
      parents =
        Enum.map(node.parents, fn p ->
          ["thf(p_", p, ", axiom, ", Canonical.to_iodata(der.nodes[p].statement.formula), ").\n"]
        end)

      problem = [
        decl_src,
        parents,
        "thf(goal, conjecture, ",
        Canonical.to_iodata(node.statement.formula),
        ").\n"
      ]

      file = Path.join(System.tmp_dir!(), "gdv_#{System.unique_integer([:positive])}.p")
      File.write!(file, problem)

      run = fn cmd, args ->
        {out, _} = System.cmd(cmd, args ++ [file], stderr_to_stdout: true)

        case Regex.run(~r/SZS status (\w+)/, out),
          do: (
            [_, s] -> s
            nil -> "none"
          )
      end

      status = run.(eprover, ["--auto", "-s", "--cpu-limit=10"])

      status =
        if status in ["Theorem", "Unsatisfiable", "ContradictoryAxioms"],
          do: status,
          else: run.(vampire, ["--mode", "casc", "-t", "10"])

      File.rm(file)
      {name, step.rule, status}
    end

  bad =
    Enum.reject(results, fn {_, _, s} ->
      s in ["Theorem", "Unsatisfiable", "ContradictoryAxioms"]
    end)

  IO.puts(
    "#{Path.basename(path)}: #{length(results) - length(bad)}/#{length(results)} thm steps verified #{inspect(bad)}"
  )

  bad == []
end

ok = System.argv() |> Enum.map(check) |> Enum.count(& &1)
IO.puts("#{ok}/#{length(System.argv())} proofs fully verified")
