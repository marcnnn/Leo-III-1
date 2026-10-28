defmodule Astraea.External do
  @moduledoc """
  External TPTP prover integration (E, Vampire, Zipperposition, cvc5, Satallax,
  Leo-III, LEO-II) over OS processes supervised by `MuonTrap`.

  Each call runs the prover through `MuonTrap.cmd/3`, which owns the process via a
  port and a small C shim. When the calling Erlang process exits or is killed
  (e.g. by `Astraea.Portfolio` after a sibling strategy wins), the port closes and
  MuonTrap sends SIGTERM (then SIGKILL after `:delay_to_sigkill`) to its child.

  Without a cgroup MuonTrap only signals that direct child, so provers are started
  through `priv/process_group.sh`, which runs them in their own process group and
  kills the whole group. On Linux, `muontrap: [cgroup_base: ..., cgroup: %{...}]`
  additionally gives cgroup v2 containment and memory/CPU limits.

  Two input modes are supported:
    1. `prove_problem/3` - hands the original TPTP file to the prover (`include`s
       are resolved by the prover from `$TPTP`).
    2. `prove_clauses/4` / `prove_lowered/3` - hands Astraea's own clausified
       (SInE-filtered, Skolemized) clause set to the prover, as THF0
       (`Astraea.External.ThfPrinter`), as first-order TFF0
       (`Astraea.External.TffPrinter`) or as untyped FOF
       (`Astraea.External.FofPrinter`) depending on the prover and the
       `:encoding` option (see `Astraea.External.FolEncoding`).

  External answers are oracle results: they are not checked by
  `Astraea.ProofChecker`. `Astraea.External.Reconstruct` turns refutations into
  LCF-verified proofs by re-proving their unsat core; callers must keep answers
  that could not be reconstructed apart from verified proofs.
  """

  alias Astraea.{Arena, Clausifier, ProofChecker, TptpCorpus, TptpLower}
  alias Astraea.External.{FofPrinter, FolEncoding, Provers, SZS, TffPrinter, ThfPrinter}

  @default_timeout_ms 10_000
  @default_grace_ms 1_000

  defmodule Result do
    @moduledoc """
    Outcome of one external prover run.
    """

    defstruct prover: nil,
              status: :unknown,
              status_raw: nil,
              dataform: nil,
              proof: [],
              exit_status: nil,
              elapsed_ms: 0,
              output: nil

    @type t :: %__MODULE__{
            prover: atom(),
            status: Astraea.External.SZS.status(),
            status_raw: String.t() | nil,
            dataform: String.t() | nil,
            proof: [String.t()],
            exit_status: non_neg_integer() | :timeout | nil,
            elapsed_ms: non_neg_integer(),
            output: String.t() | nil
          }
  end

  @type prover :: atom() | Provers.spec()

  @doc """
  Runs `prover` on an existing TPTP problem file. Options:
    * `:timeout_ms` - prover time limit (default `#{@default_timeout_ms}`); passed to
      the prover's own limit and, plus `:grace_ms`, to `MuonTrap.cmd/3`
    * `:grace_ms` - extra wall-clock time before MuonTrap kills the prover
      (default `#{@default_grace_ms}`)
    * `:path` - explicit executable path (default: `$PATH` lookup)
    * `:extra_args` - appended to the prover's command line
    * `:cd`, `:env` - working directory and environment for the prover
    * `:muontrap` - extra `MuonTrap.cmd/3` options (e.g. `cgroup_base:`, `cgroup:`)
    * `:process_group` - run the prover via `priv/process_group.sh` so that its
      whole process tree is killed (default `true`)
    * `:keep_output` - keep the full stdout/stderr in the result (default `false`)
    * `:debug` - print the command line, exit status and output as `%` comments
      (Leo-III `--atpdebug`, default `false`)

  The same option list is shared with the clause-set entry points
  (`prove_clauses/4`, `prove_lowered/3`, `write_clause_problem/4`), which
  additionally read:
    * `:format` - `:thf`, `:tff` or `:fof` (default: the prover's preferred one)
    * `:encoding` - first-order encoding for `:tff` and `:fof`: a keyword list
      `[lambda: :lambda_lifting | :ski, arity: :applicative | :min_arity,
      booleans: :lift | :proxies, types: :mono_native | :mono_guards |
      :mono_guards_light]` or a preset `:default` / `:leo3` (see
      `Astraea.External.FolEncoding`). A guard `:types` value prints FOF even for
      TFF provers; `format: :fof` defaults `:types` to `:mono_guards_light`.
  """
  @spec run(prover(), Path.t(), keyword()) :: {:ok, Result.t()} | {:error, term()}
  def run(prover, problem_file, opts \\ []) do
    result = do_run(prover, problem_file, opts)
    if Keyword.get(opts, :debug, false), do: debug_result(prover, result)
    result
  end

  defp debug_result(prover, {:error, reason}),
    do: IO.puts("% [atpdebug] #{inspect(prover)}: #{inspect(reason)}")

  defp debug_result(_prover, {:ok, %Result{} = res}) do
    IO.puts(
      "% [atpdebug] #{res.prover}: exit #{inspect(res.exit_status)}, #{res.elapsed_ms} ms, " <>
        "SZS #{res.status_raw || "none"}"
    )
  end

  defp do_run(prover, problem_file, opts) do
    with {:ok, spec} <- resolve_spec(prover),
         {:ok, exe} <- Provers.find_executable(spec, opts) do
      timeout_ms = Keyword.get(opts, :timeout_ms, @default_timeout_ms)
      grace_ms = Keyword.get(opts, :grace_ms, @default_grace_ms)
      limits = %{seconds: max(1, div(timeout_ms + 999, 1000)), ms: timeout_ms}
      args = spec.args.(limits, problem_file) ++ Keyword.get(opts, :extra_args, [])

      cmd_opts =
        [stderr_to_stdout: true, timeout: timeout_ms + grace_ms]
        |> put_if(:cd, Keyword.get(opts, :cd))
        |> put_if(:env, Keyword.get(opts, :env))
        |> Keyword.merge(Keyword.get(opts, :muontrap, []))

      t0 = System.monotonic_time(:millisecond)

      {cmd, args} =
        if Keyword.get(opts, :process_group, true),
          do: {"/bin/sh", [process_group_wrapper(), exe | args]},
          else: {exe, args}

      if Keyword.get(opts, :debug, false),
        do: IO.puts("% [atpdebug] #{Enum.join([cmd | args], " ")}")

      {output, exit_status} = MuonTrap.cmd(cmd, args, cmd_opts)

      if Keyword.get(opts, :debug, false) do
        for line <- String.split(output, "\n", trim: true),
            do: IO.puts("% [atpdebug] | " <> line)
      end

      elapsed_ms = System.monotonic_time(:millisecond) - t0
      parsed = SZS.parse(output)

      {:ok,
       %Result{
         prover: spec.name,
         status: status(parsed.status, exit_status),
         status_raw: parsed.status_raw,
         dataform: parsed.dataform,
         proof: parsed.proof,
         exit_status: exit_status,
         elapsed_ms: elapsed_ms,
         output: if(Keyword.get(opts, :keep_output, false), do: output)
       }}
    end
  end

  @doc """
  Runs `prover` on the original TPTP problem at `path`. `include` directives are
  resolved by the prover, so `$TPTP` and the working directory are set to
  `:tptp_root` (default `Astraea.TptpCorpus.default_tptp_root/0`).
  """
  @spec prove_problem(prover(), Path.t(), keyword()) :: {:ok, Result.t()} | {:error, term()}
  def prove_problem(prover, path, opts \\ []) do
    tptp_root = Path.expand(Keyword.get(opts, :tptp_root, TptpCorpus.default_tptp_root()))

    opts =
      opts
      |> Keyword.put_new(:env, [{"TPTP", tptp_root}])
      |> Keyword.put_new_lazy(:cd, fn -> if File.dir?(tptp_root), do: tptp_root end)

    run(prover, Path.expand(path), opts)
  end

  @doc """
  Prints `clauses` into a temporary file under `:tmp_dir` (default
  `System.tmp_dir!/0`) and runs `prover` on it. The format is `:format` or the
  prover's preferred one (see `Astraea.External.Provers.format/2`). The file is
  removed afterwards; callers that may be killed mid-run should pass a `:tmp_dir`
  they clean up themselves.

  Clause `i` of `clauses` is named `c<i>`, which `Astraea.External.Reconstruct`
  relies on to map proof cores back to clauses; this holds for every
  `:encoding`. An invalid `:encoding` yields `{:error, {:invalid_encoding, msg}}`.
  """
  @spec prove_clauses(prover(), Arena.t(), [ProofChecker.clause()], keyword()) ::
          {:ok, Result.t()} | {:error, term()}
  def prove_clauses(prover, %Arena{} = arena, clauses, opts \\ []) do
    with {:ok, spec} <- resolve_spec(prover),
         {:ok, file} <- write_clause_problem(spec, arena, clauses, opts) do
      try do
        run(spec, file, opts)
      after
        File.rm(file)
      end
    end
  end

  @doc """
  Writes `clauses` as a problem file for `prover` (see `prove_clauses/4`) and
  returns its path. The caller owns the file.
  """
  @spec write_clause_problem(prover(), Arena.t(), [ProofChecker.clause()], keyword()) ::
          {:ok, Path.t()} | {:error, term()}
  def write_clause_problem(prover, %Arena{} = arena, clauses, opts \\ []) do
    with {:ok, spec} <- resolve_spec(prover),
         {:ok, source} <- clause_problem(spec, arena, clauses, opts) do
      tmp_dir = Keyword.get_lazy(opts, :tmp_dir, &System.tmp_dir!/0)
      file = Path.join(tmp_dir, "astraea_#{spec.name}_#{System.unique_integer([:positive])}.p")
      File.write!(file, source)
      {:ok, file}
    end
  end

  @doc """
  Renders `clauses` as the problem text that `write_clause_problem/4` writes for
  `prover`, honouring `:format` and `:encoding`.
  """
  @spec clause_problem(prover(), Arena.t(), [ProofChecker.clause()], keyword()) ::
          {:ok, String.t()} | {:error, term()}
  def clause_problem(prover, %Arena{} = arena, clauses, opts \\ []) do
    requested = Keyword.get(opts, :encoding)

    with {:ok, spec} <- resolve_spec(prover),
         {:ok, encoding} <- FolEncoding.normalize(requested) do
      case Provers.format(spec, opts) do
        :thf ->
          {:ok, ThfPrinter.problem(arena, clauses)}

        :fof ->
          {:ok, FofPrinter.problem(arena, clauses, encoding: FofPrinter.encoding(requested))}

        :tff ->
          if encoding[:types] == :mono_native,
            do: {:ok, TffPrinter.problem(arena, clauses, encoding: encoding)},
            else: {:ok, FofPrinter.problem(arena, clauses, encoding: encoding)}
      end
    end
  end

  @doc """
  Clausifies a lowered problem (honouring `:sine_limit` and `:inline_bridges`) and
  runs `prover` on the resulting clause set via `prove_clauses/4`.

  Note that a `Satisfiable` answer only refers to the SInE-filtered clause set and
  says nothing about the original problem.
  """
  @spec prove_lowered(prover(), TptpLower.t(), keyword()) :: {:ok, Result.t()} | {:error, term()}
  def prove_lowered(prover, %TptpLower{} = lowered, opts \\ []) do
    {arena, clauses} =
      Clausifier.clausify(lowered,
        sine_limit: Keyword.get(opts, :sine_limit, 55),
        inline_bridges: Keyword.get(opts, :inline_bridges, false)
      )

    prove_clauses(prover, arena, clauses, opts)
  end

  defp process_group_wrapper, do: Application.app_dir(:astraea, "priv/process_group.sh")

  defp resolve_spec(name) when is_atom(name), do: Provers.spec(name)
  defp resolve_spec(%{name: _, executables: _, args: _} = spec), do: {:ok, spec}
  defp resolve_spec(other), do: {:error, {:invalid_prover_spec, other}}

  defp status(:unknown, :timeout), do: :timeout
  defp status(:unknown, code) when is_integer(code) and code != 0, do: :error
  defp status(szs_status, _exit_status), do: szs_status

  defp put_if(opts, _key, nil), do: opts
  defp put_if(opts, key, value), do: Keyword.put(opts, key, value)
end
