defmodule Astraea.External.Provers do
  @moduledoc """
  Command-line specifications for the external TPTP provers known to Astraea.

  Ported from `leo.modules.external.TPTPProvers` in Leo-III. Clause sets are
  printed in the first format a prover lists: THF0 via
  `Astraea.External.ThfPrinter`, or first-order TFF0 via the applicative encoding
  of `Astraea.External.TffPrinter`.

  A spec is a map with:
    * `:name` - prover name used in results and portfolio telemetry
    * `:executables` - candidate executable names looked up on `$PATH`
    * `:formats` - accepted clause-set formats (`:thf`, `:tff`), preferred first
    * `:args` - `fn %{seconds: s, ms: ms}, problem_file -> [arg] end`, builds the
      call including the prover's own time limit (a second line of defense
      behind the MuonTrap timeout)

  Custom provers can be passed to `Astraea.External.run/3` as such a map.
  """

  @type limits :: %{seconds: pos_integer(), ms: pos_integer()}

  @type format :: :thf | :tff

  @type spec :: %{
          required(:name) => atom(),
          required(:executables) => [String.t()],
          required(:args) => (limits(), Path.t() -> [String.t()]),
          optional(:formats) => [format()]
        }

  @doc """
  Returns the names of all built-in prover specs.
  """
  @spec names() :: [atom()]
  def names,
    do: [
      :eprover_ho,
      :eprover,
      :vampire,
      :zipperposition,
      :cvc5,
      :iprover,
      :satallax,
      :leo3,
      :leo2
    ]

  @doc """
  Returns the built-in spec for `name`.
  """
  @spec spec(atom()) :: {:ok, spec()} | {:error, {:unknown_prover, atom()}}
  def spec(:eprover_ho) do
    # E built with `--enable-ho`; a plain `eprover` build rejects THF input.
    {:ok, %{e_spec() | name: :eprover_ho, executables: ["eprover-ho"], formats: [:thf, :tff]}}
  end

  def spec(:eprover), do: {:ok, e_spec()}

  def spec(:vampire) do
    {:ok,
     %{
       name: :vampire,
       executables: ["vampire"],
       formats: [:thf, :tff],
       args: fn %{seconds: s}, file ->
         ["--mode", "casc", "-t", "#{s}s", "--proof", "tptp", file]
       end
     }}
  end

  def spec(:zipperposition) do
    {:ok,
     %{
       name: :zipperposition,
       executables: ["zipperposition"],
       formats: [:thf, :tff],
       args: fn %{seconds: s}, file -> [file, "--timeout", "#{s}", "-o", "tptp"] end
     }}
  end

  def spec(:cvc5) do
    {:ok,
     %{
       name: :cvc5,
       executables: ["cvc5"],
       formats: [:thf, :tff],
       args: fn %{ms: ms}, file ->
         ["--lang=tptp", "--tlimit=#{ms}", "--dump-unsat-cores", file]
       end
     }}
  end

  def spec(:iprover) do
    {:ok,
     %{
       name: :iprover,
       executables: ["iproveropt", "iprover"],
       formats: [:tff],
       args: fn %{seconds: s}, file -> ["--time_out_real", "#{s}", file] end
     }}
  end

  def spec(:satallax) do
    {:ok,
     %{
       name: :satallax,
       executables: ["satallax"],
       formats: [:thf],
       args: fn %{seconds: s}, file -> ["-t", "#{s}", "-p", "tstp", file] end
     }}
  end

  def spec(:leo3) do
    {:ok,
     %{
       name: :leo3,
       executables: ["leo3"],
       formats: [:thf, :tff],
       args: fn %{seconds: s}, file -> [file, "-t", "#{s}", "-p"] end
     }}
  end

  def spec(:leo2) do
    {:ok,
     %{
       name: :leo2,
       executables: ["leo"],
       formats: [:thf],
       args: fn %{seconds: s}, file -> ["-t", "#{s}", file] end
     }}
  end

  def spec(name) when is_atom(name), do: {:error, {:unknown_prover, name}}

  @doc """
  Returns the clause-set format to use for `spec`: `:format` from `opts` if given,
  else the spec's preferred format (THF for specs without `:formats`).
  """
  @spec format(spec(), keyword()) :: format()
  def format(spec, opts \\ []) do
    Keyword.get_lazy(opts, :format, fn -> spec |> Map.get(:formats, [:thf]) |> hd() end)
  end

  defp e_spec do
    %{
      name: :eprover,
      executables: ["eprover"],
      formats: [:tff],
      args: fn %{seconds: s}, file ->
        ["--auto-schedule", "--cpu-limit=#{s}", "-s", "--proof-object", file]
      end
    }
  end

  @doc """
  Resolves the executable path for a spec. An explicit `:path` option wins over
  the `$PATH` lookup of `spec.executables`.
  """
  @spec find_executable(spec(), keyword()) ::
          {:ok, String.t()} | {:error, {:executable_not_found, atom(), [String.t()]}}
  def find_executable(spec, opts \\ []) do
    candidates =
      case Keyword.get(opts, :path) do
        nil -> spec.executables
        path -> [path]
      end

    candidates
    |> Enum.find_value(&executable_path/1)
    |> case do
      nil -> {:error, {:executable_not_found, spec.name, candidates}}
      path -> {:ok, path}
    end
  end

  @doc """
  Returns the built-in provers whose executables are installed.
  """
  @spec available() :: [atom()]
  def available do
    Enum.filter(names(), fn name ->
      {:ok, spec} = spec(name)
      match?({:ok, _}, find_executable(spec))
    end)
  end

  defp executable_path(candidate) do
    if String.contains?(candidate, "/") do
      if File.regular?(candidate), do: Path.expand(candidate)
    else
      System.find_executable(candidate)
    end
  end
end
