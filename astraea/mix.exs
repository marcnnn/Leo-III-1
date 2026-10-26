defmodule Astraea.MixProject do
  use Mix.Project

  def project do
    [
      app: :astraea,
      version: "0.1.0",
      elixir: "~> 1.15",
      start_permanent: Mix.env() == :prod,
      deps: deps(),
      aliases: aliases()
    ]
  end

  def application do
    [
      extra_applications: [:logger, :crypto]
    ]
  end

  defp deps do
    base = [
      {:tptp, "~> 0.3.0"},
      {:rustler, "~> 0.36"},
      {:muontrap, "~> 2.0"},
      {:jason, "~> 1.4"},
      {:stream_data, "~> 1.1", only: [:dev, :test]},
      {:benchee, "~> 1.3"}
    ]

    nx_simd_path = Path.expand("../../../nx_simd", __DIR__)
    nx_fixed_path = Path.expand("../../../nx_fixed", __DIR__)

    if File.dir?(nx_simd_path) and File.dir?(nx_fixed_path) do
      base ++
        [
          {:nx_fixed, path: nx_fixed_path},
          {:nx_simd, path: nx_simd_path}
        ]
    else
      base
    end
  end

  defp aliases do
    [
      "gate.1": ["test --only gate1"],
      "gate.2": ["test --only gate2"],
      "gate.3": ["test --only gate3"],
      "gate.4": ["gate.four"]
    ]
  end
end
