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
    [
      {:tptp, "~> 0.3.0"},
      {:jason, "~> 1.4"},
      {:stream_data, "~> 1.1", only: [:dev, :test]},
      {:benchee, "~> 1.3", only: [:dev, :test]}
    ]
  end

  defp aliases do
    [
      "gate.1": ["test --only gate1"],
      "gate.3": ["test --only gate3"]
    ]
  end
end
