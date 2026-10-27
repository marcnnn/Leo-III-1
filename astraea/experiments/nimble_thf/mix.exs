defmodule NimbleThf.MixProject do
  use Mix.Project

  def project do
    [
      app: :nimble_thf,
      version: "0.1.0",
      elixir: "~> 1.15",
      start_permanent: Mix.env() == :prod,
      deps: deps()
    ]
  end

  def application do
    [extra_applications: [:logger]]
  end

  defp deps do
    [
      {:nimble_parsec, "~> 1.4"},
      {:tptp, "~> 0.3.0"},
      {:benchee, "~> 1.3", only: :dev}
    ]
  end
end
