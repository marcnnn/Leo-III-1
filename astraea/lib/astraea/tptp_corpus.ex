defmodule Astraea.TptpCorpus do
  @moduledoc """
  Loads SHA-256 locked TPTP-v9.3.1 THF0 manifests (`smoke`, `dev`, `holdout`)
  and verifies corpus integrity and `{:tptp, "~> 0.3.0"}` parsing on `armix`.
  """

  @repo_root Path.expand("../../..", __DIR__)
  @manifests_dir Path.join(@repo_root, "benchmarks/manifests")

  @spec default_tptp_root() :: String.t()
  def default_tptp_root do
    System.get_env("TPTP") ||
      Path.expand("~/.local/share/tptp/TPTP-v9.3.1")
  end

  @spec load_manifest_lock() :: map()
  def load_manifest_lock do
    @manifests_dir
    |> Path.join("manifest_lock.json")
    |> File.read!()
    |> Jason.decode!()
  end

  @spec load_split(:smoke | :dev | :holdout) :: [String.t()]
  def load_split(tier) when tier in [:smoke, :dev, :holdout] do
    lock = load_manifest_lock()
    filename = "tptp_thf0_#{tier}.txt"
    raw = File.read!(Path.join(@manifests_dir, filename))

    actual_sha =
      :crypto.hash(:sha256, raw)
      |> Base.encode16(case: :lower)

    expected_sha = Map.fetch!(lock["sha256"], Atom.to_string(tier))

    if actual_sha != expected_sha do
      raise "Manifest integrity violation for #{tier}: expected #{expected_sha}, got #{actual_sha}"
    end

    raw
    |> String.split("\n", trim: true)
  end

  @spec load_catalog_map() :: %{String.t() => map()}
  def load_catalog_map do
    @manifests_dir
    |> Path.join("thf_catalog.csv")
    |> File.read!()
    |> String.split(~r/\r?\n/, trim: true)
    |> Enum.drop(1)
    |> Map.new(fn line ->
      [problem, domain, spc, rel_path, status, rating | _rest] = String.split(line, ",")

      {problem,
       %{
         problem: problem,
         domain: domain,
         spc: spc,
         rel_path: rel_path,
         status: status,
         rating: rating
       }}
    end)
  end

  @spec load_split_entries(:smoke | :dev | :holdout) :: [map()]
  def load_split_entries(tier) when tier in [:smoke, :dev, :holdout] do
    cat = load_catalog_map()

    load_split(tier)
    |> Enum.map(&Map.fetch!(cat, &1))
  end

  @spec problem_path(String.t(), String.t()) :: String.t()
  def problem_path(problem_stem, tptp_root \\ default_tptp_root()) do
    domain = String.slice(problem_stem, 0, 3)
    Path.join([tptp_root, "Problems", domain, "#{problem_stem}.p"])
  end
end
