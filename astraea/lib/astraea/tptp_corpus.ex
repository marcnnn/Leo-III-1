defmodule Astraea.TptpCorpus do
  @moduledoc """
  Loads SHA-256 locked TPTP-v9.3.1 manifests and verifies corpus integrity and
  `{:tptp, "~> 0.3.0"}` parsing on `armix`.

  Splits:
    * `:smoke`, `:dev`, `:holdout` — strict THF0 (`manifest_lock.json`),
    * `:extended` — a development sample of the fragments beyond strict THF0 (TH1,
      arithmetic, choice, modal logic), drawn by `scripts/tptp_extended_split.py` and
      locked in `extended_manifest_lock.json`.
  """

  @repo_root Path.expand("../../..", __DIR__)
  @manifests_dir Path.join(@repo_root, "benchmarks/manifests")

  @type split :: :smoke | :dev | :holdout | :extended

  @spec default_tptp_root() :: String.t()
  def default_tptp_root do
    System.get_env("TPTP") ||
      Path.expand("~/.local/share/tptp/TPTP-v9.3.1")
  end

  @spec load_manifest_lock() :: map()
  def load_manifest_lock, do: read_json("manifest_lock.json")

  @spec load_extended_lock() :: map()
  def load_extended_lock, do: read_json("extended_manifest_lock.json")

  defp read_json(name) do
    @manifests_dir
    |> Path.join(name)
    |> File.read!()
    |> Jason.decode!()
  end

  @spec load_split(split()) :: [String.t()]
  def load_split(tier) when tier in [:smoke, :dev, :holdout] do
    load_locked("tptp_thf0_#{tier}.txt", load_manifest_lock(), Atom.to_string(tier))
  end

  def load_split(:extended) do
    load_locked("tptp_extended_dev.txt", load_extended_lock(), "extended")
  end

  defp load_locked(filename, lock, key) do
    raw = File.read!(Path.join(@manifests_dir, filename))

    actual_sha =
      :crypto.hash(:sha256, raw)
      |> Base.encode16(case: :lower)

    expected_sha = Map.fetch!(lock["sha256"], key)

    if actual_sha != expected_sha do
      raise "Manifest integrity violation for #{key}: expected #{expected_sha}, got #{actual_sha}"
    end

    String.split(raw, "\n", trim: true)
  end

  @flags ~w(strict_thf0 has_let_ite has_choice has_ext_types has_th1 has_arith has_modal)a

  @spec load_catalog_map() :: %{String.t() => map()}
  def load_catalog_map do
    @manifests_dir
    |> Path.join("thf_catalog.csv")
    |> File.read!()
    |> String.split(~r/\r?\n/, trim: true)
    |> Enum.drop(1)
    |> Map.new(fn line ->
      [problem, domain, spc, rel_path, status, rating, _includes, _axioms | flags] =
        String.split(line, ",")

      flags = Map.new(Enum.zip(@flags, flags), fn {k, v} -> {k, v == "True"} end)

      {problem,
       Map.merge(flags, %{
         problem: problem,
         domain: domain,
         spc: spc,
         rel_path: rel_path,
         status: status,
         rating: rating
       })}
    end)
  end

  @spec load_split_entries(split()) :: [map()]
  def load_split_entries(tier) when tier in [:smoke, :dev, :holdout, :extended] do
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
