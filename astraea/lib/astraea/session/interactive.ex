defmodule Astraea.Session.Interactive do
  @moduledoc """
  Streaming JSON-RPC Protocol Engine for Interactive Proof Assistants.

  Provides a bi-directional streaming interface suited for Isabelle Sledgehammer,
  Lean 4 hammers, and continuous verification condition (VC) pipelines:
  - `init_theory`: Ingests and warms the shared background theory.
  - `prove_goal`: Asynchronously or synchronously refutes goals against the warm session.
  - `session_stats`: Inspects accumulated lemmas and throughput.
  """

  alias Astraea.Session

  @doc """
  Processes a single incoming JSON-RPC string message against an active `Astraea.Session`.
  Returns an outgoing JSON-RPC response string.
  """
  @spec handle_message(GenServer.server(), String.t()) :: String.t()
  def handle_message(session, json_str) do
    case Jason.decode(json_str) do
      {:ok, %{"jsonrpc" => "2.0", "method" => method} = req} ->
        id = Map.get(req, "id")
        params = Map.get(req, "params", %{})
        dispatch(session, method, params, id)

      {:ok, %{"method" => method} = req} ->
        id = Map.get(req, "id")
        params = Map.get(req, "params", %{})
        dispatch(session, method, params, id)

      {:error, reason} ->
        encode_error(nil, -32700, "Parse error: #{inspect(reason)}")

      _other ->
        encode_error(nil, -32600, "Invalid Request")
    end
  end

  @doc """
  Runs an interactive stdio loop, reading newline-delimited JSON-RPC requests
  from standard input and writing responses to standard output.
  """
  @spec run_stdio(GenServer.server()) :: :ok
  def run_stdio(session) do
    case IO.read(:stdio, :line) do
      :eof ->
        :ok

      {:error, _reason} ->
        :ok

      line when is_binary(line) ->
        trimmed = String.trim(line)

        if trimmed != "" do
          response = handle_message(session, trimmed)
          IO.puts(:stdio, response)
        end

        run_stdio(session)
    end
  end

  # ---------------------------------------------------------------------------
  # Method Dispatcher
  # ---------------------------------------------------------------------------

  defp dispatch(session, "init_theory", params, id) do
    spec =
      cond do
        is_list(params["files"]) ->
          {:files, params["files"]}

        is_binary(params["source"]) ->
          {:string, params["source"]}

        true ->
          nil
      end

    if is_nil(spec) do
      encode_error(id, -32602, "Invalid params: must provide 'files' list or 'source' string")
    else
      opts = build_opts(params)

      case Session.init_theory(session, spec, opts) do
        {:ok, res} ->
          encode_result(id, Map.put(res, :status, "ok"))

        {:error, reason} ->
          encode_error(id, -32000, "Init theory failed: #{inspect(reason)}")
      end
    end
  end

  defp dispatch(session, "prove_goal", params, id) do
    spec =
      cond do
        is_binary(params["conjecture"]) ->
          {:formula, params["conjecture"]}

        is_binary(params["source"]) ->
          {:string, params["source"]}

        is_binary(params["file"]) ->
          {:file, params["file"]}

        true ->
          nil
      end

    if is_nil(spec) do
      encode_error(id, -32602, "Invalid params: must provide 'conjecture', 'source', or 'file'")
    else
      opts = build_opts(params)

      case Session.prove(session, spec, opts) do
        {:ok, res} ->
          formatted = %{
            szs: format_szs(Map.get(res, :szs, :unknown)),
            duration_ms: res.duration_ms,
            proof_length: Map.get(res, :proof_length, 0),
            iterations: Map.get(res, :iterations, 0),
            harvested_rules: Map.get(res, :harvested_rules, 0)
          }

          encode_result(id, formatted)

        {:error, reason} ->
          encode_error(id, -32001, "Prove goal failed: #{inspect(reason)}")
      end
    end
  end

  defp dispatch(session, "session_stats", _params, id) do
    stats = Session.stats(session)
    encode_result(id, stats)
  end

  defp dispatch(_session, unknown_method, _params, id) do
    encode_error(id, -32601, "Method not found: #{unknown_method}")
  end

  # ---------------------------------------------------------------------------
  # Protocol Serialization
  # ---------------------------------------------------------------------------

  defp encode_result(id, result) do
    Jason.encode!(%{
      "jsonrpc" => "2.0",
      "id" => id,
      "result" => result
    })
  end

  defp encode_error(id, code, message) do
    Jason.encode!(%{
      "jsonrpc" => "2.0",
      "id" => id,
      "error" => %{
        "code" => code,
        "message" => message
      }
    })
  end

  defp build_opts(params) do
    []
    |> maybe_put(:timeout_ms, params["timeout_ms"])
    |> maybe_put(:tptp_root, params["tptp_root"])
  end

  defp maybe_put(opts, _key, nil), do: opts
  defp maybe_put(opts, key, val), do: Keyword.put(opts, key, val)

  defp format_szs(:theorem), do: "Theorem"
  defp format_szs(:unsatisfiable), do: "Unsatisfiable"
  defp format_szs(:counter_satisfiable), do: "CounterSatisfiable"
  defp format_szs(:timeout), do: "Timeout"
  defp format_szs(other) when is_atom(other), do: Atom.to_string(other)
  defp format_szs(other), do: inspect(other)
end
