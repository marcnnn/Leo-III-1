alias Astraea.{Portfolio, Schedule, Prover, TptpCorpus}

root = TptpCorpus.default_tptp_root()
problems = ["CAT038^2", "LCL735^5", "LCL736^5", "SYO295^5", "SYO530^1", "SYO537^1", "SYO539^1", "SYO540^1"]

IO.puts("Testing 8 choice gap problems on armix...")
for p <- problems do
  domain = String.slice(p, 0, 3)
  rel = Path.join(["Problems", domain, p <> ".p"])
  path = Path.join(root, rel)
  
  t0 = System.monotonic_time(:millisecond)
  res_port = Portfolio.prove_file(path, tptp_root: root, timeout_ms: 2_500)
  ms_port = System.monotonic_time(:millisecond) - t0

  tag_port =
    case res_port do
      {:proved, steps, _st} -> "PROVED(#{length(steps)} steps)"
      {:proved_external, st} -> "PROVED_EXT(#{st.winning_strategy})"
      {tag, _} -> to_string(tag)
      other -> inspect(other)
    end

  t1 = System.monotonic_time(:millisecond)
  res_sched = Schedule.prove_file(path, tptp_root: root, timeout_ms: 2_500)
  ms_sched = System.monotonic_time(:millisecond) - t1

  tag_sched =
    case res_sched do
      {:proved, steps, _st} -> "PROVED(#{length(steps)} steps)"
      {:proved_external, st} -> "PROVED_EXT(#{st.winning_strategy})"
      {tag, _} -> to_string(tag)
      other -> inspect(other)
    end

  IO.puts("  #{p}: Portfolio 2.5s -> #{tag_port} (#{ms_port}ms) | Schedule 2.5s -> #{tag_sched} (#{ms_sched}ms)")
end
