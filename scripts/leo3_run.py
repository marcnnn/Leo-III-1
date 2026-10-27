#!/usr/bin/env python3
"""Runs Leo-III on a TPTP split and writes one CSV row per problem.

    scripts/leo3_run.py --split smoke --timeout 2.5 --config stock \
        --out benchmarks/results/leo3_smoke_stock_2.5s.csv --proofs /tmp/leo3_proofs

Each problem gets a hard wall-clock budget of --timeout seconds, measured from
process start, so JVM startup counts against it. Leo-III's own -t takes whole
seconds; it is set to ceil(timeout) and the process group is killed at the
budget. A problem counts as solved when the SZS status line was printed before
the kill. CPU time (user + sys of Leo-III and its children, e.g. E) comes from
wait4().

Configs: `stock` (no external provers) and `e` (--atp e=<eprover>).
Only the smoke and dev splits are accepted; holdout is a blind benchmark.
"""

import argparse
import csv
import math
import os
import re
import signal
import subprocess
import sys
import threading
import time
from concurrent.futures import ThreadPoolExecutor
from pathlib import Path

HOME = Path.home()
REPO = Path(__file__).resolve().parent.parent
MANIFESTS = REPO / "benchmarks" / "manifests"
SPLITS = {"smoke": "tptp_thf0_smoke.txt", "dev": "tptp_thf0_dev.txt"}

STATUS_RE = re.compile(r"^% SZS status (\w+) for .*?(?:: (\d+) ms resp\. (\d+) ms w/o parsing)?$", re.M)
PROOF_START = "% SZS output start"
PROOF_END = "% SZS output end"

FIELDS = [
    "problem", "domain", "expected", "config", "timeout_s", "szs_status",
    "solved", "proof", "wall_s", "cpu_s", "leo_ms", "leo_ms_noparse", "killed",
]


def load_entries(split):
    names = [l.strip() for l in (MANIFESTS / SPLITS[split]).read_text().splitlines() if l.strip()]
    with open(MANIFESTS / "thf_catalog.csv", newline="") as f:
        catalog = {row["problem"]: row for row in csv.DictReader(f)}
    return [catalog[n] for n in names]


def run_one(entry, args, tptp, proof_dir):
    path = Path(tptp) / entry["rel_path"]
    cmd = [args.leo3, str(path), "-t", str(max(1, math.ceil(args.timeout))), "-p"]
    if args.config == "e":
        cmd += ["--atp", f"e={args.eprover}"]

    env = dict(os.environ, TPTP=tptp)
    t0 = time.monotonic()
    proc = subprocess.Popen(cmd, stdout=subprocess.PIPE, stderr=subprocess.STDOUT,
                            env=env, start_new_session=True)
    killed = threading.Event()

    def kill():
        killed.set()
        try:
            os.killpg(proc.pid, signal.SIGKILL)
        except ProcessLookupError:
            pass

    timer = threading.Timer(args.timeout, kill)
    timer.start()
    out = proc.stdout.read().decode("utf-8", "replace")
    _, _, rusage = os.wait4(proc.pid, 0)
    wall = time.monotonic() - t0
    timer.cancel()
    # Leo-III may leave external provers behind on normal exit as well.
    try:
        os.killpg(proc.pid, signal.SIGKILL)
    except ProcessLookupError:
        pass

    m = STATUS_RE.search(out)
    status = m.group(1) if m else ("Killed" if killed.is_set() else "NoAnswer")
    has_proof = PROOF_START in out and PROOF_END in out
    solved = status in ("Theorem", "Unsatisfiable", "ContradictoryAxioms") and entry["status"] == "Theorem"

    if proof_dir:
        (proof_dir / f"{entry['problem']}.out").write_text(out)

    return {
        "problem": entry["problem"],
        "domain": entry["domain"],
        "expected": entry["status"],
        "config": args.config,
        "timeout_s": args.timeout,
        "szs_status": status,
        "solved": int(solved),
        "proof": int(has_proof),
        "wall_s": f"{wall:.3f}",
        "cpu_s": f"{rusage.ru_utime + rusage.ru_stime:.3f}",
        "leo_ms": m.group(2) if m and m.group(2) else "",
        "leo_ms_noparse": m.group(3) if m and m.group(3) else "",
        "killed": int(killed.is_set()),
    }


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--split", required=True, choices=sorted(SPLITS))
    ap.add_argument("--timeout", type=float, required=True, help="wall-clock seconds per problem")
    ap.add_argument("--config", default="stock", choices=["stock", "e"])
    ap.add_argument("--concurrency", type=int, default=4)
    ap.add_argument("--leo3", default=str(HOME / "tools/leo3/bin/leo3"))
    ap.add_argument("--eprover", default=str(HOME / "tools/eprover/bin/eprover"))
    ap.add_argument("--tptp", default=os.environ.get("TPTP", str(HOME / ".local/share/tptp/TPTP-v9.3.1")))
    ap.add_argument("--out", required=True)
    ap.add_argument("--proofs", help="directory for raw Leo-III output per problem")
    args = ap.parse_args()

    proof_dir = Path(args.proofs) if args.proofs else None
    if proof_dir:
        proof_dir.mkdir(parents=True, exist_ok=True)

    entries = load_entries(args.split)
    t0 = time.monotonic()
    with ThreadPoolExecutor(args.concurrency) as pool:
        rows = list(pool.map(lambda e: run_one(e, args, args.tptp, proof_dir), entries))

    Path(args.out).parent.mkdir(parents=True, exist_ok=True)
    with open(args.out, "w", newline="") as f:
        w = csv.DictWriter(f, fieldnames=FIELDS)
        w.writeheader()
        w.writerows(rows)

    thm = [r for r in rows if r["expected"] == "Theorem"]
    sat = [r for r in rows if r["expected"] in ("CounterSatisfiable", "Satisfiable")]
    false_thm = [r["problem"] for r in sat if r["szs_status"] in ("Theorem", "Unsatisfiable")]
    print(f"{args.split} {args.config} {args.timeout}s c={args.concurrency}: "
          f"solved {sum(r['solved'] for r in thm)}/{len(thm)} THM, "
          f"proofs {sum(r['proof'] for r in thm if r['solved'])}, "
          f"CSA answered {sum(r['szs_status'] in ('CounterSatisfiable', 'Satisfiable') for r in sat)}/{len(sat)}, "
          f"false THM on CSA {false_thm}, wall {time.monotonic() - t0:.0f}s", file=sys.stderr)


if __name__ == "__main__":
    main()
