#!/usr/bin/env python3
"""Runs an overnight comparative benchmark across CASC-J13 THF problems on armix.

Evaluates:
  1. Astraea (LCF-verified higher-order micro-prover)
  2. Leo-III 1.8.1 (standard baseline, with E-prover backend)
  3. ShotTx (multi-agent blackboard tableau prover for STT)

Problems are executed sequentially to avoid CPU cache and memory interference.
Real-time progress is streamed to CSV.
"""

import argparse
import csv
import json
import math
import os
import re
import signal
import subprocess
import sys
import threading
import time
from datetime import datetime
from pathlib import Path

REPO = Path(__file__).resolve().parent.parent
MANIFEST = REPO / "benchmarks" / "manifests" / "casc_j13_manifest.txt"
RESULTS_DIR = REPO / "benchmarks" / "results"

STATUS_RE = re.compile(r"^% SZS status (\w+)", re.M)

FIELDS = [
    "problem", "division", "prover", "timeout_s", "szs_status", "solved",
    "wall_s", "timestamp", "detail"
]


def run_cmd_with_timeout(cmd, cwd, env, timeout_s):
    t0 = time.monotonic()
    proc = subprocess.Popen(
        cmd,
        cwd=str(cwd),
        env=env,
        stdout=subprocess.PIPE,
        stderr=subprocess.STDOUT,
        start_new_session=True,
    )
    killed = threading.Event()

    def kill_proc():
        killed.set()
        try:
            os.killpg(proc.pid, signal.SIGKILL)
        except (ProcessLookupError, PermissionError):
            pass

    timer = threading.Timer(timeout_s + 2.0, kill_proc)
    timer.start()
    try:
        out_bytes, _ = proc.communicate(timeout=timeout_s + 4.0)
        out = out_bytes.decode("utf-8", "replace")
    except subprocess.TimeoutExpired:
        kill_proc()
        out = ""
    finally:
        timer.cancel()
        kill_proc()

    wall_s = time.monotonic() - t0
    m = STATUS_RE.search(out)
    if m:
        status = m.group(1)
    elif killed.is_set():
        status = "Timeout"
    else:
        status = "GaveUp"

    solved = 1 if status in ("Theorem", "Unsatisfiable") else 0
    return {
        "status": status,
        "solved": solved,
        "wall_s": round(wall_s, 3),
        "out_snippet": out[:300].replace("\n", " ").strip()
    }


def main():
    parser = argparse.ArgumentParser(description="Run CASC-J13 comparison benchmark")
    parser.add_argument("--timeout", type=float, default=30.0, help="Per-problem timeout in seconds (default: 30.0)")
    parser.add_argument("--limit", type=int, default=None, help="Limit number of problems to test (default: all 400)")
    parser.add_argument("--provers", nargs="+", default=["astraea", "leo3", "shottx"], help="Provers to run")
    parser.add_argument("--out", type=str, default=None, help="Output CSV path")
    args = parser.parse_args()

    tptp_root = os.environ.get("TPTP", os.path.expanduser("~/.local/share/tptp/TPTP-v9.3.1"))
    if not os.path.isdir(tptp_root):
        sys.exit(f"TPTP root directory not found at {tptp_root}")

    home = Path.home()
    env = dict(
        os.environ,
        TPTP=tptp_root,
        PATH=f"{home}/.asdf/shims:{home}/.cargo/bin:{home}/tools/jdk/bin:{home}/tools/leo3/bin:{home}/tools/eprover-ho/bin:{home}/tools/eprover/bin:{os.environ.get('PATH', '')}",
        ELIXIR_ERL_OPTIONS="+fnu",
        LC_ALL="en_US.UTF-8",
        LANG="en_US.UTF-8"
    )

    RESULTS_DIR.mkdir(parents=True, exist_ok=True)
    stamp = datetime.now().strftime("%Y%m%d_%H%M%S")
    out_csv = Path(args.out) if args.out else (RESULTS_DIR / f"casc_j13_comparison_{int(args.timeout)}s_{stamp}.csv")
    out_json = out_csv.with_suffix(".json")

    problems = [l.strip() for l in MANIFEST.read_text().splitlines() if l.strip()]
    if args.limit:
        problems = problems[:args.limit]

    print(f"=== Starting CASC-J13 Comparative Benchmark ===")
    print(f"Problems: {len(problems)} (TNE: 100, TEQ: 300)")
    print(f"Timeout per problem: {args.timeout}s")
    print(f"Provers: {args.provers}")
    print(f"Output: {out_csv}")
    print("-" * 60)

    results = []
    with open(out_csv, "w", newline="", buffering=1) as f:
        writer = csv.DictWriter(f, fieldnames=FIELDS)
        writer.writeheader()

        for idx, prob in enumerate(problems, 1):
            dom = prob[:3]
            prob_path = Path(tptp_root) / "Problems" / dom / f"{prob}.p"
            division = "TNE" if idx <= 100 else "TEQ"

            if not prob_path.exists():
                print(f"[{idx}/{len(problems)}] {prob} NOT FOUND at {prob_path}, skipping")
                continue

            print(f"[{idx}/{len(problems)}] ({division}) {prob}:")

            for prover in args.provers:
                if prover == "astraea":
                    cmd = [
                        "mix", "run", "-e",
                        f'Astraea.CLI.main(["{prob_path}", "-t", "{int(math.ceil(args.timeout))}"])'
                    ]
                    cwd = REPO / "astraea"
                elif prover == "leo3":
                    cmd = [
                        "leo3", str(prob_path),
                        "-t", str(max(1, int(math.ceil(args.timeout)))),
                        "-p"
                    ]
                    cwd = REPO
                elif prover == "shottx":
                    cmd = [
                        str(home / "ShotTx" / "shot_tx"),
                        "--szs",
                        "-t", str(int(args.timeout * 1000)),
                        str(prob_path)
                    ]
                    cwd = home / "ShotTx"
                else:
                    continue

                res = run_cmd_with_timeout(cmd, cwd, env, args.timeout)
                row = {
                    "problem": prob,
                    "division": division,
                    "prover": prover,
                    "timeout_s": args.timeout,
                    "szs_status": res["status"],
                    "solved": res["solved"],
                    "wall_s": res["wall_s"],
                    "timestamp": datetime.now().isoformat(),
                    "detail": res["out_snippet"]
                }
                writer.writerow(row)
                results.append(row)

                mark = "✓ SOLVED" if res["solved"] else f"✗ {res['status']}"
                print(f"    {prover:<8}: {mark:<12} ({res['wall_s']}s)")

    # Summarize
    summary = {}
    for prover in args.provers:
        p_res = [r for r in results if r["prover"] == prover]
        tne_solved = sum(r["solved"] for r in p_res if r["division"] == "TNE")
        teq_solved = sum(r["solved"] for r in p_res if r["division"] == "TEQ")
        tot_solved = sum(r["solved"] for r in p_res)
        avg_time = sum(r["wall_s"] for r in p_res if r["solved"]) / max(1, tot_solved)
        summary[prover] = {
            "total_tested": len(p_res),
            "total_solved": tot_solved,
            "tne_solved": tne_solved,
            "teq_solved": teq_solved,
            "avg_solve_time_s": round(avg_time, 2)
        }

    with open(out_json, "w") as f:
        json.dump(summary, f, indent=2)

    print("\n=== FINAL BENCHMARK SUMMARY ===")
    for prover, stats in summary.items():
        print(f"{prover:<8}: Total={stats['total_solved']}/{stats['total_tested']} (TNE: {stats['tne_solved']}/100, TEQ: {stats['teq_solved']}/300) AvgSolveTime={stats['avg_solve_time_s']}s")


if __name__ == "__main__":
    main()
