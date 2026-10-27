#!/usr/bin/env bash
# Leo-III baseline on TPTP-Smoke and TPTP-Dev: stock and with E, at 2.5 s and 10 s
# wall clock per problem, 4 problems in parallel. CSVs go to benchmarks/results/,
# raw Leo-III output (SZS status and TSTP proofs) to $RAW (default ~/leo3_runs).
#   scripts/leo3_baseline.sh
set -euo pipefail
cd "$(dirname "$0")/.."
export TPTP=${TPTP:-$HOME/.local/share/tptp/TPTP-v9.3.1}
RAW=${RAW:-$HOME/leo3_runs}
CONC=${CONC:-4}

for t in 2.5 10; do
  for split in smoke dev; do
    for cfg in stock e; do
      python3 -I scripts/leo3_run.py --split "$split" --timeout "$t" --config "$cfg" \
        --concurrency "$CONC" --out "benchmarks/results/leo3_${split}_${cfg}_${t}s.csv" \
        --proofs "$RAW/${split}_${cfg}_${t}"
    done
  done
done
