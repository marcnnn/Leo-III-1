#!/usr/bin/env bash
# Astraea on TPTP-Smoke and TPTP-Dev for the Leo-III comparison: all
# `mix external.eval` configurations at 2.5 s, and the baseline at 10 s,
# 2 problems in parallel. Writes benchmarks/results/astraea_<split>_<ms>ms.{csv,json}.
#   scripts/leo3_astraea_eval.sh
set -euo pipefail
cd "$(dirname "$0")/.."
RESULTS=$PWD/benchmarks/results
export PATH=$HOME/.asdf/shims:$HOME/.cargo/bin:$HOME/tools/eprover-ho/bin:$HOME/tools/eprover/bin:$HOME/tools/vampire/bin:$HOME/tools/cvc5/bin:$HOME/tools/leo3/bin:$PATH
export TPTP=${TPTP:-$HOME/.local/share/tptp/TPTP-v9.3.1}
mkdir -p "$RESULTS"
cd astraea

run() {
  local split=$1 ms=$2 configs=$3
  mix external.eval --split "$split" --timeout "$ms" --concurrency 2 --configs "$configs" \
    --out "$RESULTS/astraea_${split}_${ms}ms.json" --csv "$RESULTS/astraea_${split}_${ms}ms.csv"
}

for split in smoke dev; do
  run "$split" 2500 baseline,racers,cooperate,leo3_racer,leo3
done
for split in smoke dev; do
  run "$split" 10000 baseline
done
