#!/usr/bin/env bash
# ============================================================================
# Astraea / Leo-III CASC LTB Overnight Benchmark Launcher for ARM Evaluation Server (armix)
# ============================================================================
# Runs the CASC-J11 Large Theory Batch (Isabelle Van Emde Boas Trees) benchmark
# in background under nohup or tmux with resilient state checkpointing.
#
# Usage:
#   ./scripts/run_overnight_casc_ltb.sh [options]
#
# Examples:
#   # Run all 356 THF VBT problems overnight with 30s timeout and external prover race:
#   ./scripts/run_overnight_casc_ltb.sh --timeout 30 --competitive
#
#   # Run pure internal LCF-verified mode:
#   ./scripts/run_overnight_casc_ltb.sh --timeout 30
# ============================================================================

set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
ROOT_DIR="$(dirname "$SCRIPT_DIR")"
ASTRAEA_DIR="$ROOT_DIR/astraea"
RESULTS_DIR="$ROOT_DIR/benchmarks/results"

mkdir -p "$RESULTS_DIR"

# Set up paths for armix
export TPTP="${TPTP:-$HOME/.local/share/tptp/TPTP-v9.3.1}"
export PATH="$HOME/.asdf/shims:$HOME/.asdf/bin:$HOME/.local/bin:$HOME/tools/oss-cad-suite/bin:$PATH"

LOG_FILE="$RESULTS_DIR/casc_ltb_overnight.log"
PID_FILE="$RESULTS_DIR/casc_ltb_overnight.pid"

echo "=============================================================================="
echo "          LAUNCHING CASC LTB OVERNIGHT BENCHMARK (armix)"
echo "=============================================================================="
echo "  Root Directory  : $ROOT_DIR"
echo "  TPTP Directory  : $TPTP"
echo "  Log File        : $LOG_FILE"
echo "  PID File        : $PID_FILE"
echo "  Arguments       : $@"
echo "=============================================================================="

cd "$ASTRAEA_DIR"

# Run in background via nohup
nohup mix run ../scripts/run_ltb_benchmark.exs "$@" > "$LOG_FILE" 2>&1 &
RUN_PID=$!
echo "$RUN_PID" > "$PID_FILE"

echo ""
echo "[SUCCESS] Benchmark successfully launched in background (PID: $RUN_PID)"
echo ""
echo "To monitor live progress, run:"
echo "  tail -f $LOG_FILE"
echo ""
echo "To check process status:"
echo "  ps -p $RUN_PID"
echo ""
echo "To inspect live CSV progress:"
echo "  tail -n 15 $RESULTS_DIR/ltb_report_*.csv"
echo "=============================================================================="
