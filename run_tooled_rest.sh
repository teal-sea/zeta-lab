#!/bin/bash
# Remaining tooled arms. Opus 5 completed 2026-08-20; Gemini was interrupted at
# 3 of 5 and is re-run whole rather than patched, so no arm is a partial average.
: "${OPENROUTER_API_KEY:?set OPENROUTER_API_KEY in your environment before running this}"
export INSPECT_LOG_DIR="$HOME/zeta-selfreport/logs-tooled"
export ZETA_LEAN_ROOT="$HOME/zeta-lab"
export PYTHONPATH="$HOME/zeta-selfreport/evals"
PY="$HOME/zeta-lab/.venv/bin/python"
for M in google/gemini-3.7-flash qwen/qwen3.7-flash; do
  echo "=================== TOOLED ARM: $M ==================="
  date "+start %H:%M:%S"
  "$PY" -m inspect_ai eval evals/self_report_tooled.py --model "openrouter/$M" \
        --max-connections 1 2>&1 | tail -18
  date "+end   %H:%M:%S"
done
echo "TOOLED ARMS DONE"
