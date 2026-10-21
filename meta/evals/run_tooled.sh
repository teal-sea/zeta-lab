#!/bin/bash
: "${OPENROUTER_API_KEY:?set OPENROUTER_API_KEY in your environment before running this}"
export INSPECT_LOG_DIR="$HOME/zeta-selfreport/logs-tooled"
export ZETA_LEAN_ROOT="$HOME/zeta-lab"
export PYTHONPATH="$HOME/zeta-selfreport/evals"
PY="$HOME/zeta-lab/.venv/bin/python"
for M in anthropic/claude-opus-5 google/gemini-3.7-flash qwen/qwen3.7-flash; do
  echo "=================== TOOLED ARM: $M ==================="
  date "+start %H:%M:%S"
  "$PY" -m inspect_ai eval evals/self_report_tooled.py --model "openrouter/$M" \
        --max-connections 1 2>&1 | tail -20
  date "+end   %H:%M:%S"
done
echo "TOOLED ARMS DONE"
