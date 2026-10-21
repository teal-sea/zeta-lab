#!/bin/bash
# Frozen arms, per SELF-REPORT-PROTOCOL.md section 9. Sequential on purpose:
# the kernel build locks the Lean package, so arms never overlap.
: "${OPENROUTER_API_KEY:?set OPENROUTER_API_KEY in your environment before running this}"
export INSPECT_LOG_DIR="$HOME/zeta-selfreport/logs"
export ZETA_LEAN_ROOT="$HOME/zeta-lab"
PY="$HOME/zeta-lab/.venv/bin/python"
for M in anthropic/claude-opus-5 openai/gpt-5.4 google/gemini-3.7-flash deepseek/deepseek-v4-flash qwen/qwen3.7-flash; do
  echo "=================== ARM: $M ==================="
  date "+start %H:%M:%S"
  "$PY" -m inspect_ai eval evals/self_report.py --model "openrouter/$M" \
        --max-connections 1 --no-sandbox-cleanup 2>&1 | tail -25
  date "+end   %H:%M:%S"
done
echo "ALL ARMS DONE"
