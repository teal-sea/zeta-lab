#!/bin/bash
# RECORD, NOT A RUNNER. The script as executed on 2026-08-20, kept so the runs
# reported in meta/SELF-REPORT-PROTOCOL.md section 11 can be audited. It ran on
# the operator's Mac from a separate checkout at ~/zeta-selfreport, with the
# eval modules then at evals/ (now meta/evals/), and it ran lake in
# ZETA_LEAN_ROOT=~/zeta-lab, the operator's main checkout. CLAUDE.md's compute
# rules now keep Lean builds off the operator's machines, so this copy refuses
# to start. A re-run is a new, pre-registered round on GitHub Actions or a
# larger remote machine, invoking
#   inspect eval meta/evals/self_report.py (or self_report_tooled.py)
# with ZETA_LEAN_ROOT naming a checkout that has a built Mathlib and that
# nobody else is working in.
echo "$0 is the record of the 2026-08-20 run; see its header" >&2
exit 1
# ---- as run on 2026-08-20 ----
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
