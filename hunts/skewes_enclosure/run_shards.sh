#!/usr/bin/env bash
# Production driver for hunt #152: one worker runs its shards in order, skipping
# any shard whose JSON already exists (the checkpoint). Box gates: wait while the
# 1-minute load exceeds 64; stop if MemAvailable falls below 20 GiB.
# Usage: [PYTHON=..] [OMEGAS=omega_grid.json] [ZEROS_DIR=dir] run_shards.sh <outdir> <shard index> ...
# Shard k covers zero indices (k-1)*100000+1 .. k*100000.
set -u
out="$1"; shift
here="$(cd "$(dirname "$0")" && pwd)"
py="${PYTHON:-python3}"   # e.g. PYTHON=.venv/bin/python run_shards.sh ...
mkdir -p "$out"
for k in "$@"; do
  n0=$(( (k - 1) * 100000 + 1 ))
  f="$out/shard_$(printf %03d "$k").json"
  [ -s "$f" ] && continue
  while [ "$(cut -d' ' -f1 /proc/loadavg | cut -d. -f1)" -ge 64 ]; do sleep 30; done
  mem=$(awk '/MemAvailable/ {print $2}' /proc/meminfo)
  if [ "$mem" -lt $((20 * 1024 * 1024)) ]; then echo "MemAvailable low, stopping before shard $k"; exit 3; fi
  echo "$(date -Iseconds) start shard $k"
  nice -n 10 "$py" -u "$here/zero_layer.py" --n0 "$n0" --num 100000 --batch 5000 \
      --prec 64 --sample 50 --seed "$((152000 + k))" ${OMEGAS:+--omegas "$OMEGAS"} \
      ${ZEROS_DIR:+--zeros-out "$ZEROS_DIR/zeros_$(printf %03d "$k").txt.gz"} \
      --out "$f.tmp" > "$f.log" 2>&1 \
    && mv "$f.tmp" "$f" && echo "$(date -Iseconds) done shard $k" \
    || { echo "$(date -Iseconds) FAILED shard $k"; exit 1; }
done
