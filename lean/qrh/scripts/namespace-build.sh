#!/usr/bin/env bash
# Run only on a remote Linux builder: a Namespace runner with /cache mounted
# persistently, or a Modal container (scripts/modal_build.py), never on the
# operator's Macs. QRH_CACHE names the working cache directory; on Namespace it
# must be the attached volume, on Modal it is the container's local disk and
# the launcher checkpoints it to a Modal volume during and after the run.
set -euo pipefail
task_runner=${QRH_RUNNER:-namespace}
task_cache=${QRH_CACHE:-/cache}
if [[ $(uname -s) != Linux || ( ${QRH_NAMESPACE_RUN:-} != 1 && ${QRH_REMOTE_RUN:-} != 1 ) ]]; then
  echo 'Refusing local execution. Run this through Namespace or Modal.' >&2
  exit 2
fi
case $task_runner in
  namespace)
    if ! mountpoint -q "$task_cache"; then
      echo "$task_cache must be the attached Namespace cache volume." >&2
      exit 2
    fi ;;
  modal)
    mkdir -p "$task_cache" ;;
  *)
    echo "Unknown QRH_RUNNER: $task_runner" >&2
    exit 2 ;;
esac
test -w "$task_cache" || { echo "$task_cache is not writable." >&2; exit 2; }

task_qrh=$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")/.." && pwd)
task_openai_commit=adc7f1241b42e322a6451854ab7e4b4c146bf78a
task_mathlib_commit=d13f23b723b8a846827a245b89c10fc7d3f11612
task_toolchain=leanprover/lean4:v4.34.1
task_upstream=$task_cache/openai-math-$task_openai_commit
task_evidence=$task_cache/evidence/$(date -u +%Y%m%dT%H%M%SZ)-$$
mkdir -p "$task_evidence"
exec 9>"$task_cache/qrh-build.lock"
flock -n 9 || { echo 'Another QRH build holds the cache lock.' >&2; exit 2; }
task_started=$SECONDS
trap 'task_rc=$?; printf "exit_code=%s total_seconds=%s\n" "$task_rc" "$((SECONDS-task_started))" | tee "$task_evidence/outcome.txt"' EXIT
trap 'exit 143' TERM
trap 'exit 130' INT

stage() {
  local task_label=$1
  shift
  local task_start=$SECONDS task_rc
  set +e
  /usr/bin/time -v "$@" 2>&1 | tee "$task_evidence/$task_label.log"
  task_rc=${PIPESTATUS[0]}
  set -e
  printf '%s exit_code=%s wall_seconds=%s\n' "$task_label" "$task_rc" "$((SECONDS-task_start))" |
    tee -a "$task_evidence/timings.txt"
  return "$task_rc"
}

# Runtime task workers, not the unsupported `lake build -j` option.
# The exact 4.34.1 runtime reads LEAN_NUM_THREADS in src/runtime/object.cpp.
export LEAN_NUM_THREADS=6
export ELAN_HOME=$task_cache/elan
export XDG_CACHE_HOME=$task_cache/tool-cache
export PATH="$ELAN_HOME/bin:$PATH"
printf 'openai=%s\nmathlib=%s\ntoolchain=%s\nLEAN_NUM_THREADS=%s\n' \
  "$task_openai_commit" "$task_mathlib_commit" "$task_toolchain" "$LEAN_NUM_THREADS" > "$task_evidence/pins.txt"
cp "$task_qrh/source-revision.txt" "$task_evidence/" 2>/dev/null || true

for task_command in git curl python3 timeout flock make cc; do
  command -v "$task_command" >/dev/null || { echo "Missing runner prerequisite: $task_command" >&2; exit 2; }
done
test -x /usr/bin/time

if [[ ! -d $task_upstream/.git ]]; then
  stage upstream-clone git clone --no-checkout https://github.com/openai/math.git "$task_upstream"
  git -C "$task_upstream" checkout --detach "$task_openai_commit"
  echo cold-checkout > "$task_evidence/cache.txt"
else
  echo reused-checkout > "$task_evidence/cache.txt"
fi
test "$(git -C "$task_upstream" rev-parse HEAD)" = "$task_openai_commit"
test -z "$(git -C "$task_upstream" status --porcelain --untracked-files=no)"
test "$(cat "$task_upstream/lean/lean-toolchain")" = "$task_toolchain"
test "$(cat "$task_qrh/lean-toolchain")" = "$task_toolchain"
if [[ ! -x $ELAN_HOME/bin/elan ]]; then
  curl -fsSL https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh -o "$task_cache/elan-init.sh"
  stage elan-install sh "$task_cache/elan-init.sh" -y --default-toolchain none
fi
stage toolchain elan toolchain install "$task_toolchain"

cd "$task_upstream/lean"
stage upstream-update lake update
test "$(git -C .lake/packages/mathlib rev-parse HEAD)" = "$task_mathlib_commit"
cp lake-manifest.json "$task_evidence/openai-lake-manifest.json"
if grep -q prelim_decay_2 .lake/packages/PrimeNumberTheoremAnd/PrimeNumberTheoremAnd/Wiener.lean; then
  echo 'The upstream PNT compatibility patch was not applied.' >&2
  exit 1
fi
stage upstream-cache lake exe cache get

# The interval package resolves only Mathlib. OAI is kept in its own workspace
# because its pre-resolution and post-update hooks require their own paths.
cd "$task_qrh"
if [[ ! -e .lake ]]; then
  mkdir -p "$task_cache/qrh-lake-4341"
  ln -s "$task_cache/qrh-lake-4341" .lake
fi
stage qrh-update lake update
test "$(git -C .lake/packages/mathlib rev-parse HEAD)" = "$task_mathlib_commit"
cp lake-manifest.json "$task_evidence/qrh-lake-manifest.json"
stage qrh-cache lake exe cache get
stage qrh-build lake build

cd "$task_upstream/lean"
# Keep every compiler in the supervisor's process group for paused checkpoints.
stage upstream-build timeout --foreground --signal=TERM --kill-after=60s 210m lake build \
  OAI.NumberTheory.DirichletL.Nonvanishing \
  OAI.NumberTheory.SiegelZeros.Estimates.ConstantCancellation \
  OAI.NumberTheory.DirichletL.LogarithmicControl
export QRH_SOURCE_ROOT="$task_qrh"
stage bridge lake env bash -c '
  export LEAN_PATH="$QRH_SOURCE_ROOT/.lake/build/lib/lean:${LEAN_PATH:-}"
  lean --root="$QRH_SOURCE_ROOT" -o "$QRH_SOURCE_ROOT/.lake/build/lib/lean/QRHOpenAI.olean" "$QRH_SOURCE_ROOT/QRHOpenAI.lean"
'
stage axioms lake env bash -c '
  export LEAN_PATH="$QRH_SOURCE_ROOT/.lake/build/lib/lean:${LEAN_PATH:-}"
  lean --root="$QRH_SOURCE_ROOT" "$QRH_SOURCE_ROOT/Audit.lean"
'
python3 "$task_qrh/scripts/check-axioms.py" "$task_evidence/axioms.log"
echo 'Partial lemmas built. Hunt 125 Theorem 1(a) is still open.' | tee "$task_evidence/status.txt"
