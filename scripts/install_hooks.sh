#!/usr/bin/env bash
# Install the pre-push secret guard into this checkout.
#
# Hooks live in .git/hooks and are not version controlled, so every clone and
# every worktree needs this run once. Cheap, and the alternative is the
# 2026-08-20 incident: a live OpenRouter key committed to a local branch, caught
# by a human asking a question rather than by anything mechanical.
set -euo pipefail

repo_root="$(git rev-parse --show-toplevel)"
hooks_dir="$(git rev-parse --git-path hooks)"
mkdir -p "$hooks_dir"

cat > "$hooks_dir/pre-push" <<'HOOK'
#!/usr/bin/env bash
# Refuse to push credential-shaped content. See scripts/check_secrets.py.
set -uo pipefail

repo_root="$(git rev-parse --show-toplevel)"
python_bin="$repo_root/.venv/bin/python"
[ -x "$python_bin" ] || python_bin="$(command -v python3)"

zero="0000000000000000000000000000000000000000"
status=0

while read -r _local_ref local_sha _remote_ref remote_sha; do
  [ "$local_sha" = "$zero" ] && continue          # deletion, nothing to scan
  if [ "$remote_sha" = "$zero" ]; then
    range="$local_sha --not --remotes=origin"      # new branch: everything new
  else
    range="$remote_sha..$local_sha"
  fi
  # shellcheck disable=SC2086
  "$python_bin" "$repo_root/scripts/check_secrets.py" --range "$range" || status=1
done

if [ "$status" -ne 0 ]; then
  echo "" >&2
  echo "pre-push: blocked. Override only if you are certain:" >&2
  echo "  git push --no-verify ..." >&2
  exit 1
fi
exit 0

# The secret guard passed. Now the gate: same hook, one push, both answers.
gate="$(git rev-parse --git-path hooks)/pre-push-gate"
[ -x "$gate" ] && { "$gate" || exit 1; }
exit $status
HOOK

chmod +x "$hooks_dir/pre-push"

# The gate, in the same hook and for the same reason the secret guard is there: a rule that lives
# only in prose is a habit, and nothing has to remember a habit. This runs tier 1 BEFORE the push,
# so a red tree never reaches a runner and nobody stands and waits for one to say what a local
# machine could have said in seconds.
#
# It does NOT copy the list of tier-1 files. It reads them out of .github/workflows/checks.yml,
# which is the single place that decides what tier 1 is. A copied list is a list that drifts, and
# the copy would go stale silently: the gate would keep passing while checking the wrong thing.
cat > "$hooks_dir/pre-push-gate" <<'GATE'
#!/usr/bin/env bash
# Tier 1, locally, before the push. The file list comes from the workflow, never from a copy.
set -uo pipefail
repo_root="$(git rev-parse --show-toplevel)"
cd "$repo_root" || exit 1

workflow=".github/workflows/checks.yml"
[ -f "$workflow" ] || { echo "pre-push: $workflow is gone; tier 1 cannot be derived. Refusing." >&2; exit 1; }
# Comment lines are stripped first. checks.yml mentions tests/test_lab_state.py in prose on
# line 10, and picking that up would make the gate run a file tier 1 does not, so the gate could
# fail where CI passes. A guard that is stricter than the thing it mirrors gets ignored too.
mapfile -t tier1 < <(sed 's/#.*//' "$workflow" | grep -o 'tests/test_[a-z0-9_]*\.py' | sort -u)
[ "${#tier1[@]}" -gt 0 ] || { echo "pre-push: no tests named in $workflow. Refusing rather than passing empty." >&2; exit 1; }

# An interpreter that actually has pytest. A cloud VM builds one at /opt/zeta-venv because
# python3.11 cannot install cypari2; a laptop uses .venv; a bare python3 usually has no pytest.
python_bin=""
for c in "$repo_root/.venv/bin/python" /opt/zeta-venv/bin/python "$(command -v python3)"; do
  [ -x "$c" ] && "$c" -c "import pytest" >/dev/null 2>&1 && { python_bin="$c"; break; }
done
[ -n "$python_bin" ] || { echo "pre-push: no interpreter with pytest (.venv, /opt/zeta-venv, python3). Refusing rather than passing silently." >&2; exit 1; }

"$python_bin" -m pytest -q -p no:cacheprovider -o addopts="" --no-header "${tier1[@]}" || {
  echo "pre-push: tier 1 is red (${#tier1[@]} files from $workflow). Fix it here." >&2; exit 1; }
"$python_bin" scripts/make_context.py --check || {
  echo "pre-push: CONTEXT.md is stale. Run: python scripts/make_context.py" >&2; exit 1; }
GATE
chmod +x "$hooks_dir/pre-push-gate"
echo "installed: $hooks_dir/pre-push and $hooks_dir/pre-push-gate"
