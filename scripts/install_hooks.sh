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

# The gate, in the same hook, for the same reason the secret guard is there: a rule that lives
# only in prose is a habit, and an agent never promised to follow it. This is tier 1 from
# .github/workflows/checks.yml, the same files in the same order, stdlib and pytest only, about
# six seconds. It runs BEFORE the push, so a red tree cannot reach a runner and there is nothing
# to stand and wait for afterwards.
#
# Written 2026-09-10, after an agent ran the full suite locally, watched 2957 tests pass, and then
# held a merge waiting for the identical suite to finish again on a runner. CI is a second opinion
# on a clean checkout, which is the one thing a local machine cannot give you. It was never
# permission, and now nothing has to remember that: the gate answers here, immediately.
cat > "$hooks_dir/pre-push-gate" <<'GATE'
#!/usr/bin/env bash
# Tier 1, locally, before the push. Mirror of .github/workflows/checks.yml.
set -uo pipefail
repo_root="$(git rev-parse --show-toplevel)"
cd "$repo_root" || exit 1
# The interpreter, in the order a checkout is likely to have one. A cloud VM builds the
# toolchain at /opt/zeta-venv because python3.11 cannot install cypari2; a laptop uses .venv.
# A bare python3 usually has no pytest, so the gate must SAY that rather than report red.
python_bin=""
for c in "$repo_root/.venv/bin/python" /opt/zeta-venv/bin/python "$(command -v python3)"; do
  [ -x "$c" ] && "$c" -c "import pytest" >/dev/null 2>&1 && { python_bin="$c"; break; }
done
if [ -z "$python_bin" ]; then
  echo "pre-push: no interpreter with pytest (.venv, /opt/zeta-venv, python3). Gate NOT run." >&2
  echo "pre-push: refusing rather than passing silently. See the Setup section of CLAUDE.md." >&2
  exit 1
fi

"$python_bin" -m pytest -q -p no:cacheprovider -o addopts="" --no-header \
  tests/test_docs_numbering.py tests/test_repo_hygiene.py tests/test_telemetry.py \
  tests/test_huntspec.py tests/test_meta_ledger.py tests/test_graveyard.py \
  tests/test_review.py tests/test_dossier_schema.py tests/test_discovery_schema.py \
  tests/test_site.py || {
    echo "pre-push: tier 1 is red. Fix it here; do not push and wait for the runner to say so." >&2
    exit 1
  }
"$python_bin" scripts/make_context.py --check || {
    echo "pre-push: CONTEXT.md is stale. Run: python scripts/make_context.py" >&2
    exit 1
  }
GATE
chmod +x "$hooks_dir/pre-push-gate"
echo "installed: $hooks_dir/pre-push and $hooks_dir/pre-push-gate"
