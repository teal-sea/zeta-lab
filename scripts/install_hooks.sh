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
HOOK

chmod +x "$hooks_dir/pre-push"
echo "installed: $hooks_dir/pre-push"
