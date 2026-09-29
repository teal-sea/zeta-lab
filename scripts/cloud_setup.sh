#!/usr/bin/env bash
# Build this tree's numerical toolchain, for a Claude Code cloud environment's setup script.
#
# Paste this file's contents into the environment's Setup script field, or call it. The
# environment runs a setup script ONCE, then Anthropic snapshots the filesystem and every later
# session in that environment starts from the snapshot with the script skipped. So the toolchain
# is paid for once per environment, not once per hunt, which is what makes launching many hunt
# sessions cheap rather than merely possible.
#
# Measured 2026-09-10: 42 seconds. The documented setup-script budget is about five minutes.
#
# python3.12 and NOT 3.11, and this is not a preference. On 3.11 cypari2 publishes no wheel, pip
# falls back to the sdist, that needs a system PARI/GP the runner does not have, and the whole
# `pip install -r requirements.txt` dies taking every other dependency with it. requirements.txt
# says so in its own comments; this is that comment made executable.
set -euo pipefail

VENV="${ZETA_VENV:-/opt/zeta-venv}"
PY="${ZETA_PYTHON:-python3.12}"

command -v "$PY" >/dev/null 2>&1 || {
  echo "cloud_setup: $PY not found. 3.11 will not do: cypari2 has no cp311 wheel." >&2
  exit 1
}

"$PY" -m venv "$VENV"
"$VENV/bin/pip" -q install --upgrade pip
"$VENV/bin/pip" -q install mpmath numpy scipy matplotlib sympy pytest pytest-xdist \
    python-flint 'cypari2>=2.2'

# Both optional backends must import. Without python-flint, zeta/rigor.py falls back to mpmath's
# iv context: correct, roughly 1600x slower on the certified paths, and it silently removes the
# Arb-vs-mpmath cross-check that is the only reason rigor.py may use its reserved word. Without
# cypari2 the PARI oracle skips instead of running, so every reference value comes from one
# library again. A session that discovers either three hours into a cell has already wasted the
# money. Fail here, by name.
"$VENV/bin/python" - <<'CHECK'
import sys
missing = []
for mod, why in (("flint", "python-flint: the Arb backend and the rigor.py cross-check"),
                 ("cypari2", "cypari2: the PARI oracle, the second independent implementation")):
    try:
        __import__(mod)
    except Exception as exc:
        missing.append(f"  {why}\n    {type(exc).__name__}: {exc}")
if missing:
    print("cloud_setup: the optional backends are not optional here.", file=sys.stderr)
    print("\n".join(missing), file=sys.stderr)
    sys.exit(1)
print("cloud_setup: python-flint and cypari2 both import")
CHECK

echo "cloud_setup: ready at $VENV"
echo "cloud_setup: hunts should call $VENV/bin/python, and boards should declare it in sandbox.tools"
