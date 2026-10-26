"""Run just the abstract Lean proof remotely, using a pinned Mathlib cache.

No repository or credential is uploaded. Only Symmetry.lean is sent as text.
Run from the repo root with the operator's configured Modal environment:
    modal run hunts/reversal_minimax/modal_check.py
"""

from pathlib import Path
import hashlib
import json
import subprocess
import modal

HERE = Path(__file__).resolve().parent
MATHLIB_REV = "51e6992efd06126df61a496bebf8f49482a4e129"
app = modal.App("zeta-reversal-minimax")
image = (
    modal.Image.debian_slim(python_version="3.12")
    .apt_install("curl", "git", "zstd", "unzip", "build-essential")
    .run_commands(
        "curl -sSf https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh "
        "| sh -s -- -y --default-toolchain leanprover/lean4:v4.33.0-rc2",
        "git init /opt/mathlib",
        "git -C /opt/mathlib remote add origin https://github.com/leanprover-community/mathlib4",
        f"git -C /opt/mathlib fetch --depth=1 origin {MATHLIB_REV}",
        "git -C /opt/mathlib checkout --detach FETCH_HEAD",
    )
    .env({"PATH": "/root/.elan/bin:/usr/local/bin:/usr/bin:/bin"})
    .workdir("/opt/mathlib")
    .run_commands(
        "lake exe cache get Mathlib/Data/Real/Basic.lean "
        "Mathlib/Algebra/BigOperators/Group/Finset/Basic.lean "
        "Mathlib/Tactic/Linarith.lean Mathlib/Tactic/NormNum.lean Mathlib/Tactic/Ring.lean"
    )
)


@app.function(image=image, cpu=2, memory=16384, timeout=600)
def check(source: str):
    path = Path("/tmp/ReversalMinimax.lean")
    path.write_text(source)
    proc = subprocess.run(["lake", "env", "lean", str(path)], cwd="/opt/mathlib",
                          text=True, capture_output=True, timeout=540)
    version = subprocess.check_output(["lean", "--version"], text=True).strip()
    return {"exit_code": proc.returncode, "stdout": proc.stdout, "stderr": proc.stderr,
            "lean_version": version, "mathlib_rev": MATHLIB_REV,
            "source_sha256": hashlib.sha256(source.encode()).hexdigest()}


@app.local_entrypoint()
def main():
    result = check.remote((HERE / "Symmetry.lean").read_text())
    (HERE / "lean_check.json").write_text(json.dumps(result, indent=2) + "\n")
    print(json.dumps(result, indent=2))
    if result["exit_code"]:
        raise RuntimeError("Lean rejected the proof")
