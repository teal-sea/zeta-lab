"""A missing pyyaml must not abort pytest.

Issue #225: `scripts/palomar_correspondence.py` used `sys.exit` at import
time when yaml was absent. SystemExit is a BaseException, so collecting
`tests/test_palomar_correspondence.py` killed the whole run (exit 3, the
summary reading "1 skipped"). Raising ImportError is what pytest can
turn into a skip or a collection error instead of an abort.
"""
from __future__ import annotations

import pathlib
import subprocess
import sys

ROOT = pathlib.Path(__file__).resolve().parents[1]
SCRIPTS = ROOT / "scripts"


def test_missing_yaml_raises_importerror_not_systemexit():
    """Importing the module with yaml blocked is ImportError, not SystemExit."""
    code = (
        "import sys\n"
        "sys.modules['yaml'] = None\n"
        "sys.path.insert(0, %r)\n"
        "try:\n"
        "    import palomar_correspondence\n"
        "except SystemExit as e:\n"
        "    raise SystemExit('still SystemExit: %%s' %% e)\n"
        "except ImportError as e:\n"
        "    assert 'pip install pyyaml' in str(e), repr(e)\n"
        "    print('ImportError')\n"
        "else:\n"
        "    raise SystemExit('imported with yaml blocked')\n"
        % str(SCRIPTS)
    )
    got = subprocess.run(
        [sys.executable, "-c", code],
        capture_output=True, text=True, cwd=ROOT,
    )
    assert got.returncode == 0, got.stderr
    assert "ImportError" in got.stdout


def test_missing_yaml_as_script_exits_nonzero_with_the_install_hint():
    """Run as a script: the same hint, a nonzero exit, not a silent abort."""
    code = (
        "import sys, runpy\n"
        "sys.modules['yaml'] = None\n"
        "runpy.run_path(%r, run_name='__main__')\n"
        % str(SCRIPTS / "palomar_correspondence.py")
    )
    got = subprocess.run(
        [sys.executable, "-c", code],
        capture_output=True, text=True, cwd=ROOT,
    )
    assert got.returncode != 0
    assert "pip install pyyaml" in got.stderr
    assert "SystemExit" not in got.stderr
