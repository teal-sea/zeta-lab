"""Trusted subprocess entry point. No model content is executed here."""
import contextlib
import io
import json
from pathlib import Path
import re
import runpy
import sys


def fixed(source: Path, mode: str) -> dict:
    certificate = "certificates.npz" if mode == "fine" else "certificates_coarse.npz"
    log = io.StringIO()
    sys.argv = [str(source / "certify_bloch.py"), str(source / certificate)]
    with contextlib.redirect_stdout(log):
        runpy.run_path(str(source / "certify_bloch.py"), run_name="__main__")
    text = log.getvalue()
    if f"PASS: all assertions applicable to the {mode} certificate verified" not in text:
        raise RuntimeError("missing success marker")
    match = re.search(r"\(C\)  B >= sqrt3/4 \+ \[([0-9.]+) \+/-", text)
    if not match:
        raise RuntimeError("missing gain enclosure")
    return {"gain": match[1], "log": text}


def near(source: Path) -> dict:
    import numpy as np
    import variable_radius_certificate as vr
    prerequisite = fixed(source, "fine")
    log = io.StringIO()
    with np.load(source / "variable_radius_certificate.npz", allow_pickle=False) as data:
        if not (float(data["eta"]) == vr.ETA
                and float(data["large_rad"]) == vr.LARGE_RAD
                and float(data["point_edges"][-1]) == vr.LARGE_RAD):
            raise RuntimeError("source/data constants disagree")
        with contextlib.redirect_stdout(log):
            positivity = vr.verify_positivity(data, vr.ETA)
            gain = vr.verify_near_moment(data, vr.ETA)
    import math
    if not (math.isfinite(positivity) and positivity > 0 and math.isfinite(gain) and gain > 0):
        raise RuntimeError("near certificate verification failed")
    return {"gain": repr(gain), "positivity": positivity,
            "log": prerequisite["log"] + log.getvalue(), "away_sectors_replayed": False}


if __name__ == "__main__":
    source, mode = Path(sys.argv[1]), sys.argv[2]
    sys.path.insert(0, str(source))
    print(json.dumps(near(source) if mode == "near" else fixed(source, mode)))
