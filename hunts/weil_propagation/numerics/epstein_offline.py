"""Independent route: does zeta_(1,1,6) have an off-line zero where its
negative Weil ground states point (t ~ 16 to 18)?

The window scan (epstein_scan.py) finds the deep negative ground states
concentrated at frequencies 15 to 18.5. By the explicit-formula dictionary an
off-line pair at gamma - i delta is the only way a positive-on-line zero sum
can go negative, so the scan predicts an off-line zero near there. This
checks it with code that shares nothing with the Galerkin assembly: the
lattice-sum completion zeta.epstein.epstein_completed and the argument
principle zeta.epstein.count_zeros_box on a box strictly right of the
critical line; if the count is positive, mp.findroot polishes the zero from
seeds at the beam frequencies.

Writes epstein_offline.json.
"""

from __future__ import annotations

import os
import sys
import time

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import wp_common as W  # noqa: E402
from mpmath import mp  # noqa: E402
from zeta.epstein import count_zeros_box, epstein_completed  # noqa: E402

OUT = os.path.join(W.HERE, "epstein_offline.json")
FORM = (1, 1, 6)
DPS = 20
BOXES = [("0.51", "1.3", "14", "20")] + [tuple(a.split(",")) for a in sys.argv[1:]]


def fn(z):
    return epstein_completed(z, FORM, dps=DPS)


def main():
    d = W.load(OUT, {"meta": {"form": list(FORM), "dps": DPS, "note": __doc__.split("\n\n")[0]}, "boxes": {}, "roots": []})
    for a, b, c, e in BOXES:
        k = f"[{a},{b}]x[{c},{e}]"
        if k in d["boxes"]:
            continue
        t0 = time.time()
        with mp.workdps(DPS):
            n = count_zeros_box(mp.mpc(a, c), mp.mpc(b, e), dps=DPS, fn=fn)
        d["boxes"][k] = {"count": n, "elapsed_s": round(time.time() - t0, 1)}
        W.save(OUT, d)
        print("box", k, "count", n, round(time.time() - t0, 1), "s", flush=True)
    if not d["roots"] and any(v["count"] > 0 for v in d["boxes"].values()):
        with mp.workdps(DPS):
            for seed in [(0.7, 16.5), (0.7, 17.5), (0.6, 17.0), (0.9, 17.0)]:
                t0 = time.time()
                try:
                    r = mp.findroot(fn, mp.mpc(*seed), tol=mp.mpf(10) ** (-DPS + 6), maxsteps=40)
                except Exception as exc:  # noqa: BLE001
                    d["roots"].append({"seed": seed, "error": str(exc)[:120]})
                    W.save(OUT, d)
                    continue
                rec = {"seed": seed, "root": [mp.nstr(mp.re(r), 15), mp.nstr(mp.im(r), 15)],
                       "abs_value": mp.nstr(abs(fn(r)), 3), "elapsed_s": round(time.time() - t0, 1)}
                d["roots"].append(rec)
                W.save(OUT, d)
                print("root", rec, flush=True)
                if mp.re(r) > 0.5 + 1e-3 and 14 < mp.im(r) < 20:
                    break


if __name__ == "__main__":
    main()
