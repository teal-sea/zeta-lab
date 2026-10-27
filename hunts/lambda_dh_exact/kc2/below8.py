"""The strip below t = 8 for kill condition 2: count on [0.90, 2.05] x [-8, 8], Arb.

Symmetric about the real axis so that s = 1, where the four Hurwitz poles
cancel and a ball evaluation of f is useless, lies strictly inside the
rectangle; a total of 0 then also excludes real zeros in [0.90, 2.05].

Run: .venv/bin/python hunts/lambda_dh_exact/kc2/below8.py
"""
import json
import os
import sys
from fractions import Fraction

_HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.dirname(_HERE))
import decide_deep_zero as dd  # noqa: E402
import decide_kc2 as kc  # noqa: E402

r = kc.count_rect(dd.ArbRoute(prec=kc.PREC), kc.SIG_L, kc.SIG_R, Fraction(-8), Fraction(8))
r["rectangle"] = [["9/10", "41/20"], ["-8", "8"]]
json.dump(r, open(os.path.join(_HERE, "below8.json"), "w"), indent=2)
print(r)
