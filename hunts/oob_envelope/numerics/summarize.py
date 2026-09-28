"""Print a run JSON from assemble.py as a table (measured values)."""
import json
import sys

d = json.load(open(sys.argv[1]))
for r in d["rows"]:
    line = f"T={r['T']:5.0f}"
    for v, x in r.items():
        if not isinstance(x, dict):
            continue
        if "lam" in x:
            line += f" | {v}: b={x['beta']:.3f} lam={x['lam']:.4e}+-{x['lam_rad']:.0e} neg={x['n_neg']} und={x['undecided']}"
        else:
            line += f" | {v}: b={x['beta']:.3f}"
    print(line)
