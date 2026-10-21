"""Assemble zeros.json from the two merged census files, the abscissa bounds,
and PARI/GP recomputations of the off-line zeros; audit the result.

    .venv/bin/python hunts/plocal_rivals/assemble.py MERGED_Q17.json MERGED_Q73.json [--out PATH]

Writes ``zeros.json`` next to this file unless ``--out`` says otherwise.  Grades are recorded inside it.

Third routes (PARI/GP through cypari2: no mpmath, no Arb).  PARI builds its own
character (``znstar``, ``chareval``) and its own k = tan(theta/2) from
``lfunrootres``, so nothing below reads route A's or route B's k.

* ``pari_hurwitz_zero``: Newton on q^{-s} sum_a b(a) zetahurwitz(s, a/q) from
  route A's root, for every off-line zero.  The formula is the census's, the
  Hurwitz implementation is PARI's.
* ``pari_combination_zero``: Newton on lfun of F's own Dirichlet series,
  lfuncreate([b(n)], self-dual, gamma [0], conductor q, root number +1), for the
  lowest off-line zero of each q.  It uses neither L(s, chi) nor a Hurwitz zeta,
  only PARI's L-function machinery for a degree-1 self-dual series.
* ``pari_two_character_zero``: Newton on A lfun(L(chi)) + conj(A) lfun(L(chi-bar)),
  for the lowest off-line zero of each q.

``audit`` recomputes every consistency condition ``ZEROS.md`` relies on from
the file alone and returns the failures; ``test_rivals.py`` runs it on
``zeros.json`` and on planted corruptions of it.
"""

from __future__ import annotations

import json
import os
import sys
import time
from fractions import Fraction

HERE = os.path.dirname(os.path.abspath(__file__))
REPO = os.path.dirname(os.path.dirname(HERE))
for _p in (REPO, HERE):
    if _p not in sys.path:
        sys.path.insert(0, _p)

OUT = os.path.join(HERE, "zeros.json")

#: the decided headline rationals of the phase abscissa (test_rivals.py pins them)
SIGMA_STAR = {17: "1.09896904163", 73: "1.0445906373"}
PHASE_ROOT = {17: ("1.0989690416287099417", "1.0989690416290103236"),
              73: ("1.0445906372787647953", "1.044590637279698182")}
DOMINATION = {17: ("1.5842597817", "1.5842597818"), 73: ("1.6148802929", "1.6148802930")}

#: the census was asked for every zero up to this height
T_TARGET = 1000

#: real precision of the lfun-on-F route (see main)
COMBINATION_PREC = 80


# ---------------------------------------------------------------------------
# PARI third routes
# ---------------------------------------------------------------------------


def _pstr(x) -> str:
    return str(x).replace(" E", "e")


def pari_setup(q: int, prec: int = 45):
    """A cypari2 session with PARI's own chi, chi-bar, k, b(n) and three forms of F."""
    import cypari2

    pari = cypari2.Pari()
    pari.set_real_precision(prec)
    pari(f"G = znstar({q}, 1); g = lift(znprimroot({q}))")
    pari("C = 0; forvec(v = vector(#G.cyc, j, [0, G.cyc[j] - 1]), "
         "if(chareval(G, v~, g) == 1/4 && charorder(G, v~) == 4, C = v~; break))")
    # the conjugate's exponent vector must be reduced mod G.cyc (test_rivals.py)
    pari("Cb = vector(#C, j, (G.cyc[j] - C[j]) % G.cyc[j])~")
    pari("L = lfuncreate([G, C]); Lb = lfuncreate([G, Cb]); k = tan(arg(lfunrootres(L)[3])/2)")
    pari("A = (1 - I*k)/2")
    # a GP definition swallows the rest of its line, so one per call
    pari("bn(n) = my(x = chareval(G, C, n, [I, 4])); if(x == 0, 0, real(x) + k*imag(x))")
    pari(f"B = vector({q} - 1, a, bn(a))")
    pari(f"HD(s) = my(h = 0, d = 0, z, z1); for(a = 1, {q} - 1, if(B[a], "
         f"z = zetahurwitz(s, a/{q}); z1 = zetahurwitz(s, a/{q}, 1); "
         f"h += B[a]*z; d += B[a]*(z1 - log({q})*z))); [{q}^(-s)*h, {q}^(-s)*d]")
    pari(f"Fo = lfuncreate([n -> vector(n, j, bn(j)), 0, [0], 1, {q}, 1])")
    pari("Fp(s) = A*lfun(L, s) + conj(A)*lfun(Lb, s)")
    pari("dFp(s) = A*lfun(L, s, 1) + conj(A)*lfun(Lb, s, 1)")
    # one Newton step per route
    pari("NH(z) = my(v = HD(z)); v[1]/v[2]")
    pari("NC(z) = lfun(Fo, z)/lfun(Fo, z, 1)")
    pari("NT(z) = Fp(z)/dFp(z)")
    return pari


def _newton(pari, step: str, value: str, re: float, im: float, iters: int, prec: int) -> dict:
    t0 = time.time()
    pari(f"z = {re!r} + {im!r}*I")
    pari(f"for(i = 1, {iters}, dz = {step}(z); z = z - dz; if(abs(dz) < 10^(-{prec - 5}), break))")
    return {
        "re": _pstr(pari("real(z)")),
        "im": _pstr(pari("imag(z)")),
        "abs_F": _pstr(pari(f"abs({value})")),
        "seconds": round(time.time() - t0, 2),
    }


def pari_hurwitz_zero(pari, re: float, im: float, prec: int = 45) -> dict:
    out = _newton(pari, "NH", "HD(z)[1]", re, im, 8, prec)
    out["route"] = "PARI zetahurwitz: q^(-s) sum_a b(a) zetahurwitz(s, a/q), PARI's own chi and k"
    return out


def pari_combination_zero(pari, re: float, im: float, prec: int = 45) -> dict:
    out = _newton(pari, "NC", "lfun(Fo, z)", re, im, 12, prec)
    out["route"] = ("PARI lfun on F's own Dirichlet series: lfuncreate([b(n)], self-dual, "
                    "gamma [0], conductor q, root number +1)")
    return out


def pari_two_character_zero(pari, re: float, im: float, prec: int = 45) -> dict:
    out = _newton(pari, "NT", "Fp(z)", re, im, 12, prec)
    out["route"] = ("PARI lfun on the two characters of lfuncreate([znstar(q,1), chi]), "
                    "A = (1 - I k)/2 with k from lfunrootres")
    return out


def _inside(box, re: str, im: str) -> bool:
    x0, x1, y0, y1 = (Fraction(v) for v in box)
    return x0 < Fraction(re) < x1 and y0 < Fraction(im) < y1


# ---------------------------------------------------------------------------
# summary and audit
# ---------------------------------------------------------------------------


def summarise(m: dict) -> dict:
    zs = m["zeros"]
    low = min(zs, key=lambda z: z["im_A"]) if zs else None
    hi_re = max(zs, key=lambda z: z["re_A"]) if zs else None
    lo_re = min(zs, key=lambda z: z["re_A"]) if zs else None
    return {
        "height": m["height"],
        "n_windows": m["n_windows"],
        "N_total_A": m["N_total_A"],
        "N_total_B": m["N_total_B"],
        "n_line_sign_changes_A": m["n_line_A"],
        "n_line_sign_changes_B": m["n_line_B"],
        "n_zeros_right_of_line": m["n_right"],
        "all_windows_close_A": m["all_windows_close_A"],
        "all_windows_close_B": m["all_windows_close_B"],
        "unit_boxes_disjoint_B": m["unit_boxes_disjoint_B"],
        "parity_A": m["parity_A"],
        "parity_B": m["parity_B"],
        "every_zero_in_decided_unit_box_B": all(z["unit_N_B"] == 1 for z in zs),
        "every_zero_in_decided_tiny_box_B": all(z["tiny_N_B"] == 1 for z in zs),
        "windows_line_rescanned_A": [w["j"] for w in m["windows"] if w["A"]["line_rescanned"]],
        "windows_line_rescanned_B": [w["j"] for w in m["windows"] if w["B"]["line_rescanned"]],
        "max_psi_defect_A": m["max_psi_defect_A"],
        "lowest_offline_zero_A": [low["re_A"], low["im_A"]] if low else None,
        "max_real_part_zero_A": [hi_re["re_A"], hi_re["im_A"]] if hi_re else None,
        "min_real_part_zero_A": [lo_re["re_A"], lo_re["im_A"]] if lo_re else None,
    }


def audit(doc: dict) -> list[str]:
    """Every consistency condition ZEROS.md relies on, recomputed from the file.

    Returns the list of failures; empty means every condition holds.
    """
    fails: list[str] = []
    for qs, case in doc["cases"].items():
        s, ws, zs = case["summary"], case["windows"], case["zeros"]
        tag = f"q={qs}"
        if not ws or ws[0]["lo"] != 0:
            fails.append(f"{tag}: windows do not start at height 0")
        for w0, w1 in zip(ws, ws[1:]):
            if w0["hi"] != w1["lo"]:
                fails.append(f"{tag}: windows {w0['j']} and {w1['j']} are not contiguous")
        if ws and ws[-1]["hi"] < T_TARGET:
            fails.append(f"{tag}: census stops at {ws[-1]['hi']} < {T_TARGET}")
        if ws and ws[-1]["hi"] != s["height"]:
            fails.append(f"{tag}: summary height {s['height']} is not the last boundary")
        zeros_by_window: dict[int, int] = {}
        for z in zs:
            hits = [w["j"] for w in ws if w["lo"] < z["im_A"] < w["hi"]]
            if len(hits) != 1:
                fails.append(f"{tag}: zero at {z['im_A']} lies in {len(hits)} windows")
                continue
            zeros_by_window[hits[0]] = zeros_by_window.get(hits[0], 0) + 1
        for w in ws:
            A, B = w["A"], w["B"]
            j = w["j"]
            if not (A["closes"] and None not in (A["n_box"], A["n_line"], A["n_right"])
                    and A["n_box"] == A["n_line"] + 2 * A["n_right"]):
                fails.append(f"{tag}: route A does not close window {j}")
            if not (B["closes"] and None not in (B["n_box"], B["n_line"], B["n_right_boxed"])
                    and B["n_box"] == B["n_line"] + 2 * B["n_right_boxed"]):
                fails.append(f"{tag}: route B does not close window {j}")
            if (A["n_box"], A["n_line"], A["n_right"]) != (B["n_box"], B["n_line"], B["n_right_boxed"]):
                fails.append(f"{tag}: routes disagree in window {j}")
            if zeros_by_window.get(j, 0) != A["n_right"]:
                fails.append(f"{tag}: window {j} lists {zeros_by_window.get(j, 0)} zeros, "
                             f"counts {A['n_right']}")
        n_box = sum(w["A"]["n_box"] for w in ws)
        n_line = sum(w["A"]["n_line"] for w in ws)
        if not (n_box == s["N_total_A"] == s["N_total_B"]):
            fails.append(f"{tag}: window counts {n_box} do not sum to the totals")
        if n_line != s["n_line_sign_changes_A"] or n_line != s["n_line_sign_changes_B"]:
            fails.append(f"{tag}: line counts do not sum to the totals")
        if not (len(zs) == s["n_zeros_right_of_line"] and n_box == n_line + 2 * len(zs)):
            fails.append(f"{tag}: N != n_line + 2 n_right overall")
        if not (s.get("max_psi_defect_A") is not None and s["max_psi_defect_A"] < 1e-6):
            fails.append(f"{tag}: route A's folded counts are not safely integral")
        for flag in ("parity_A", "parity_B", "unit_boxes_disjoint_B", "all_windows_close_A",
                     "all_windows_close_B", "every_zero_in_decided_unit_box_B",
                     "every_zero_in_decided_tiny_box_B"):
            if s.get(flag) is not True:
                fails.append(f"{tag}: {flag} is not True")
        if not all(case["base_B"].get(k) is True for k in
                   ("domination_at_sR", "real_segment_decided", "F_sR_positive")):
            fails.append(f"{tag}: route B base point not decided")
        boxes = []
        for z in zs:
            where = f"{tag}: zero at {z['re_A']:.6f} + {z['im_A']:.6f}i"
            if not (z["unit_status_B"] == "decided" and z["unit_N_B"] == 1
                    and z["tiny_status_B"] == "decided" and z["tiny_N_B"] == 1):
                fails.append(f"{where}: route B box not decided with one zero")
                continue
            tb = [Fraction(v) for v in z["tiny_box_B"]]
            if not tb[0] > Fraction(1, 2):
                fails.append(f"{where}: tiny box reaches the critical line")
            if not _inside(z["tiny_box_B"], repr(z["re_A"]), repr(z["im_A"])):
                fails.append(f"{where}: route A root outside route B's tiny box")
            ph = z.get("pari_hurwitz")
            if not ph or not _inside(z["tiny_box_B"], ph["re"], ph["im"]):
                fails.append(f"{where}: PARI root missing or outside route B's tiny box")
            boxes.append(tb)
        for i in range(len(boxes)):
            for k in range(i + 1, len(boxes)):
                a, c = boxes[i], boxes[k]
                if not (a[1] <= c[0] or c[1] <= a[0] or a[3] <= c[2] or c[3] <= a[2]):
                    fails.append(f"{tag}: tiny boxes {i} and {k} overlap")
        for key in ("pari_combination", "pari_two_character"):
            tr = case.get("third_route", {}).get(key)
            low = min(zs, key=lambda z: z["im_A"]) if zs else None
            if low is not None and (not tr or not _inside(low["tiny_box_B"], tr["re"], tr["im"])):
                fails.append(f"{tag}: {key} root missing or outside the lowest zero's tiny box")
    return fails


def zeros_md_lines(doc: dict) -> list[str]:
    """The table lines ZEROS.md quotes, rendered from zeros.json.

    ``test_rivals.py`` checks that every line returned here occurs verbatim in
    ZEROS.md, so the document cannot drift from the data.
    """
    cases = doc["cases"]
    qs = sorted(cases, key=int)
    out = ["| | " + " | ".join(f"q = {q}" for q in qs) + " |"]

    def row(label, f):
        out.append("| " + label + " | " + " | ".join(f(cases[q]) for q in qs) + " |")

    row("last boundary T", lambda c: repr(c["summary"]["height"]))
    row("windows", lambda c: str(c["summary"]["n_windows"]))
    row("zeros of G_q with 0 < Im s < T, route A = route B",
        lambda c: str(c["summary"]["N_total_A"]))
    row("sign changes of Z on the line, route A = route B",
        lambda c: str(c["summary"]["n_line_sign_changes_A"]))
    row("zeros in Re s > 1/2 (each with its mirror in Re s < 1/2)",
        lambda c: str(c["summary"]["n_zeros_right_of_line"]))
    row("lowest zero off the line",
        lambda c: "%.7f + %.7f i" % tuple(c["summary"]["lowest_offline_zero_A"]))
    row("largest real part found",
        lambda c: "%.7f at height %.4f" % tuple(c["summary"]["max_real_part_zero_A"]))
    row("smallest real part found",
        lambda c: "%.7f at height %.4f" % tuple(c["summary"]["min_real_part_zero_A"]))
    row("windows route A rescanned 8 times finer",
        lambda c: ", ".join(map(str, c["summary"]["windows_line_rescanned_A"])) or "none")
    row("windows route B rescanned 8 times finer",
        lambda c: ", ".join(map(str, c["summary"]["windows_line_rescanned_B"])) or "none")
    row("largest integrality defect of a route A folded count",
        lambda c: "%.1e" % c["summary"]["max_psi_defect_A"])
    row("largest distance from a route A root to PARI's",
        lambda c: "%.1e" % c["summary"]["max_pari_distance_to_A"])
    out.append("| q | # | Re rho | Im rho |")
    for q in qs:
        for i, z in enumerate(sorted(cases[q]["zeros"], key=lambda z: z["im_A"]), 1):
            out.append(f"| {q} | {i} | {z['re_A']:.6f} | {z['im_A']:.6f} |")
    return out


# ---------------------------------------------------------------------------
# main
# ---------------------------------------------------------------------------


def main() -> None:
    args = sys.argv[1:]
    out_path = OUT
    if "--out" in args:
        i = args.index("--out")
        out_path = args[i + 1]
        del args[i:i + 2]
    merged = {}
    for path in args:
        with open(path) as fh:
            d = json.load(fh)
        merged[int(d["q"])] = d
    out = {
        "hunt": "plocal_rivals",
        "hunt_number": 149,
        "assembled": time.strftime("%Y-%m-%d"),
        "function": "F_q(s) = c L(s, chi) + conj(c) L(s, chi-bar), c = (1 - i k)/2, "
                    "chi of order 4 mod q with chi(g) = i at the least primitive root g; "
                    "G_q(s) = (q/pi)^(s/2) Gamma(s/2) F_q(s) = G_q(1 - s); a zero means a zero of G_q",
        "grades": {
            "route_A": "measured: mpmath fp evaluation, folded argument principle, "
                       "right-box winding counts, Newton to |F| < 1e-11",
            "route_B": "enclosure-carrying given the classical functional equation, the "
                       "Gauss-sum root number and the cited Rademacher bound: Arb balls, "
                       "winding.py's chord-tube rule, decided sign changes and decided boxes",
            "pari": "measured: every off-line zero re-located by PARI's own Newton iteration "
                    "on its own Hurwitz zeta; the lowest per q also on lfun of F's own series "
                    "and on the two-character combination",
            "abscissa": "enclosure-carrying (Arb), strip2.py's Euler-phase method ported to q",
        },
        "accounting": "per window n_box = n_line + 2 n_right; n_box from the folded count "
                      "N(0, T) = Psi(T)/pi at the window ends, n_line from sign changes of Z "
                      "on the route's own grid plus its own signs at the ends, n_right from "
                      "right-box counts (route A) or decided unit boxes (route B)",
        "abscissa": {
            str(q): {
                "phase_root_bracket": list(PHASE_ROOT[q]),
                "decided_sigma_star": SIGMA_STAR[q],
                "domination_bracket": list(DOMINATION[q]),
                "statement": f"every zero of G_{q} (every nontrivial zero of F_{q}) has "
                             f"1 - {SIGMA_STAR[q]} < Re s < {SIGMA_STAR[q]}",
            } for q in sorted(merged)
        },
        "cases": {},
    }
    for q, m in sorted(merged.items()):
        pari = pari_setup(q)
        zeros = []
        for z in m["zeros"]:
            z = dict(z)
            ph = pari_hurwitz_zero(pari, z["re_A"], z["im_A"])
            ph["inside_route_B_tiny_box"] = _inside(z["tiny_box_B"], ph["re"], ph["im"])
            ph["distance_to_A"] = float(abs(complex(float(Fraction(ph["re"])) - z["re_A"],
                                                    float(Fraction(ph["im"])) - z["im_A"])))
            z["pari_hurwitz"] = ph
            zeros.append(z)
            print(f"q={q} zero {z['im_A']:.6f}: PARI Hurwitz {ph['seconds']} s, "
                  f"inside={ph['inside_route_B_tiny_box']}", flush=True)
        m = dict(m)
        m["zeros"] = zeros
        case = {"summary": summarise(m), "zeros": zeros, "windows": m["windows"],
                "base_B": m["base_B"], "third_route": {}}
        if zeros:
            z0 = min(zeros, key=lambda z: z["im_A"])
            # PARI's generic lfun loses digits with height at 45 digits (at q = 73's
            # lowest zero it agrees with the other routes to about 21 digits at
            # precision 45, 37 at 60, and every digit at 80: ZEROS.md), so the
            # combination route runs at 80
            pari80 = pari_setup(q, prec=COMBINATION_PREC)
            for key, fn, ses, prec in (
                    ("pari_combination", pari_combination_zero, pari80, COMBINATION_PREC),
                    ("pari_two_character", pari_two_character_zero, pari, 45)):
                tr = fn(ses, z0["re_A"], z0["im_A"], prec=prec)
                tr["inside_route_B_tiny_box"] = _inside(z0["tiny_box_B"], tr["re"], tr["im"])
                tr["real_precision"] = prec
                case["third_route"][key] = tr
            case["summary"]["max_pari_distance_to_A"] = max(z["pari_hurwitz"]["distance_to_A"]
                                                            for z in zeros)
        out["cases"][str(q)] = case
    fails = audit(out)
    out["audit_failures"] = fails
    with open(out_path, "w") as fh:
        json.dump(out, fh, indent=1)
    print(f"wrote {out_path}; audit failures: {fails if fails else 'none'}")


if __name__ == "__main__":
    main()
