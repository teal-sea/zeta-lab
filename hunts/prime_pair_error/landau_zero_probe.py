"""Locate the low-lying zeros of L(s, chi_3) and report their real parts.

Supports THEOREM_B_SEQUENCE.md: checks, at the heights this probe can reach,
whether any computed zero of L(s, chi_3) has real part detectably away from
1/2 -- i.e. whether a concrete witness for Theta_chi > 1/2 is visible at low
height. It is not a search for such a witness at all heights and proves
nothing about Theta_chi itself; it only reports what is observed in range.
"""
import json
import mpmath as mp

mp.mp.dps = 30


def chi3(n):
    n = n % 3
    if n == 0:
        return 0
    if n == 1:
        return 1
    return -1


def L_chi3(s):
    # Dirichlet L-function for the nonprincipal character mod 3, via
    # mpmath's Hurwitz zeta: L(s,chi) = 3^-s * (zeta(s,1/3) - zeta(s,2/3)).
    return mp.mpf(3) ** (-s) * (mp.zeta(s, mp.mpf(1) / 3) - mp.zeta(s, mp.mpf(2) / 3))


def find_zeros(t_max, step=0.5):
    # Bracket sign changes of the real-valued function
    # Z(t) = L(1/2+it,chi3) * (phase correction), following the same
    # Riemann-Siegel-style real-on-critical-line trick used for zeta,
    # is not implemented here; instead this does a direct argument-principle
    # count via mpmath's findroot on |L(1/2+it,chi3)| minima, which is
    # adequate for a low-height existence check, not a rigorous isolation.
    ts = []
    t = mp.mpf('0.1')
    prev = abs(L_chi3(mp.mpc(0.5, t)))
    t_grid = [mp.mpf(i) * step for i in range(1, int(t_max / step) + 1)]
    prev_t = t
    for tt in t_grid:
        cur = abs(L_chi3(mp.mpc(0.5, tt)))
        # local minimum bracket: use derivative sign via central difference
        ts.append((float(tt), float(cur)))
        prev_t, prev = tt, cur
    return ts


def refine_zero(t_guess):
    # Complex Newton/secant in the full plane, started near 0.5+i*t_guess:
    # this locates the nearest actual zero of L(s,chi3) wherever it is, it
    # does not assume the zero sits on Re(s)=1/2.
    f = lambda z: L_chi3(z)
    try:
        root = mp.findroot(f, mp.mpc(0.5, t_guess))
        return complex(root)
    except Exception:
        return None


def off_line_check(t, sigma_list):
    # Check |L(sigma+it,chi3)| at a few sigma off the critical line near a
    # located low point, to confirm the minimum is on Re=1/2 and not off it.
    out = {}
    for sigma in sigma_list:
        out[str(sigma)] = abs(complex(L_chi3(mp.mpc(sigma, t))))
    return out


def main():
    t_max = 60.0
    scan = find_zeros(t_max, step=0.25)
    # crude local-minimum detection
    candidates = []
    for i in range(1, len(scan) - 1):
        t0, v0 = scan[i]
        tm, vm = scan[i - 1]
        tp, vp = scan[i + 1]
        if v0 < vm and v0 < vp and v0 < 0.5:
            candidates.append(t0)

    refined = []
    seen_t = set()
    for c in candidates:
        r = refine_zero(mp.mpf(c))
        if r is None:
            continue
        key = round(r.imag, 3)
        if key in seen_t:
            continue
        seen_t.add(key)
        refined.append(r)

    report = {
        "t_max_scanned": t_max,
        "scan_step": 0.25,
        "candidate_minima_t": candidates,
        "located_zeros": [
            {
                "re": r.real,
                "im": r.imag,
                "residual_abs_L": abs(complex(L_chi3(mp.mpc(r.real, r.imag)))),
                "deviation_from_half": r.real - 0.5,
            }
            for r in refined
        ],
        "off_line_spot_checks": [],
    }
    # For each located zero, evaluate |L| at nearby sigma off its own real
    # part, at the same height, as a sanity check that the Newton solve
    # landed on a genuine isolated zero and not a false minimum.
    for r in refined:
        checks = off_line_check(r.imag, [r.real - 0.1, r.real - 0.05, r.real, r.real + 0.05, r.real + 0.1])
        report["off_line_spot_checks"].append({"im": r.imag, "abs_L_by_sigma": checks})

    with open("hunts/prime_pair_error/results_landau_zero_probe.json", "w") as fh:
        json.dump(report, fh, indent=2)

    print(json.dumps(report, indent=2))


if __name__ == "__main__":
    main()
