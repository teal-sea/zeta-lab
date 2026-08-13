"""Coordinator's INDEPENDENT re-derivation of the blocker-2 closure.

Written from the Lean definitions in EForm3/Defs.lean ONLY.  Imports
nothing from hunts/frontier_math.  Every constant is recomputed.

    g u        = cos(sqrt2 u) on |u| <= 1/2, 0 outside
    A          = sqrt2 sin(1/sqrt2)
    c2 w       = int g(u) g(u+w) du
    Eng G      = (1/A^2) int_{-1}^{1} c2(w) |G(w)|^2 dw
    Qre a b    = int g(u) cosh(au) cos(bu) du
    Qim a b    = int g(u) sinh(au) sin(bu) du
    Shq y      = Qre(2y,0)^2 - A^2
    F w        = sum_j exp(i x_j w),   P w = 2 cosh(yw) exp(i t w)

Obligation: (199/200) Eng(F) + n/200 + 4 <= Eng(F+P).
"""
from __future__ import annotations

import math
import mpmath as mp

mp.mp.dps = 40

SQ2 = mp.sqrt(2)
A = SQ2 * mp.sin(1 / SQ2)
A2 = A**2


# ---- closed forms, derived here -------------------------------------------

def ghat(z):
    """int_{-1/2}^{1/2} cos(sqrt2 u) cosh(z u) du, z complex."""
    z = mp.mpmathify(z)
    zp, zm = z + 1j * SQ2, z - 1j * SQ2
    return mp.sinh(zp / 2) / zp + mp.sinh(zm / 2) / zm


def ghat_quad(z):
    """Same by quadrature, to check the closed form."""
    return mp.quad(lambda u: mp.cos(SQ2 * u) * mp.cosh(z * u), [-mp.mpf(1) / 2, mp.mpf(1) / 2])


def Qre(a, b):
    return mp.re(ghat(mp.mpc(a, b)))


def Qim(a, b):
    return mp.im(ghat(mp.mpc(a, b)))


def phir(v):
    """Qre 0 v = int g cos(vu) du."""
    return Qre(0, v)


def damage(y, s):
    """Qim^2 - Qre^2 = -Re[ghat(y+is)^2]."""
    return -mp.re(ghat(mp.mpc(y, s)) ** 2)


def Shq(y):
    return Qre(2 * y, 0) ** 2 - A2


# ---- the definition route (quadrature), for the identity check -------------

def c2(w):
    """int g(u) g(u+w) du; support |w| <= 1."""
    w = mp.mpf(w)
    lo, hi = max(-mp.mpf(1) / 2, -mp.mpf(1) / 2 - w), min(mp.mpf(1) / 2, mp.mpf(1) / 2 - w)
    if hi <= lo:
        return mp.mpf(0)
    return mp.quad(lambda u: mp.cos(SQ2 * u) * mp.cos(SQ2 * (u + w)), [lo, hi])


def Eng(G):
    return (1 / A2) * mp.quad(lambda w: c2(w) * abs(G(w)) ** 2, [-1, 0, 1])


def margin_definition(xs, y, t):
    """Eng(F+P) - (199/200)Eng(F) - n/200 - 4, straight from the definitions."""
    n = len(xs)

    def F(w):
        return mp.fsum([mp.e ** (1j * x * w) for x in xs])

    def P(w):
        return 2 * mp.cosh(y * w) * mp.e ** (1j * t * w)

    eF = Eng(F)
    eFP = Eng(lambda w: F(w) + P(w))
    return eFP - mp.mpf(199) / 200 * eF - mp.mpf(n) / 200 - 4


def slack_formula(xs, y, t):
    """Shq/2 - sum_j D_j + (1/400) sum_{j<k} phir^2."""
    dam = mp.fsum([damage(y, x - t) for x in xs])
    rel = mp.fsum([phir(xs[j] - xs[k]) ** 2
                   for j in range(len(xs)) for k in range(j + 1, len(xs))])
    return Shq(y) / 2 - dam + rel / 400


# ---------------------------------------------------------------------------

def check_identity():
    print("== 1. margin == (4/A^2) * slack, from the definitions ==")
    cases = [
        ([6.517], 0.5, 0.0),
        ([6.517, 6.517], 0.5, 0.0),
        ([6.517, 6.517, 6.517], 0.5, 0.0),
        ([0.0, 1.3, 6.5, -6.5], 0.5, 0.2),
        ([6.5, 6.9, 12.8, -6.6], 0.4, 0.0),
        ([-3.1, 0.0, 2.7, 9.4, 15.2], 0.25, 1.1),
    ]
    worst = mp.mpf(0)
    for xs, y, t in cases:
        m = margin_definition(xs, y, t)
        s = slack_formula(xs, y, t)
        pred = 4 / A2 * s
        d = abs(m - pred)
        worst = max(worst, d)
        print(f"  n={len(xs)} y={y} t={t}: margin={mp.nstr(m, 10)}  "
              f"(4/A^2)slack={mp.nstr(pred, 10)}  |diff|={mp.nstr(d, 3)}")
    print(f"  worst |diff| = {mp.nstr(worst, 3)}   (LEMMA A holds numerically)")
    return worst


def find_windows(y, nwin=400):
    """Damage windows: maximal intervals of s>0 with D(y,s) > 0."""
    y = mp.mpf(y)
    # zeros of phir: ghat(i v) real, first near 6.64
    zeros = []
    v, step = mp.mpf(1), mp.mpf('0.01')
    prev = phir(v)
    while len(zeros) < nwin + 2:
        v2 = v + step
        cur = phir(v2)
        if prev * cur < 0:
            zeros.append(mp.findroot(phir, (v, v2), solver='bisect'))
        v, prev = v2, cur
    wins = []
    for z in zeros[:nwin]:
        f = lambda s: damage(y, s)
        if f(z) <= 0:
            wins.append(None)
            continue
        # bracket the sign changes either side of z
        lo = mp.findroot(f, (z - 3, z), solver='bisect')
        hi = mp.findroot(f, (z, z + 3), solver='bisect')
        pk = mp.findroot(lambda s: mp.diff(f, s), z, solver='secant')
        wins.append({'zero': z, 'lo': lo, 'hi': hi, 'width': hi - lo,
                     'peak': pk, 'D': f(pk)})
    return [w for w in wins if w]


def check_structure(y=0.5, nwin=60):
    print(f"\n== 2. LEMMA C structure at y={y} ==")
    wins = find_windows(y, nwin)
    w_max = max(w['width'] for w in wins)
    lo_min = min(w['lo'] for w in wins)
    print(f"  windows found: {len(wins)}")
    print(f"  (i)   innermost window starts at s = {mp.nstr(lo_min, 12)}"
          f"   [claim 6.0653, EForm3 no_damage 5.6]")
    print(f"  (ii)  max window width = {mp.nstr(w_max, 10)}   [claim 0.9860008]")
    gaps = [wins[i + 1]['lo'] - wins[i]['hi'] for i in range(len(wins) - 1)]
    print(f"        min gap BETWEEN windows = {mp.nstr(min(gaps), 10)}")
    # is phir positive and decreasing on [0, w_max]?
    grid = [w_max * k / 400 for k in range(401)]
    vals = [phir(v) for v in grid]
    mono = all(vals[i] >= vals[i + 1] for i in range(len(vals) - 1))
    gamma = phir(w_max)
    print(f"  (iii) phir(0)=A={mp.nstr(A, 10)}, phir(w_max)={mp.nstr(gamma, 10)}"
          f"  [claim gamma >= 0.88452]")
    print(f"        phir nonincreasing on [0,w_max]: {mono}   min on grid ="
          f" {mp.nstr(min(vals), 10)}")
    tot = mp.fsum([w['D'] for w in wins])
    print(f"  (iv)  sum of window peaks (one side, {len(wins)} windows) = "
          f"{mp.nstr(tot, 10)}   [claim <= 6.8610e-03]")
    print(f"        largest peak D_1 = {mp.nstr(wins[0]['D'], 10)} at s = "
          f"{mp.nstr(wins[0]['peak'], 10)}   [claim 4.396424e-03 at 6.517]")
    return wins, w_max, gamma


def check_majorant(y=0.5, nwin=60):
    print(f"\n== 3. LEMMA C arithmetic at y={y} ==")
    wins, w_max, gamma = check_structure(y, nwin), None, None
    wins, w_max, gamma = wins  # unpack
    c = gamma**2 / 800
    total = mp.mpf(0)
    levels = []
    for w in wins:
        D = w['D']
        best, bn = mp.mpf(0), 0
        for n in range(0, 40):
            v = n * D - c * n * (n - 1)
            if v > best:
                best, bn = v, n
        total += best
        levels.append(bn)
    total_both = 2 * total
    sh = Shq(y) / 2
    print(f"  relief per in-window pair = gamma^2/400 = {mp.nstr(gamma**2/400, 10)}")
    print(f"  per-window optima (first 6 levels): {levels[:6]}")
    print(f"  sum over {len(wins)} windows, BOTH sides = {mp.nstr(total_both, 10)}"
          f"   [claim 1.95721e-02]")
    print(f"  Shq(y)/2 = {mp.nstr(sh, 10)}   [claim 3.37542e-02]")
    print(f"  slack lower bound = {mp.nstr(sh - total_both, 10)}  "
          f"safety factor {mp.nstr(sh/total_both, 8)}")
    print(f"  HOLDS: {sh > total_both}")
    return total_both, sh


def check_tail(y=0.5, s_from=None, nwin=60):
    """Is the discarded tail actually small?  Sum peaks past window nwin."""
    print(f"\n== 4. tail past {nwin} windows ==")
    wins = find_windows(y, nwin + 60)
    tail = mp.fsum([w['D'] for w in wins[nwin:]])
    print(f"  windows {nwin}..{nwin+60} peak sum (one side) = {mp.nstr(tail, 6)}")
    # D ~ C/s^2: extrapolate the rest
    last = wins[-1]
    C = float(last['D']) * float(last['peak']) ** 2
    rest = C / (2 * math.pi) / float(last['peak'])
    print(f"  D_k * s_k^2 -> {C:.8f} (const => D ~ C/s^2)")
    print(f"  crude integral majorant past s={float(last['peak']):.4f}: {rest:.3e}")
    print(f"  => the {nwin}-window truncation costs at most ~"
          f"{2*(float(tail)+rest):.2e} (both sides), vs headroom "
          f"{float(Shq(y)/2):.6f}")


def check_worst_y():
    print("\n== 5. is y=1/2 the binding depth? ==")
    for y in ['0.1', '0.2', '0.3', '0.4', '0.5']:
        y = mp.mpf(y)
        wins = find_windows(y, 30)
        w_max = max(w['width'] for w in wins)
        gamma = phir(w_max)
        c = gamma**2 / 800
        tot = mp.mpf(0)
        for w in wins:
            tot += max(n * w['D'] - c * n * (n - 1) for n in range(0, 40))
        tot *= 2
        sh = Shq(y) / 2
        print(f"  y={float(y):.2f}: net<= {mp.nstr(tot,8)}  Shq/2={mp.nstr(sh,8)}"
              f"  ratio={float(tot/sh):.4f}  w_max={float(w_max):.5f}")


def adversarial_search(y=0.5, trials=4000, seed=20260813):
    """Direct search for a configuration violating slack > 0.

    Uses slack_formula (exact identity), NOT the majorant, so it can also
    catch an error in the majorant's *conclusion*.
    """
    print(f"\n== 6. adversarial search for slack <= 0 at y={y} ==")
    import random
    rng = random.Random(seed)
    wins = find_windows(y, 12)
    peaks = [float(w['peak']) for w in wins]
    peaks = [-p for p in reversed(peaks)] + peaks
    worst = None
    mp.mp.dps = 25
    for _ in range(trials):
        mode = rng.random()
        if mode < 0.45:                      # multiplicities on peaks
            xs = []
            for p in peaks:
                for _ in range(rng.randint(0, 4)):
                    xs.append(p + rng.gauss(0, 0.25))
        elif mode < 0.75:                    # tight clusters on the top peaks
            xs = []
            for p in peaks[:4] + peaks[-4:]:
                m = rng.randint(0, 8)
                for i in range(m):
                    xs.append(p + rng.uniform(-0.5, 0.5))
        else:                                # free random
            xs = [rng.uniform(-40, 40) for _ in range(rng.randint(1, 25))]
        if not xs:
            continue
        s = slack_formula(xs, mp.mpf(y), mp.mpf(0))
        if worst is None or s < worst[0]:
            worst = (s, list(xs))
    mp.mp.dps = 40
    s, xs = worst
    print(f"  trials={trials}, worst slack = {mp.nstr(s, 10)} "
          f"(n={len(xs)})")
    print(f"  Shq/2 = {mp.nstr(Shq(mp.mpf(y))/2, 8)};  violation: {s <= 0}")
    return s


if __name__ == '__main__':
    print(f"A = {mp.nstr(A, 20)}  (claim 0.9187253698655684)")
    print(f"|ghat closed form - quadrature| at 0.5+6.5i = "
          f"{mp.nstr(abs(ghat(mp.mpc(0.5,6.5)) - ghat_quad(mp.mpc(0.5,6.5))), 3)}")
    check_identity()
    check_majorant()
    check_tail()
    check_worst_y()
    adversarial_search()
