"""Ball trapezoid for Li coefficients: aliasing bound, branch tracking, sizing.

Setting.  g(z) = log F(1/(1-z)) = sum_m b_m z^m is analytic on |z| < R_a, and
lambda_m = m b_m.  With N nodes z_k = r e^{2 pi i k/N} on a circle r < R_a,

    btilde_n = (1/(N r^n)) sum_k g(z_k) e^{-2 pi i k n/N} = b_n + E_n,
    E_n      = sum_{j>=1} b_{n+jN} r^{jN}                       (0 <= n < N),

and Cauchy's estimate on any circle rho with r < rho < R_a, |b_m| <= M(rho) rho^{-m},
M(rho) = max_{|z|=rho} |g(z) - C| for any constant C, gives the aliasing bound

    |lambda_n - n btilde_n|  <=  n M(rho) rho^{-n} x / (1 - x),    x = (r/rho)^N.   (A)

The additive constant of g (the branch of the logarithm at one point) changes b_0
only, so the bound and every lambda_n with n >= 1 are blind to it.  What is not
free is continuity: g must be one analytic function along the whole circle.

The branch.  g = log G(s) + log f(s) (``balls.py``).  log G is Arb's principal
log-gamma expression, analytic on Re s > -1, and the circle |z| = r < 1 maps into
Re s > 1/2.  log f is the analytic branch on the image disc; on the part of it
with Re s >= 3/2 we have |f - 1| <= S(3/2) = 0.7376 < 1, the principal Log f is
analytic there, and we fix the branch by it.  Along the rest of the circle
(the arc through s = 1/(1+r), where |Im s| stays below about sqrt(2/(1-r^2)))
arg f is continued node to node.  The step from node i to node j is
decided in balls: the arc from z_i to z_j is enclosed in one ball, its image
f(1/(1 - ball)) must lie in one open half-plane through 0, and then the continuous
change is the difference of the rotated principal arguments, each in
(-pi/2, pi/2).  The chain must land back on the principal value where Re s >= 3/2
again (or, by conjugate symmetry, on arg f = 0 at the real point s = 1/(1+r)):
that is the closure check, equivalent to winding number zero.

By g(conj z) = conj g(z) only the upper half circle is sampled; node N - k is
the conjugate of node k.

M(rho) is bounded the same way: a cover of the upper half circle rho by arc balls;
on each, |log G| from an Arb ball, and |log f| <= -log(1 - S) + arcsin S where
Re s >= 3/2, else |log |f|| + |continuous arg f| from the chained cover.

Nothing here is evidence about the Riemann Hypothesis.
"""

from __future__ import annotations

import json
import math
import os
import sys
import time
from fractions import Fraction as Q

from flint import acb, arb, fmpz

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))

from balls import HERE, S_tail, f_ball, logG_ball, prec_guard, q_arb  # noqa: E402

ART = os.path.join(HERE, "artifacts")
SIGMA_P = Q(3, 2)        # principal-branch half-plane, S(3/2) < 1
#: s-balls wider than this are split without being evaluated: Arb's Hurwitz zeta
#: on a ball hundreds wide is slow and its image always meets 0 anyway
#: (measured: a rehearsal at N = 2^17 spent over 13 CPU-minutes on such balls).
S_BALL_MAX = 0.5


def _pk(x):
    """Exact (mantissa, exponent) pairs of an arb's midpoint and radius, or None."""
    if x is None:
        return None
    m, e = x.mid().man_exp()
    rm, re = x.rad().man_exp()
    return (int(m), int(e), int(rm), int(re))


def _uk(t):
    if t is None:
        return None
    m, e, rm, re = t
    return arb(arb(fmpz(m)) * arb(2) ** e, arb(fmpz(rm)) * arb(2) ** re)


def _save(path, obj) -> None:
    import pickle
    with open(path + ".tmp", "wb") as fh:
        pickle.dump(obj, fh)
    os.replace(path + ".tmp", path)


def _narrow(sb) -> bool:
    return bool(sb.real.is_finite() and sb.imag.is_finite()
                and float(sb.real.rad()) + float(sb.imag.rad()) < S_BALL_MAX)


# ---------------------------------------------------------------------------
# geometry
# ---------------------------------------------------------------------------

def node(r: arb, k: int, N: int) -> acb:
    """z_k = r e^{2 pi i k/N} as a ball (the angle is an exact rational times pi)."""
    x = q_arb(Q(2 * k, N))
    return acb(r * x.cos_pi(), r * x.sin_pi())


def arc_ball(r: arb, q0: Q, q1: Q) -> acb:
    """A ball containing the arc {r e^{i pi q}: q0 <= q <= q1}.

    Every point of the arc is within r * pi * (q1 - q0)/2 of its angular midpoint
    (arc length bounds chord length); the square of that half-width contains
    the disc.  The midpoint itself is a ball, whose radius is added.
    """
    qm = q_arb((q0 + q1) / 2)
    c = acb(r * qm.cos_pi(), r * qm.sin_pi())
    h = r * arb.pi() * q_arb((q1 - q0) / 2)
    return acb(arb(c.real.mid(), arb(h.upper()) + c.real.rad()),
               arb(c.imag.mid(), arb(h.upper()) + c.imag.rad()))


def s_of(z: acb) -> acb:
    return 1 / (1 - z)


# ---------------------------------------------------------------------------
# rotated principal argument
# ---------------------------------------------------------------------------

_ROT = (acb(1), acb(0, -1), acb(-1), acb(0, 1))


def half_plane(w: acb):
    if w.real > 0:
        return 0
    if w.imag > 0:
        return 1
    if w.real < 0:
        return 2
    if w.imag < 0:
        return 3
    return None


def rarg(w: acb, k: int):
    """Arg(w e^{-i k pi/2}) in (-pi/2, pi/2) when proven, else None."""
    u = w * _ROT[k]
    if not (u.real > 0):
        return None
    return (u.imag / u.real).atan()


# ---------------------------------------------------------------------------
# the aliasing circle: M(rho)
# ---------------------------------------------------------------------------

def _up(cur: float, b: arb) -> float:
    """max(cur, upper end of b), rounded up to a float."""
    v = float(arb(b).upper())
    return max(cur, math.nextafter(v, math.inf) * (1 + 1e-12))


def principal_bound(prec: int) -> arb:
    """|Log f| <= -log(1 - S) + arcsin S on Re s >= 3/2, S = S(3/2)."""
    S = S_tail(SIGMA_P, prec)
    with prec_guard(prec):
        return arb((-(1 - S).log() + S.asin()).upper())


def bound_M(rho: arb, prec: int = 128, max_depth: int = 60, model=None,
            ckpt: str | None = None, every: int = 50) -> dict:
    """An upper bound for max |g| on |z| = rho, from an adaptive arc cover.

    Walks the upper half circle q in [0, 1] (angle pi q) left to right with a
    stack of intervals.  Continuous arg f is carried from the last interval
    whose ball lies in Re s >= 3/2 (principal there).  Returns the bound and the
    closure value of arg f at q = 1 (s = 1/(1+rho), real, f > 0 there).
    """
    model = model or DHModel()
    if hasattr(model, "principal_bound"):
        PB = model.principal_bound(prec)
    else:
        PB = principal_bound(prec) if model.name == "dh" else None
    pending = None             # right end q of the last principal arc, anchored lazily
    stats = {"arcs": 0, "principal_arcs": 0, "tracked_arcs": 0, "splits": 0}
    M = 0.0
    arg_anchor = None          # continuous arg h at the left end of the next arc
    stack = [(Q(0), Q(1), 0)]
    with prec_guard(prec):
        if PB is None:             # no principal region: anchor h real positive at q = 0
            h0 = model.h(s_of(acb(rho)), prec)
            if not (h0.real > 0 and h0.imag.contains(0)):
                raise RuntimeError("no anchor for the arg of h")
            arg_anchor = arb(0)
        if ckpt and os.path.exists(ckpt):          # resume an interrupted cover
            import pickle
            st = pickle.load(open(ckpt, "rb"))
            stack, M, stats, pending = st["stack"], st["M"], st["stats"], st["pending"]
            arg_anchor = _uk(st["arg_anchor"])
        done_since = 0
        while stack:
            if ckpt and done_since >= every:
                _save(ckpt, {"stack": stack, "M": M, "stats": stats, "pending": pending,
                             "arg_anchor": _pk(arg_anchor)})
                done_since = 0
            done_since += 1
            q0, q1, depth = stack.pop()
            zb = arc_ball(rho, q0, q1)
            sb = s_of(zb)
            ok = sb.real.is_finite() and sb.imag.is_finite() and \
                (sb.real.rad() + sb.imag.rad()) < abs(sb).lower() / 8
            if ok:
                Lb = model.L(sb, prec)
                ok = Lb.real.is_finite() and Lb.imag.is_finite()
            if ok and PB is not None and model.principal(sb):
                M = _up(M, abs(Lb).upper() + PB)
                stats["principal_arcs"] += 1
                # the continuous arg at the right end is the principal value there;
                # it is evaluated only if a tracked arc follows (lazily)
                pending, arg_anchor = q1, None
                stats["arcs"] += 1
                continue
            if ok and arg_anchor is None and pending is not None:
                fr = model.h(s_of(acb(rho * q_arb(pending).cos_pi(),
                                      rho * q_arb(pending).sin_pi())), prec)
                arg_anchor = rarg(fr, 0)
                pending = None
            if ok and arg_anchor is not None:
                Lb = model.L(sb, prec)
                fb = model.h(sb, prec)
                k = half_plane(fb)
                if k is not None:
                    z0 = acb(rho * q_arb(q0).cos_pi(), rho * q_arb(q0).sin_pi())
                    z1 = acb(rho * q_arb(q1).cos_pi(), rho * q_arb(q1).sin_pi())
                    a0, a1 = rarg(model.h(s_of(z0), prec), k), rarg(model.h(s_of(z1), prec), k)
                    ab = rarg(fb, k)
                    if a0 is not None and a1 is not None and ab is not None:
                        # continuous arg over the arc lies in anchor + (ab - a0)
                        arg_range = arg_anchor + (ab - a0)
                        logabs = abs(fb).log()
                        bound = abs(Lb).upper() + abs(logabs).upper() + abs(arg_range).upper()
                        M = _up(M, bound)
                        arg_anchor = arg_anchor + (a1 - a0)
                        stats["tracked_arcs"] += 1
                        stats["arcs"] += 1
                        continue
            if depth >= max_depth:
                raise RuntimeError(f"arc [{q0}, {q1}] not resolved")
            qm = (q0 + q1) / 2
            stats["splits"] += 1
            stack.append((qm, q1, depth + 1))   # right half popped second
            stack.append((q0, qm, depth + 1))
        closure = arg_anchor
    return {"M_upper": M, "closure_arg_at_pi": closure.str(10, radius=True),
            "closure_contains_0": bool(closure.contains(0)), "stats": stats}


# ---------------------------------------------------------------------------
# sizing
# ---------------------------------------------------------------------------

def nodes_needed(n_max: int, r: float, rho: float, M: float, tol: float) -> int:
    """Smallest N with n M rho^{-n} x/(1-x) <= tol for all n <= n_max, x = (r/rho)^N."""
    worst = math.log(n_max) + math.log(M) + n_max * math.log(1 / rho)
    need = worst - math.log(tol)
    # x/(1-x) <= tol' iff x <= tol'/(1+tol'); with tol' tiny this is x <= tol'
    return int(math.ceil((need + 1e-9) / math.log(rho / r)))


def bits_needed(n_max: int, r: float, M: float, tol: float, N: int) -> int:
    """Working bits so that sample round-off, carried through the DFT and the
    division by r^n and multiplied by n, stays below tol: a float estimate used to
    choose the precision; the run itself reports the actual ball radii."""
    amp = n_max * math.exp(n_max * math.log(1 / r)) * M * (1 + math.log2(N))
    return int(math.ceil(math.log2(amp / tol))) + 16


def aliasing_bound(n: int, N: int, r: arb, rho: arb, M: arb) -> arb:
    """The right side of (A) as a ball, for one n."""
    x = (r / rho) ** N
    return arb(n) * M * rho ** (-n) * x / (1 - x)


def plan(c: int, n_max: int, rho: float, M: float, tol: float, sec_per_eval: float) -> dict:
    r = math.sqrt(1 - 1 / c)
    N_alias = nodes_needed(n_max, r, rho, M, tol)
    N = max(N_alias, n_max + 1)
    N2 = 1 << (N - 1).bit_length()
    bits = bits_needed(n_max, r, M, tol, N2)
    evals = N2 // 2 + 1
    return {"c": c, "r": r, "one_minus_r": 1 - r, "rho": rho, "n_max": n_max,
            "N_aliasing": N_alias, "N_power_of_two": N2, "bits": bits,
            "node_evaluations_upper_half": evals,
            "core_hours_sampling": evals * sec_per_eval / 3600}


# ---------------------------------------------------------------------------
# models: g = L(s) + log h(s), L analytic in balls, arg h tracked
# ---------------------------------------------------------------------------

class DHModel:
    """g = log G(s) + log f(s); principal Log f where Re s > 3/2."""
    name = "dh"

    def __init__(self, fault: str | None = None):
        self.fault = fault

    def L(self, s: acb, prec: int) -> acb:
        return logG_ball(s, prec)

    def h(self, s: acb, prec: int) -> acb:
        return f_ball(s, prec)

    def principal(self, s: acb) -> bool:
        return bool(s.real > q_arb(SIGMA_P))


class XiModel:
    """xi(s) = (1/2) s pi^{-s/2} Gamma(s/2) [(s-1) zeta(s)]; L = the first four
    factors (Log s principal on Re s > 0), h = (s-1) zeta(s), tracked from h(s) > 0
    at the real node s = 1/(1-r).  ``fault='gamma_shift'`` replaces Gamma(s/2) by
    Gamma(s/2 + 2^-60), a planted evaluator defect."""
    name = "xi"

    def __init__(self, fault: str | None = None):
        self.fault = fault

    def L(self, s: acb, prec: int) -> acb:
        with prec_guard(prec):
            w = s / 2
            gw = w + arb(2) ** -60 if self.fault == "gamma_shift" else w
            return -arb(2).log() + s.log() - w * arb.pi().log() + gw.lgamma()

    def h(self, s: acb, prec: int) -> acb:
        with prec_guard(prec):
            return (s - 1) * s.zeta()

    def principal(self, s: acb) -> bool:
        return False


# ---------------------------------------------------------------------------
# the ball trapezoid
# ---------------------------------------------------------------------------

def arc_change(model, r: arb, qa: Q, qb: Q, ha: acb, hb: acb, prec: int,
               stats: dict, depth: int = 0, max_depth: int = 48) -> arb:
    """Continuous change of arg h along the arc r e^{i pi q}, qa <= q <= qb.

    Decided when one ball around the arc has its h-image in an open half-plane;
    otherwise the arc is bisected and h evaluated at the new point.  A zero of h
    on or within the ball resolution of the arc exhausts ``max_depth`` and
    raises: the step is refused, never guessed.
    """
    zb = arc_ball(r, qa, qb)
    sb = s_of(zb)
    if _narrow(sb):
        kk = half_plane(model.h(sb, prec))
        if kk is not None:
            a, b = rarg(ha, kk), rarg(hb, kk)
            if a is not None and b is not None:
                return b - a
    if depth >= max_depth:
        raise RuntimeError(f"arc step [{qa}, {qb}] refused: h may vanish on the arc")
    qm = (qa + qb) / 2
    x = q_arb(qm)
    hm = model.h(s_of(acb(r * x.cos_pi(), r * x.sin_pi())), prec)
    stats["arc_bisections"] = stats.get("arc_bisections", 0) + 1
    return (arc_change(model, r, qa, qm, ha, hm, prec, stats, depth + 1, max_depth)
            + arc_change(model, r, qm, qb, hm, hb, prec, stats, depth + 1, max_depth))


def evaluate_nodes(model, r: arb, N: int, prec: int, k0: int, k1: int) -> tuple:
    """(L, h, principal) at nodes k0 <= k < k1, the expensive part of sampling."""
    L, H, P = [], [], []
    with prec_guard(prec):
        for k in range(k0, k1):
            s = s_of(node(r, k, N))
            L.append(model.L(s, prec))
            H.append(model.h(s, prec))
            P.append(model.principal(s))
    return L, H, P


def sample_upper(model, r: arb, N: int, prec: int, block: int = 256,
                 fault: str | None = None, evaluated: tuple | None = None,
                 ckpt: str | None = None, every: int = 100) -> tuple[list, dict]:
    """g(z_k) for k = 0..N/2 as balls, with arg h continued by ball steps.

    ``fault='skip_unwrap'`` adds 2 pi i to every tracked sample after the
    middle of the tracked stretch: the branch error the tracking exists to
    prevent, planted.
    """
    assert N % 2 == 0
    half = N // 2
    t0 = time.time()
    stats = {"principal_nodes": 0, "tracked_nodes": 0, "cover_balls": 0,
             "cover_splits": 0}
    L, H, P = evaluated if evaluated is not None else \
        evaluate_nodes(model, r, N, prec, 0, half + 1)
    with prec_guard(prec):
        t1 = time.time()
        arg = [None] * (half + 1)
        # principal stretch from k = 0
        k = 0
        while k <= half and P[k]:
            a = rarg(H[k], 0)
            if a is None:
                raise RuntimeError(f"principal node {k} has Re h not > 0")
            arg[k] = a
            k += 1
        stats["principal_nodes"] = k
        if k == 0:                              # anchor: h real positive at k = 0
            if not (H[0].real > 0 and H[0].imag.contains(0)):
                raise RuntimeError("no anchor: h(s_0) not real positive")
            arg[0] = arb(0)
            k = 1
        i = k - 1                               # last node with a known arg
        if ckpt and os.path.exists(ckpt):       # resume an interrupted tracking
            import pickle
            st = pickle.load(open(ckpt, "rb"))
            i, stats = st["i"], st["stats"]
            for m, t in enumerate(st["arg"]):
                arg[m] = _uk(t)
        blocks_since = 0
        while i < half:
            if ckpt and blocks_since >= every:
                _save(ckpt, {"i": i, "stats": stats,
                             "arg": [_pk(a) for a in arg[:i + 1]]})
                blocks_since = 0
            blocks_since += 1
            j = min(i + block, half)
            while True:
                zb = arc_ball(r, Q(2 * i, N), Q(2 * j, N))
                sb = s_of(zb)
                kk = half_plane(model.h(sb, prec)) if _narrow(sb) else None
                if kk is not None:
                    ai = rarg(H[i], kk)
                    rs = [rarg(H[m], kk) for m in range(i + 1, j + 1)]
                    if ai is not None and all(x is not None for x in rs):
                        for m, x in zip(range(i + 1, j + 1), rs):
                            arg[m] = arg[i] + (x - ai)
                        stats["cover_balls"] += 1
                        break
                if j == i + 1:
                    # one step still undecided: bisect the arc itself, chaining
                    # through evaluations at points between the two nodes
                    arg[j] = arg[i] + arc_change(model, r, Q(2 * i, N), Q(2 * j, N),
                                                 H[i], H[j], prec, stats)
                    stats["cover_balls"] += 1
                    break
                j = i + max(1, (j - i) // 2)
                stats["cover_splits"] += 1
            stats["tracked_nodes"] += j - i
            i = j
        closure = arg[half]
        stats["closure_arg"] = closure.str(10, radius=True)
        stats["closure_contains_0"] = bool(closure.contains(0))
        g = []
        mid = (stats["principal_nodes"] + half) // 2
        for k in range(half + 1):
            v = L[k] + acb(abs(H[k]).log(), arg[k])
            if fault == "skip_unwrap" and k > mid:
                v = v + acb(0, 2 * arb.pi())
            g.append(v)
    stats["seconds_sampling"] = round(t1 - t0, 2)
    stats["seconds_tracking"] = round(time.time() - t1, 2)
    return g, stats


def li_balls(model, r: arb, N: int, n_max: int, prec: int, rho: arb, M: float,
             fault: str | None = None, evaluated: tuple | None = None,
             ckpt: str | None = None) -> dict:
    """lambda_n, 1 <= n <= n_max, as real balls including the aliasing bound (A)."""
    g_up, stats = sample_upper(model, r, N, prec, fault=fault, evaluated=evaluated,
                               ckpt=ckpt)
    t0 = time.time()
    with prec_guard(prec):
        g = g_up + [g_up[N - k].conjugate() for k in range(N // 2 + 1, N)]
        W = acb.dft(g)                      # W_n = sum_k g_k e^{-2 pi i k n/N}
        Mb = q_arb(Q(M))
        x = (r / rho) ** N
        lam, worst_rad, imag_ok = [], 0.0, True
        rn, rho_inv, rho_n = arb(1), 1 / rho, arb(1)
        xx = x / (1 - x)
        for n in range(1, n_max + 1):
            rn = rn * r
            rho_n = rho_n * rho_inv                  # rho^{-n}, a ball by products
            v = arb(n) * W[n] / (arb(N) * rn)
            alias = arb(n) * Mb * rho_n * xx
            if not v.imag.contains(0):
                imag_ok = False
            re = v.real + arb(0, alias.upper())
            lam.append(re)
            worst_rad = max(worst_rad, float(re.rad()))
    stats["seconds_dft"] = round(time.time() - t0, 2)
    stats["imag_parts_contain_0"] = imag_ok
    stats["worst_radius"] = worst_rad
    return {"lambda": lam, "stats": stats}
