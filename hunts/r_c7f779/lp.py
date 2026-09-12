"""The reconditioned certificate LP, its tail argument, and its verification.

    minimise   int mu       over  mu = sum_j x_j B_j,  x_j >= 0
    subject to G(s) >= f(s) for every s > 0,

with `G(s) = mu'(0+)/s^2 - Theta(s)/(2 s^4)` exactly (see `certificate.py`).

Three things make this solvable where run `37fb06a9`'s formulation was not.

1. **The class can hold the tail.**  `s^2 f(s)` has limsup
   `E_inf = 4 cos^2(sqrt2/2) sinh^2(1/2) = 0.6277706...`, attained on the
   critical `2*pi` lattice, so any certificate needs a positive `1/s^2` floor.
   Here that floor is `mu'(0+)`, a *linear functional of the variables*, and
   it is imposed as an explicit constraint rather than hoped for.

2. **The tail is closed by an inequality, not by absence of grid points.**
   For `s >= S`,

       s^2 [G(s) - f(s)]  >=  mu'(0+) - E(S) - Theta_sup / (2 S^2),

   with `E(S) = sup_{s >= S} s^2 f(s)` (bounded below by measurement and above
   by `E_inf + c/S`, `c` measured) and `Theta_sup = sup_s |Theta(s)|` bounded
   by the sum of `|jumps of mu'''|`.  So a feasible point plus one arithmetic
   check covers `(S, infinity)`.

3. **The rows are `O(1)`.**  Constraints are imposed on `s^2 G(s) >= s^2 f(s)`,
   whose coefficients are `B_j'(0) - Theta_j(s)/(2 s^2)`, bounded and of
   comparable size across the whole horizon.  The conditioning problem that
   killed the uniform-grid formulation is a scaling artefact of the `1/s^2`
   decay, and it disappears here.
"""

from __future__ import annotations

import math

import numpy as np
from scipy.optimize import linprog

import certificate as C


def envelope_constant(S_list=(200.0, 500.0, 2000.0, 8000.0),
                      n: int = 40001) -> dict:
    """Measure `c` in `sup_{s>=S} s^2 f(s) <= E_inf + c/S`, and `E(S)`."""
    rows = []
    for S in S_list:
        s = np.linspace(S, S + 8.0 * math.pi, n)
        v = s ** 2 * C.f_gas(s)
        sup = float(np.max(v))
        rows.append({"S": S, "sup_s2f": sup,
                     "excess_over_E_inf": sup - C.TAIL_ENVELOPE,
                     "c_est": (sup - C.TAIL_ENVELOPE) * S,
                     "max_abs_dev_from_envelope": float(
                         np.max(np.abs(v - C.f_envelope(s)))),
                     "dev_times_S": float(
                         np.max(np.abs(v - C.f_envelope(s)))) * S})
    return {"E_inf": C.TAIL_ENVELOPE, "rows": rows}


def constraint_grid(S: float, per_period: int = 48,
                    fine_to: float = 40.0, fine_step: float = 0.002,
                    lattice_pad: int = 12) -> np.ndarray:
    """`s`-points: fine near the origin, `per_period` per `2*pi` throughout,
    plus a cluster on each critical-lattice point `2*pi*d`, where `f` peaks."""
    fine = np.arange(fine_step, min(fine_to, S), fine_step)
    bulk = np.arange(fine_to, S, 2.0 * math.pi / per_period)
    d = np.arange(1, int(S / (2.0 * math.pi)) + 1)
    off = np.linspace(-0.30, 0.30, 2 * lattice_pad + 1)
    lat = (2.0 * math.pi * d[:, None] + off[None, :]).ravel()
    lat = lat[(lat > 0) & (lat < S)]
    return np.unique(np.concatenate([fine, bulk, lat]))


def margin(s: np.ndarray, eps: float) -> np.ndarray:
    """The pointwise slack demanded of `s^2 (G - f)`.

    It has to vanish like `s^2` at the origin -- `G - f` is bounded there, so
    `s^2 (G - f) -> 0` and a constant demand is infeasible for that reason
    alone, which is the first thing a naive margin gets wrong.
    """
    s = np.asarray(s, dtype=float)
    return eps * s ** 2 / (1.0 + s ** 2)


def solve(basis: C.CubicBasis, s: np.ndarray, mu1_floor: float,
          method: str = "highs", eps: float = 0.0,
          twoy: float = 1.0) -> dict:
    """`min int mu` s.t. `s^2 (G - f) >= eps` on `s`, and `mu'(0+) >= mu1_floor`.

    `eps > 0` buys pointwise slack, which is what turns a grid check into a
    statement about the whole half-line once a Lipschitz bound is in hand.
    """
    A = -basis.s2G_matrix(s)                       # -s^2 G(s) <= -s^2 f(s) - m
    b = -(s ** 2) * C.f_gas(s, twoy) - margin(s, eps)
    A = np.vstack([A, -basis.d1_zero[None, :]])    # -mu'(0) <= -floor
    b = np.concatenate([b, [-mu1_floor]])
    res = linprog(c=basis.mass, A_ub=A, b_ub=b, bounds=(0, None), method=method)
    out = {"status": int(res.status), "message": str(res.message),
           "n_constraints": int(A.shape[0]), "n_vars": int(basis.n),
           "method": method}
    if res.status == 0:
        x = np.asarray(res.x, dtype=float)
        out.update({"value": float(basis.mass @ x),
                    "mu1_zero": float(basis.d1_zero @ x),
                    "theta_sup_bound": basis.theta_bound(x),
                    "x": x})
    return out


def worst_violation(basis: C.CubicBasis, x: np.ndarray, S: float,
                    step: float = 2.0 * math.pi / 1500.0,
                    s_min: float = 1e-3, chunk: int = 40000,
                    twoy: float = 1.0) -> dict:
    """Dense independent re-evaluation of `s^2 (G - f)` on `(s_min, S]`.

    The grid is finer than, and offset from, the one constraints were imposed
    on, so it is not the same points read back.
    """
    s_all = np.arange(s_min, S, step) + 0.5 * step
    worst, arg = math.inf, None
    for i in range(0, len(s_all), chunk):
        s = s_all[i:i + chunk]
        r = (basis.s2G_matrix(s) @ x) - (s ** 2) * C.f_gas(s, twoy)
        j = int(np.argmin(r))
        if float(r[j]) < worst:
            worst, arg = float(r[j]), float(s[j])
    return {"worst_s2_slack": worst, "at_s": arg, "n_points": int(len(s_all))}


def violating_points(basis: C.CubicBasis, x: np.ndarray, S: float,
                     step: float, tol: float, cap: int = 4000,
                     chunk: int = 40000, twoy: float = 1.0) -> np.ndarray:
    """The `s` where `s^2(G - f) < -tol`, for constraint generation."""
    s_all = np.arange(1e-3, S, step) + 0.5 * step
    hits = []
    for i in range(0, len(s_all), chunk):
        s = s_all[i:i + chunk]
        r = (basis.s2G_matrix(s) @ x) - (s ** 2) * C.f_gas(s, twoy)
        m = r < -tol
        if m.any():
            hits.append(s[m])
    if not hits:
        return np.empty(0)
    h = np.concatenate(hits)
    if len(h) > cap:                      # keep the worst, spread over s
        r = (basis.s2G_matrix(h) @ x) - (h ** 2) * C.f_gas(h, twoy)
        h = h[np.argsort(r)[:cap]]
    return np.sort(h)


def _lip_f(a: float, b: float, twoy: float = 1.0, n: int = 4000,
           safety: float = 1.05) -> float:
    """A bound on `|d/ds [s^2 f(s)]|` over `[a, b]`.

    `s^2 f = s^2 max(0, D) - s^2 Kpair`, and `max(0, .)` is 1-Lipschitz, so
    `|(s^2 f)'| <= |(s^2 D)'| + |(s^2 Kpair)'|` pointwise, with both parts
    smooth -- central differences on them are accurate, unlike on `f` itself,
    whose derivative jumps where `D` changes sign.
    """
    s = np.linspace(a, b, n)
    h = 1e-6 * max(1.0, a)
    d1 = np.abs(((s + h) ** 2 * C.damage(s + h, twoy)
                 - (s - h) ** 2 * C.damage(s - h, twoy)) / (2 * h))
    d2 = np.abs(((s + h) ** 2 * C.kpair(s + h)
                 - (s - h) ** 2 * C.kpair(s - h)) / (2 * h))
    return safety * float(np.max(d1 + d2))


def verify_lipschitz(basis: C.CubicBasis, x: np.ndarray, S: float,
                     twoy: float = 1.0, base_step: float = 2e-3,
                     s_min: float = 1e-3, max_refine: int = 3) -> dict:
    """Cover `(s_min, S]` by intervals, not points.

    On a dyadic block `[a, b]`,
    `|R'| <= sup|Theta'|/(2a^2) + sup|Theta|/a^3 + Lip(s^2 f)`, with
    `sup|Theta| <= sum |J_k|` and `sup|Theta'| <= sum |J_k| v_k` (times two for
    the mirrored knots).  If the grid step `h` satisfies `h/2 * L < min_i R(s_i)`
    then `R > 0` on the whole block, so the block is covered rather than
    sampled.
    """
    j = basis.jump.T @ x
    T = float(2.0 * np.sum(np.abs(j)) - abs(j[0]))
    T1 = float(2.0 * np.sum(np.abs(j) * basis.v))
    blocks, a = [], s_min
    while a < S:
        b = min(2.0 * a, S)
        blocks.append((a, b))
        a = b
    out, worst_ratio, worst_R = [], 0.0, math.inf
    for (a, b) in blocks:
        L = T1 / (2.0 * a ** 2) + T / a ** 3 + _lip_f(a, b, twoy)
        step = base_step
        for _ in range(max_refine + 1):
            n = int(math.ceil((b - a) / step)) + 1
            n = min(n, 4_000_000)
            s = np.linspace(a, b, n)
            R = (basis.s2G_matrix(s) @ x) - (s ** 2) * C.f_gas(s, twoy)
            Rmin = float(np.min(R))
            h = (b - a) / (n - 1)
            if Rmin <= 0 or h * L / 2.0 < Rmin:
                break
            step = 1.9 * Rmin / L
        ratio = (h * L / 2.0) / Rmin if Rmin > 0 else math.inf
        worst_ratio = max(worst_ratio, ratio)
        worst_R = min(worst_R, Rmin)
        out.append({"a": a, "b": b, "L": L, "step": h, "R_min": Rmin,
                    "cover_ratio": ratio, "n": int(n)})
    return {"theta_sup": T, "theta_prime_sup": T1, "blocks": out,
            "worst_R_min": worst_R, "worst_cover_ratio": worst_ratio,
            "covered": bool(worst_ratio < 1.0 and worst_R > 0.0)}


def small_s_check(basis: C.CubicBasis, x: np.ndarray, s_min: float = 1e-3,
                  twoy: float = 1.0, n: int = 20001) -> dict:
    """`G - f` on `(0, s_min]`, where the `s^2` scaling says nothing."""
    s = np.linspace(1e-9, s_min, n)
    g = basis.G_matrix(s) @ x
    d = g - C.f_gas(s, twoy)
    return {"min_G_minus_f": float(np.min(d)), "at_s": float(s[np.argmin(d)]),
            "G_at_0": float(-basis.mass @ x),
            "f_at_0plus": float(C.f_gas(np.array([1e-12]), twoy)[0])}


def tail_certificate(basis: C.CubicBasis, x: np.ndarray, S: float,
                     c_env: float, twoy: float = 1.0) -> dict:
    """Does the feasible point cover `(S, infinity)` by the inequality above?"""
    mu1 = float(basis.d1_zero @ x)
    T = basis.theta_bound(x)
    E_S = C.TAIL_ENVELOPE_AT(twoy) + c_env / S
    margin = mu1 - E_S
    need_S = math.sqrt(T / (2.0 * margin)) if margin > 0 else math.inf
    return {"mu1_zero": mu1, "theta_sup_bound": T, "E_of_S": E_S,
            "margin_mu1_minus_E": margin, "S_used": S,
            "S_required": need_S, "tail_covered": bool(margin > 0 and S >= need_S),
            "s2_slack_lower_bound_beyond_S": margin - T / (2.0 * S ** 2)}


def run(W: float = 2.4, n_int: int = 30, S: float = 2000.0,
        c_env: float = 4.0, delta: float = 0.02, eps: float = 0.0,
        rounds: int = 8, verify_step: float = 2.0 * math.pi / 1500.0,
        method: str = "highs", twoy: float = 1.0,
        lipschitz: bool = True, budget: float | None = None) -> dict:
    """One full solve: LP, constraint generation, dense verify, tail check.

    `budget` is the number the value has to beat (`Shq(y)`); it defaults to
    `Shq(1/2)`, which is the T1 budget at the deepest depth.
    """
    basis = C.CubicBasis(W, n_int)
    mu1_floor = C.TAIL_ENVELOPE_AT(twoy) + c_env / S + delta + eps
    s = constraint_grid(S)
    log, sol = [], None
    for r in range(rounds):
        sol = solve(basis, s, mu1_floor, method=method, eps=eps, twoy=twoy)
        if sol["status"] != 0:
            log.append({"round": r, "status": sol["status"],
                        "message": sol["message"], "n_s": int(len(s))})
            break
        x = sol["x"]
        v = worst_violation(basis, x, S, step=verify_step, twoy=twoy)
        log.append({"round": r, "n_s": int(len(s)), "value": sol["value"],
                    "mu1_zero": sol["mu1_zero"],
                    "worst_s2_slack": v["worst_s2_slack"], "at_s": v["at_s"]})
        if v["worst_s2_slack"] >= 0.4 * eps or (eps == 0.0
                                                and v["worst_s2_slack"] >= 0.0):
            break
        add = violating_points(basis, x, S, verify_step, tol=0.4 * eps,
                               twoy=twoy)
        if len(add) == 0:
            break
        s = np.unique(np.concatenate([s, add]))
    bud = C.SHQ_HALF if budget is None else budget
    out = {"W": W, "n_int": n_int, "S": S, "delta": delta, "eps": eps,
           "c_env": c_env, "twoy": twoy, "budget": bud,
           "mu1_floor": mu1_floor, "rounds": log,
           "final": ({k: sol[k] for k in sol if k != "x"} if sol else None)}
    if sol and sol["status"] == 0:
        x = sol["x"]
        out["verify"] = worst_violation(basis, x, S, step=verify_step,
                                        twoy=twoy)
        out["small_s"] = small_s_check(basis, x, twoy=twoy)
        out["tail"] = tail_certificate(basis, x, S, c_env, twoy=twoy)
        out["transform_residual"] = C.transform_residual(basis, x)
        if lipschitz:
            out["lipschitz"] = verify_lipschitz(basis, x, S, twoy=twoy)
        out["x"] = [float(t) for t in x]
        out["value"] = sol["value"]
        out["below_budget"] = bool(sol["value"] < bud)
        out["ratio_to_budget"] = sol["value"] / bud
        out["implied_reserve_rho"] = 1.0 - sol["value"] / bud
        out["above_lattice_row"] = bool(sol["value"] > C.LATTICE_ROW)
    return out
