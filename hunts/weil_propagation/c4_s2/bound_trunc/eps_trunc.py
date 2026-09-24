"""bound_trunc/: the prolate-mode truncation error of Delta_T, the interface of BRIEF.md.

    eps_trunc(c, N, nvec, S, Kmax) -> flint.arb

**No finite bound is derived** (DERIVATION.md s1.3: outcome 4 for this
folder). The function therefore returns the whole-line ball arb("inf"), the
only enclosure this folder can stand behind, and `eps_trunc.json` carries
"eps_upper": null with the reason for every stored build at every c. Anything
downstream that adds it to another bound gets a ball with no finite upper
end, so no count can be read off it by accident.

Two further things live here because RESULTS.md quotes them:

- `responses(c, N)`: the measured mode and quadrature responses
  ||Delta_T(a) - Delta_T(b)||_2 between stored builds at the same (c, N), read
  from checker/'s snapshot (T_inf is the same matrix in every build, so the
  difference of T_S is the difference of Delta_T). They fix the necessary
  condition any candidate bound must meet, by the triangle inequality through
  Delta_T_exact:
      ||Delta_T(a) - Delta_T(b)|| <= ||Delta_T(a) - Delta_T_exact|| + ||Delta_T_exact - Delta_T(b)||
                                  <= eps_trunc(a) + eps_quad(a) + eps_trunc(b) + eps_quad(b).
- `window_tail(c, N, sigma)`: sup over unit v of (1/2 pi) int_{|s| > sigma} |f^(s)|^2 ds
  for f = sum v_n U_n, the largest eigenvalue of that compression, in closed
  form through Si and Ci (mpmath). DERIVATION.md s1.3, mechanism 3: the size
  a bound of the only available shape would have, with the heuristic
  sigma_n = 2 n / sqrt3 (not a bound on anything).
"""

from __future__ import annotations

import functools
import json
import math
import os
import sys

import numpy as np
from flint import arb
from mpmath import mp

HERE = os.path.dirname(os.path.abspath(__file__))
C4S2 = os.path.normpath(os.path.join(HERE, ".."))
SNAPSHOT = os.path.join(C4S2, "checker", "checker_ts_snapshot.json")
OUT = os.path.join(HERE, "eps_trunc.json")

CELLS = ("2.2", "2.5", "2.9")
#: the stored builds (nvec, S) per N, as BRIEF.md lists them
BUILDS = {
    8: [(80, 1200)],
    16: [(80, 1200), (80, 1600), (120, 1200), (120, 1600), (160, 1600)],
    32: [(200, 2400), (240, 2400), (280, 2266), (319, 2633), (364, 3060)],
}

REASON = ("No finite bound derived (DERIVATION.md s1.3, outcome 4). The truncation error is "
          "E_n = tau_f(R_n - Pi'_n) (identity A), a difference of two traces that are each +infinity "
          "(Lemma 1), so it can only be bounded through a cancellation. The part carried by Theta "
          "closes for a degree truncation (Lemma 2); the Sonin overlap, governed by S_inf F (1-P) D on "
          "the prolate tail with no decay in n, does not close: it needs a frequency-by-frequency "
          "localization of ran S_inf that is not available. Even closed with a density of order one, "
          "a bound of this shape is about window_tail(c, N, 2n/sqrt3), 0.098 to 1.0 on these builds (size_if_closed).")
BLOCKING_STEP = "DERIVATION.md s1.3, mechanism 2 (the Sonin overlap Pi_S Theta W_n)"


def kmax_for(nvec: int) -> int:
    """two_adic.ta_prolate.kmax_for, restated so that importing this module
    does not pull in kernel/'s mpmath prolate machinery; a test pins equality."""
    return max(10, int(math.ceil(math.log2(max(nvec - 1, 1) ** 2 / (2 * math.pi)))))


def known_build(c, N, nvec, S, Kmax) -> bool:
    return (str(c) in CELLS and int(N) in BUILDS and (int(nvec), int(S)) in BUILDS[int(N)]
            and int(Kmax) == kmax_for(int(nvec)))


def eps_trunc(c, N, nvec, S, Kmax) -> arb:
    """Upper bound on ||Delta_T_exact - Delta_T^(nvec)||_2 on the (2N+1)-dim window space.

    Returns arb("inf") (no finite upper end): no bound is derived. Raises
    ValueError for a build that is not one of the stored ones."""
    if not known_build(c, N, nvec, S, Kmax):
        raise ValueError(f"not a stored build: c={c}, N={N}, nvec={nvec}, S={S}, Kmax={Kmax}")
    return arb("inf")


# ------------------------------------------------------------ measured responses


def _snapshot():
    with open(SNAPSHOT) as fh:
        return json.load(fh)


def stored_T_S(snap, c, N, nvec, S) -> np.ndarray:
    M = np.array(snap["T_S"][f"{c}|{int(N)}|40|{int(nvec)}|{int(S)}"], dtype=float)
    return (np.tril(M) + np.tril(M, -1).T)  # the symmetric matrix numpy's eigh reads (checker/ s7.9)


def responses(c, N, snap=None) -> list[dict]:
    """||T_S(a) - T_S(b)||_2 for every pair of stored builds at this (c, N)."""
    snap = snap or _snapshot()
    out = []
    bl = BUILDS[int(N)]
    for i in range(len(bl)):
        for j in range(i + 1, len(bl)):
            a, b = bl[i], bl[j]
            d = stored_T_S(snap, c, N, *a) - stored_T_S(snap, c, N, *b)
            out.append({"a": list(a), "b": list(b), "norm2": float(np.linalg.norm(d, 2))})
    return out


# ------------------------------------------------------------ mechanism 3


def _half_line(L, ka, kb, sigma):
    """int_sigma^inf sin^2(sL/2) / ((s - ka)(s - kb)) ds (mpmath), any sigma not equal to ka, kb.

    sin^2(sL/2) = sin^2((s - k)L/2) because kL is 2 pi times an integer. Antiderivatives,
    valid on both sides of u = 0 (the integrands are regular there):
    (1 - cos Lu)/(2u):   G(u) = (log|u| - Ci(L|u|))/2;
    (1 - cos Lu)/(2u^2): H(u) = -(1 - cos Lu)/(2u) + (L/2) Si(Lu), H(inf) = L pi/4."""
    if ka == kb:
        u0 = sigma - ka
        return L * mp.pi / 4 + (1 - mp.cos(L * u0)) / (2 * u0) - L * mp.si(L * u0) / 2
    ua, ub = sigma - ka, sigma - kb
    Ga = (mp.log(abs(ua)) - mp.ci(L * abs(ua))) / 2
    Gb = (mp.log(abs(ub)) - mp.ci(L * abs(ub))) / 2
    return (Gb - Ga) / (ka - kb)


def window_tail_matrix(c, N, sigma, dps: int = 30):
    """M_sigma[k, l] = (1/2 pi) int_{|s| > sigma} V^_k V^_l ds, V^_k(s) = 2 L^{-1/2} sin(sL/2)/(s - kappa_k)."""
    with mp.workdps(dps):
        L = mp.log(mp.mpf(str(c)))
        sig = mp.mpf(sigma)
        kap = [2 * mp.pi * n / L for n in range(-N, N + 1)]
        if sig <= 0 or any(sig == abs(k) for k in kap):
            raise ValueError("sigma must be positive and differ from every 2 pi n / L")
        n = 2 * N + 1
        M = np.zeros((n, n))
        for i in range(n):
            for j in range(i, n):
                v = _half_line(L, kap[i], kap[j], sig) + _half_line(L, -kap[i], -kap[j], sig)
                M[i, j] = M[j, i] = float(2 * v / (mp.pi * L))
        return M


@functools.lru_cache(maxsize=None)
def window_tail(c, N, sigma) -> float:
    return float(np.linalg.eigvalsh(window_tail_matrix(c, N, sigma))[-1])


def sigma_heuristic(nvec) -> float:
    return 2.0 * nvec / math.sqrt(3.0)


# ------------------------------------------------------------ the JSON


def entries(snap=None) -> list[dict]:
    out = []
    for c in CELLS:
        for N, bl in BUILDS.items():
            for nvec, S in bl:
                K = kmax_for(nvec)
                out.append({"c": c, "N": N, "nvec": nvec, "S": S, "Kmax": K, "eps_upper": None,
                            "grade": "no bound: outcome 4 for bound_trunc/ (ordinary arguments, unreviewed)",
                            "assumptions": [], "blocking_step": BLOCKING_STEP, "reason": REASON,
                            "size_if_closed": {"sigma_heuristic": sigma_heuristic(nvec),
                                               "window_tail": window_tail(c, N, sigma_heuristic(nvec)),
                                               "note": "a heuristic size, not a bound on anything"}})
    return out


def main():
    snap = _snapshot()
    doc = {"meta": {"interface": "BRIEF.md: eps_trunc(c, N, nvec, S, Kmax) -> flint.arb",
                    "snapshot_digest": snap["meta"]["ts_inputs_digest"],
                    "responses_note": ("||T_S(a) - T_S(b)||_2 between stored builds at equal (c, N): "
                                       "a lower bound on eps_trunc(a) + eps_quad(a) + eps_trunc(b) + eps_quad(b)")},
           "entries": entries(snap),
           "responses": {f"{c}|{N}": responses(c, N, snap) for c in CELLS for N in BUILDS if len(BUILDS[N]) > 1}}
    with open(OUT, "w") as fh:
        json.dump(doc, fh, indent=1)
    print("wrote", OUT)


if __name__ == "__main__":
    main()
