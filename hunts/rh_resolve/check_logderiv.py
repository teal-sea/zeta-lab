"""Spot checks for EQUIVALENCE.md. Not a proof, and not an enclosure.

Checks:
  * explicit L matches a difference quotient at s = 2
  * closed form of b matches -gamma/2 - 1 + log(2) + log(pi)/2
  * -2b equals 2 + gamma - log(4 pi)
  * N(1) < 0 and N' < 0 on a real grid v >= 1, for the f_1 bound
  * Re L at 0.8+10i agrees with a truncated Poisson sum to 1e-3
  * the positive Gaussian-mixture witness has a non-real cosine zero
"""

from __future__ import annotations

from mpmath import (
    ceil,
    cos,
    diff,
    exp,
    euler,
    fabs,
    findroot,
    log,
    mp,
    pi,
    psi,
    quad,
    zeta,
    mpf,
    mpc,
)


def explicit_L(s):
    return (
        1 / s
        + 1 / (s - 1)
        - log(pi) / 2
        + psi(0, s / 2) / 2
        + zeta(s, derivative=1) / zeta(s)
    )


def main() -> None:
    mp.dps = 25
    s = mpc(2)
    quot = diff(lambda z: __import__("zeta.core", fromlist=["xi"]).xi(z), s)
    # xi imported inside to keep matplotlib out; zeta.core.xi is the lab function
    from zeta.core import xi

    quot = diff(xi, s) / xi(s)
    gap = abs(quot - explicit_L(s))
    print("explicit_L_gap_at_2", gap)
    if gap > mpf("1e-18"):
        raise SystemExit("explicit L disagrees with xi difference quotient")

    b = -euler / 2 - 1 + log(2) + log(pi) / 2
    target = 2 + euler - log(4 * pi)
    print("b", b)
    print("minus_2b_minus_target", -2 * b - target)
    if abs(-2 * b - target) > mpf("1e-20"):
        raise SystemExit("b identity failed")

    # N(v) numerator of (log f_1)'' + 70, cleared. Must stay negative for v >= 1.
    def N(v):
        v = mpf(v)
        return -64 * pi**3 * v**3 + 472 * pi**2 * v**2 - 1080 * pi * v + 630

    def Np(v):
        v = mpf(v)
        return -8 * pi * (24 * pi**2 * v**2 - 118 * pi * v + 135)

    print("N(1)", N(1), "Np(1)", Np(1))
    if N(1) >= 0 or Np(1) >= 0:
        raise SystemExit("f_1 bound failed at v=1")
    worst = max(Np(1 + mpf(i) / 20) for i in range(0, 40))
    print("max_Np_on_grid", worst)
    if worst >= 0:
        raise SystemExit("N' changed sign on the grid")

    from zeta.zeros import first_n_zeros

    sig, t = mpf("0.8"), mpf(10)
    L = explicit_L(mpc(sig, t))
    zs = first_n_zeros(200)
    d = sig - mpf("0.5")
    pois = sum(
        d / (d * d + (t - g) ** 2) + d / (d * d + (t + g) ** 2) for g in zs
    )
    print("ReL", L.real, "poisson_head", pois, "gap", L.real - pois)
    if abs(L.real - pois) > mpf("1e-3"):
        raise SystemExit("Poisson spot check failed")

    def phi(u):
        u = mpf(u)

        def bump(c, width):
            return exp(-((u - c) ** 2) / width)

        return (
            bump(mpf("0.3"), mpf("0.02"))
            + bump(mpf("-0.3"), mpf("0.02"))
            + mpf("0.3")
            * (bump(mpf(2), mpf("0.05")) + bump(mpf(-2), mpf("0.05")))
        )

    def H(z):
        z = mpc(z)
        return quad(lambda u: phi(u) * cos(z * mpf(u)), [0, mpf(8)])

    root = findroot(H, mpc("1.62", "0.64"))
    resid = abs(H(root))
    print("witness_root", root, "resid", resid, "phi0", phi(0))
    if abs(root.imag) < mpf("1e-3") or resid > mpf("1e-12") or phi(0) <= 0:
        raise SystemExit("positive-weight witness failed")
    print("ok")


if __name__ == "__main__":
    main()
