"""Check the case split that repairs steps (A) and (B/C) of the chain.

The independent audit (`audit/results/REPORT.md`) showed that the chain in
FAMILY-LIMIT.md section 2.1 is not valid as a chain:

  * step (A) reverses when its numerator  N = H m - q0 (m-1)/p  is negative;
  * the chain evaluates Phi at the cap m_max = q0 + floor(1/c) without any
    argument that Phi increases in m, and Phi does not always increase in m.

Both are repaired by a case split.  Write q0 = n-1, d = m - q0 >= 1,
D = m - c d, so Phi = N / D with D >= m - 1 >= q0 >= 2 > 0.

  (R1)  Phi(m) is a Mobius function of m with positive denominator on the whole
        admissible range, and the sign of its increment is the sign of
                        p c H - 1 - c (q0 - 1).
  (R2)  If Phi <= H, then Phi <= H (1 + W) at once, since W >= 0.
  (R3)  If Phi > H, then  Phi - H = [H c d - q0 (m-1)/p] / D > 0  forces
                p c H > q0 + q0 (q0 - 1)/d >= q0 + q0 c (q0 - 1) > 1 + c (q0 - 1),
        which is exactly the (R1) condition.  So in the only branch that can
        threaten a bound above H, Phi increases in m and moving to m_max is
        legitimate; there N > 0 (because Phi(m_max) >= Phi > H > 0 and D > 0),
        so step (A) has the right direction, and m_max - 1 >= 1/c.

This script checks (R1), (R3) and the two admissible counterexamples the audit
exhibited against steps 2 and 3 as written.

Run:  .venv/bin/python hunts/family_wall/chain_repair_check.py
"""
import math
import os
import sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from famlib import H  # noqa: E402


def phi(c, m, p, n):
    q0 = n - 1
    return (H * m - q0 * (m - 1) / p) / (m - c * (m - q0))


def numerator(c, m, p, n):
    q0 = n - 1
    return H * m - q0 * (m - 1) / p


def main():
    fails = 0

    # --- the audit's counterexample to step 2 (A) as written -----------------
    n, c, m, p = 3, 0.01, 3, 1
    lhs = phi(c, m, p, n)
    rhs = H * m / (m - 1) - (n - 1) / p
    print("audit counterexample to step (A):  n=3, c=0.01, m=3, p=1")
    print(f"  Phi                    = {lhs!r}")
    print(f"  claimed step-(A) bound = {rhs!r}")
    print(f"  numerator N            = {numerator(c, m, p, n)!r}  (negative -> (A) reverses)")
    print(f"  step (A) holds?          {lhs <= rhs}   (audit: it does not)")
    if lhs <= rhs:
        fails += 1

    # --- the audit's counterexample to step 3 (moving m to the cap) ---------
    n, c, p = 3, 0.01, 2
    m_here, m_max = 3, (n - 1) + int(math.floor(1.0 / c))
    print("\naudit counterexample to step 3:  n=3, c=0.01, p=2")
    print(f"  Phi at m=3        = {phi(c, m_here, p, n)!r}")
    print(f"  Phi at m_max={m_max}  = {phi(c, m_max, p, n)!r}   (Phi decreased in m)")
    claimed = H + H * c - (n - 1) / p
    print(f"  claimed bound H + Hc - (n-1)/p = {claimed!r}")
    print(f"  step 3 holds at m=3? {phi(c, m_here, p, n) <= claimed}   (audit: it does not)")
    if phi(c, m_here, p, n) <= claimed:
        fails += 1

    # --- (R1): the increment sign formula ------------------------------------
    print("\n(R1) sign of Phi(m+1) - Phi(m) equals sign of p c H - 1 - c(q0-1):")
    checked = 0
    for n in range(3, 40):
        q0 = n - 1
        for c in (1e-4, 1e-3, 3.3e-3, 1e-2, 0.05, 0.2, 0.5, 0.9):
            m_max = q0 + int(math.floor(1.0 / c))
            for p in (1.0, 2.0, 17.0, 300.0, 3000.0, 20000.0, 1e6):
                pred = p * c * H - 1 - c * (q0 - 1)
                for m in {n, n + 1, (n + m_max) // 2, m_max - 1}:
                    if not (n <= m < m_max):
                        continue
                    inc = phi(c, m + 1, p, n) - phi(c, m, p, n)
                    checked += 1
                    if abs(inc) > 1e-14 and (inc > 0) != (pred > 0):
                        fails += 1
                        print(f"  MISMATCH n={n} c={c} p={p} m={m} inc={inc} pred={pred}")
    print(f"  {checked} (n,c,p,m) increments checked, sign formula holds on all of them")

    # --- (R3): Phi > H forces the increasing branch --------------------------
    print("\n(R3) every admissible (n,c,m,p) with Phi > H satisfies p c H > 1 + c(q0-1):")
    seen = bad = 0
    for n in range(3, 60):
        q0 = n - 1
        for c in (1e-5, 1e-4, 1e-3, 3.3e-3, 1e-2, 0.05, 0.2, 0.5, 0.9, 0.999):
            m_max = q0 + int(math.floor(1.0 / c))
            for p in (1.0, 2.0, 17.0, 300.0, 3000.0, 20000.0, 1e6, 1e9):
                for m in {n, n + 1, (n + m_max) // 2, m_max - 1, m_max}:
                    if not (n <= m <= m_max):
                        continue
                    v = phi(c, m, p, n)
                    if v > H:
                        seen += 1
                        if not (p * c * H > 1 + c * (q0 - 1)):
                            bad += 1
                            print(f"  VIOLATION n={n} c={c} p={p} m={m} Phi={v}")
                        if numerator(c, m_max, p, n) <= 0:
                            bad += 1
                            print(f"  NUMERATOR<=0 AT CAP n={n} c={c} p={p}")
                        if not (m_max - 1 >= 1.0 / c):
                            bad += 1
                            print(f"  CAP TOO SMALL n={n} c={c}")
                        if phi(c, m_max, p, n) < v - 1e-14:
                            bad += 1
                            print(f"  NOT MAXIMAL AT CAP n={n} c={c} p={p} m={m}")
    print(f"  {seen} triples with Phi > H; violations = {bad}")
    fails += bad

    print(f"\nfailures: {fails}")
    return 0 if fails == 0 else 1


if __name__ == "__main__":
    sys.exit(main())
