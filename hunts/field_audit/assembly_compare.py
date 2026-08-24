#!/usr/bin/env python3
"""Compare this laboratory's block assembly against the field's refined one.

Two assemblies map a floor `c` for the n-point functional to a bound:

  ours     (lean/bridge/Zeta23Ext/Bridge/Defs.lean, `Phi_n`)

      Phi_n(n, c, m, p) = (H - (n-1)(m-1)/(p m)) / (1 - c (m-(n-1))/m)

    with H = HD 1 = 3/2 - (1/sqrt 2) cot(1/sqrt 2), valid only while the
    linear block profile applies, i.e. while c (m - (n-1)) <= 1, so
    m <= (n-1) + floor(1/c).

  refined  (trmdy/zeta-simple-zeros-673137 `src/zeta_ext/design.py`, after
            tawanerguo-cn; Phi_m trace-energy envelope + window-in-frame
            pressure counting)

      A       = c (m - q),   q = n - 1
      Phi_m(A)= 2 sqrt((m-1) A / m) - 1 + A/m          for A >= m/(m-1)
      bound(m)= (m H - (m-q) q / p) / (m - Phi_m(A))

    with no cap on m.

The point of the script is the third column: what our own already-established
floors would give under the refined assembly, with no new search.

Run:  .venv/bin/python hunts/field_audit/assembly_compare.py
"""

from __future__ import annotations

from flint import arb, ctx, fmpq

ctx.prec = 300

_R = arb(1) / arb(2).sqrt()
H = arb(3) / 2 - _R * (_R.cos() / _R.sin())   # HD 1


def phi_linear(n: int, c: fmpq, m: int, p: int) -> arb:
    """Our `Phi_n`.  Caller must respect the cap c(m-(n-1)) <= 1."""
    return (H - (arb(n) - 1) * (arb(m) - 1) / (arb(p) * arb(m))) / (
        1 - arb(c) * (arb(m) - (arb(n) - 1)) / arb(m)
    )


def phi_refined(n: int, c: fmpq, m: int, p: int) -> arb:
    """The field's refined assembly.  No cap on m."""
    q = n - 1
    a = arb(c) * (m - q)
    envelope = 2 * (arb(fmpq(m - 1, m)) * a).sqrt() - 1 + a / m
    return (m * H - (m - q) * q * arb(fmpq(1, p))) / (m - envelope)


def optimise(fn, n: int, c: fmpq, p: int, m_max: int) -> tuple[arb, int]:
    best = best_m = None
    for m in range(n, m_max + 1):
        value = fn(n, c, m, p)
        if best is None or value > best:
            best, best_m = value, m
    assert best is not None and best_m is not None
    return best, best_m


CASES = [
    ("ours, seven-point", 7, fmpq(34697, 10**7), 3400),
    ("ours, eight-point", 8, fmpq(41763, 10**7), 3200),
    ("trmdy, seven-point", 7, fmpq(891, 200_000), 2736),
    ("trmdy, nine-point", 9, fmpq(15211, 2_500_000), 2500),
]


def main() -> int:
    print("H = HD 1 =", H.str(22))
    print()
    for label, n, c, p in CASES:
        cap = (n - 1) + int(1 / fmpq(c))          # our linear-profile cap
        lin, m_lin = optimise(phi_linear, n, c, p, cap)
        ref, m_ref = optimise(phi_refined, n, c, p, 2000)
        print(f"{label}:  c = {c}, p = {p}, our cap m <= {cap}")
        print(f"    our assembly      {lin.str(19)}   at m = {m_lin}")
        print(f"    refined assembly  {ref.str(19)}   at m = {m_ref}")
        print(f"    gain              {(ref - lin).str(10)}")
        print()
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
