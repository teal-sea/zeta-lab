# A negative third discrepancy does not force a proportion gain

Under the finite signed-vector hypotheses of [FINITE-THEOREM.md](FINITE-THEOREM.md),
matched second and third moment limits alone cannot improve the second-moment
counting proportion. This remains true when the third discrepancy is strictly
negative. The obstruction uses two allowed nonreal pairs, including the optional
orthogonality condition. It is an original finite construction; novelty has not
been established.

More precisely, for every `1 < c_2 < 2` and every `d > 0`, there is a sequence of
the allowed configurations for which

    N -> infinity,
    M_2/N -> c_2,
    M_3/N -> 3c_2 - 2 - d,
    s/N -> 2 - c_2.

Thus the normalized third discrepancy tends to `-d`, while the limiting simple
proportion equals the second-moment lower bound. This is a theorem about the
finite hypotheses. It does not construct a zero configuration of zeta or rule
out stronger estimates using additional information about its zeros.

## 1. The three-dimensional block

For `b > 0`, take an orthonormal basis `e_1,e_2,e_3` and the two pairs

    g_1 = sqrt(1+b/2) e_1,    h_1 = sqrt(b/2) e_3,
    g_2 = sqrt(1+b/2) e_2,    h_2 = sqrt(b/2) e_3.

Both multiplicities are one. For each pair,
`||g_j||^2 - ||h_j||^2 = 1` and `g_j` is orthogonal to `h_j`.
There are no simple or multiple real vectors in this block. Consequently

    A_b = 2(g_1 tensor g_1 - h_1 tensor h_1)
          + 2(g_2 tensor g_2 - h_2 tensor h_2)
        = diag(b+2, b+2, -2b),

    N_b = 4,    s_b = 0.

Its traces are

    M_1 = 4,
    M_2 = 6b^2 + 8b + 8,
    M_3 = -6b^3 + 12b^2 + 24b + 16,
    M_4 = 18b^4 + 16b^3 + 48b^2 + 64b + 32.

In particular, its third discrepancy and its slack in quadratic counting are

    Delta_3 = M_3 - 3M_2 + 2N_b = -6b^2(b+1) < 0,
    E_b = M_2 - 2N_b + s_b = 6b^2 + 8b > 0.

The discrepancy grows cubically while the slack grows quadratically. An exact
comparison, valid already for `b >= 0`, is

    -Delta_3 - (b/2) E_b = b^2(3b+2) >= 0.

A single orthogonal signed pair has zero third discrepancy at multiplicity one.
The shared negative direction of these two pairs is what permits the negative
cubic term.

## 2. A sequence attaining the quadratic limiting proportion

Fix `c_2` and `d` as in the statement. For positive integers `L`, put

    r_L = floor((c_2-1)L/2),
    s_L = L - 2r_L,
    b_L = (dL/6)^(1/3).

Here `0 <= 2r_L <= L`, so the counts are admissible. On mutually orthogonal
directions take `s_L` simple unit vectors and `r_L` multiple unit vectors, each
of multiplicity two. This baseline has

    N_0 = L,
    M_2,0 = L + 2r_L,
    Delta_3,0 = 0,
    M_2,0 - 2N_0 + s_L = 0.

Add the block `A_(b_L)` on three further orthogonal directions. The combined
configuration has

    N_L = L+4,
    M_2,L = L + 2r_L + 6b_L^2 + 8b_L + 8,
    Delta_3,L = -6b_L^3 - 6b_L^2 = -dL - 6b_L^2.

Since `b_L` has order `L^(1/3)`, division by `N_L` gives

    M_2,L/N_L -> c_2,
    Delta_3,L/N_L -> -d,
    s_L/N_L -> 2-c_2.

The third-moment limit in the headline follows from the defining identity for
`Delta_3`. The normalized counting slack is exactly

    (M_2,L - 2N_L + s_L)/N_L = (6b_L^2+8b_L)/(L+4) -> 0.

Meanwhile

    M_4,L/N_L >= 18b_L^4/(L+4) -> infinity.

The finite fourth-moment condition in the quartic theorem therefore excludes
precisely this kind of construction. It is a substantive hypothesis.

## 3. Consequence for the Montgomery-Taylor constants

Take `c_2 = k+1/2`, where `k = cot(1/sqrt(2))/sqrt(2)`, and take

    d = -(6k-5)(6k^2+6k-1)/24 > 0.

These constants satisfy the restrictions above by Section 8 of
[FINITE-THEOREM.md](FINITE-THEOREM.md). The construction then matches both the
second moment and the triangle third moment in that note, yet its limiting
simple proportion is exactly `2-c_2`.

Consequently no conclusion of the form `liminf s/N >= 2-c_2+epsilon`, with
`epsilon > 0`, follows from those two limits and the finite signed-vector
hypotheses alone. A truncated score cannot produce such a theorem either:
the two moment limits are compatible with this exact counterexample. A mixed
moment estimate can still provide additional information that this construction
does not constrain.

## 4. Verification and formal scope

[ThirdMomentObstruction.lean](ThirdMomentObstruction.lean) checks the square-root
norm difference, all four eigenvalue power-sum identities, the discrepancy and
slack formulas, their strict signs, and the cubic-versus-slack inequality. AXLE
checked the full file with Lean 4.33.0 on 2026-09-05, with no failed declarations,
errors, or warnings. Every printed declaration uses only `propext`,
`Classical.choice`, and `Quot.sound`.

- Request: `660ac38d-cc8e-4a7c-94e1-6dd2ea885db3`.
- Lean source SHA-256:
  `61d0bc606ceb3a04dc623c83bb10af895cc83a32f640c3c575f16731627b7b69`.
- Formal scope: scalar power sums and inequalities. The vector construction,
  its direct-sum interpretation, and the asymptotic limit proof above are
  ordinary mathematical proofs, not Lean proofs.

An independent symbolic matrix calculation also passed. To reproduce it from
the repository root:

```bash
.venv/bin/python - <<'PY'
import sympy as sp
b = sp.symbols('b', positive=True)
a = sp.diag(b+2, b+2, -2*b)
m = [sp.expand(sp.trace(a**j)) for j in range(1, 5)]
assert m == [4, 6*b**2+8*b+8, -6*b**3+12*b**2+24*b+16,
             18*b**4+16*b**3+48*b**2+64*b+32]
assert sp.expand(m[2]-3*m[1]+8) == -6*b**3-6*b**2
assert sp.expand(-(m[2]-3*m[1]+8)-b*(m[1]-8)/2) == 3*b**3+2*b**2
print('Exact matrix trace checks passed.')
PY
```
