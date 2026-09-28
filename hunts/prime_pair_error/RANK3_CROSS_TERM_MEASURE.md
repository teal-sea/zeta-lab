# Measuring RANK3_ROUTE_D.md's cross term Sigma_cross(q)

RANK3_ROUTE_D.md's exact identity (D7) splits the coprime-driven part of
\(U_{(q)}\), summed over the reduced residues \(a\bmod q\), into a diagonal
piece \(\Sigma_{\rm diag}(q)=\phi(q)\sum_b^*T(q,b)\) and a cross term
\[
 \Sigma_{\rm cross}(q)=\sum_{b\ne b'\bmod q}^*c_q(b-b')X(b,b'),
\]
with \(c_q\) the Ramanujan sum and \(X(b,b')\) the exact bilinear cross
term (D6). Section 3 of that document proves only the cancellation-free
ceiling \(|\Sigma_{\rm cross}(q)|\le\phi(q)(\phi(q)-1)\sum_b^*T(q,b)\) and
states plainly that whether the true \(\Sigma_{\rm cross}(q)\) sits near
\(0\) or near that ceiling "is not determined by UPPER_BOUND.md or
RESULTS.md — both are consistent with the exact identity (D7)." This
document reports a direct numerical measurement of \(\Sigma_{\rm cross}(q)\)
at a ladder of moduli and cutoffs, from `rank3_cross_term_probe.py`, writing
`results_rank3_cross_term_probe.json`.

## Method

For each \(q\in\{2,3,5,6,7,10,11,13\}\) and each
\(N\in\{10^3,3\times10^3,10^4,3\times10^4,10^5,3\times10^5,10^6\}\):

1. \(\Lambda(n)\) for \(n\le N\) is read from `probe.von_mangoldt`, the
   smallest-prime-factor sieve already used by `residue.py` and `probe.py`
   in this hunt.
2. \(\Delta(t;q,b)=\psi(t;q,b)-t/\phi(q)\) is built by a cumulative sum of
   \(\Lambda\) restricted to each reduced residue class, exactly as defined
   in RANK3_ROUTE_D.md Section 1.
3. \(T(q,b)\) and \(X(b,b')\) are the exact finite sums (D5), (D6) — no
   approximation, no truncation of the sum over \(t\).
4. \(c_q(k)\) is computed from its defining exponential sum over the
   \(\phi(q)\) reduced residues (UPPER_BOUND.md Section 2).
5. \(\Sigma_{\rm cross}(q)=\sum_{b\ne b'}^*c_q(b-b')X(b,b')\), computed
   directly from the assignment's own definition, not assembled from a
   separate identity.

Two ratios are recorded at each \((q,N)\):

* `ratio_cross_over_diag` = \(\Sigma_{\rm cross}(q)/(\phi(q)\sum_b^*T(q,b))\)
  — the exact quantity the task asks for.
* `ratio_cross_over_ceiling` = \(\Sigma_{\rm cross}(q)/(\phi(q)(\phi(q)-1)\sum_b^*T(q,b))\)
  — the same numerator against the proved (D8) ceiling instead of the
  diagonal term; the two ratios are related by a factor of \(\phi(q)-1\)
  and are reported separately because the task asks for the comparison
  against both quantities.

At \(q=2\), \(\phi(q)=1\): there is only one reduced residue, so the sum
over \(b\ne b'\) is empty, \(\Sigma_{\rm cross}(2)\equiv0\) identically (not
a numerical coincidence — the same structural fact (D7) records at
\(q=1\)), and `ratio_cross_over_ceiling` is undefined (division by
\(\phi(q)(\phi(q)-1)=0\)); both are recorded as such in the JSON.

## Cross-checks (before trusting any ratio)

Reusing the hunt's own von Mangoldt machinery rather than re-deriving one,
as the task requires, still leaves open whether that machinery is right;
three independent checks are run and recorded in the JSON's
`cross_checks` block:

* **\(\Lambda(n)\), two methods.** `probe.von_mangoldt`'s sieve against a
  direct enumeration of prime powers via `sympy.primerange` (the same
  second method `rank3_bdh_probe.py` and `rank3_fourth_moment_probe.py`
  already use in this hunt) — measured max abs difference `0.0` up to
  \(n=50000\).
* **\(c_q(k)\), two methods.** The defining exponential sum against the
  classical closed form \(c_q(k)=\mu(q/g)\phi(q)/\phi(q/g)\), \(g=\gcd(q,k)\),
  for every \(q\in\{2,3,5,6,7,10,11,13\}\) and every \(k\) in \([-q,q]\) —
  measured max abs difference \(1.57\times10^{-14}\) (floating-point
  roundoff).
* **\(T(q,b)\), two independent code paths.** The partial-sum formula (D5)
  against an explicit finite convolution of
  \(d_b(n)=\Lambda(n)\mathbf1_{n\equiv b(q)}-1/\phi(q)\) with the constant
  sequence \(1\) on \(1..N\) (the same convolution RANK3_ROUTE_D.md
  Section 2 sets up before reading off (D5)), taking the sum of squares of
  the resulting coefficients (Parseval on the explicit trigonometric
  polynomial) at \(q=3\), \(N=500\) — measured max abs difference
  \(9.1\times10^{-11}\) (floating-point roundoff on sums of size
  \(\sim10^5\)).
* **Gram/Cauchy-Schwarz consistency.** \(|X(b,b')|\le\sqrt{T(q,b)T(q,b')}\)
  must hold at every \((q,N,b,b')\) since \(X\) is a Gram matrix entry
  (RANK3_ROUTE_D.md Section 2); `max_cauchy_schwarz_violation` is recorded
  per run and is \(\le0\) (i.e. no violation) throughout.

All four checks pass at or near floating-point precision; none is a proof
that the script is free of every possible error, but they are independent
of each other and of the main computation, and none turned up a
disagreement.

## What was measured

Full numbers are in `results_rank3_cross_term_probe.json` (56 rows, one per
\((q,N)\) pair). The measured `ratio_cross_over_ceiling` ranges over
approximately \([-0.254,\ 0.426]\) across every \((q,N)\) in the ladder, and
is below \(0.1\) in absolute value for \(q\ge11\) at every cutoff measured.
The measured `ratio_cross_over_diag` is larger (it omits the extra factor
\(\phi(q)-1\)) but still stays under \(0.43\) in absolute value throughout,
and is well under \(0.15\) for \(q\ge7\) at the largest cutoffs measured.
\(\Sigma_{\rm cross}(q)\) changes sign across the ladder at several moduli
(e.g. \(q=3,6,7,10\) all have at least one negative entry): it is, as
RANK3_ROUTE_D.md Section 3 already notes on general grounds, "a real number
of either sign," not a one-signed quantity trending toward the ceiling.

**Reading against the two candidate weights.** RANK3_ROUTE_D.md Section 5
contrasts a diagonal-only weight \(\mu(q)^2/\phi(q)\) (obtained if
\(\Sigma_{\rm cross}(q)\) is discarded as negligible, i.e. the ratio to the
diagonal term is treated as \(\approx0\)) against the proved
cancellation-free weight \(2\mu(q)^2\) (obtained if no cancellation at all
is assumed, i.e. the ratio to the ceiling is treated as \(\approx1\)). At
every \((q,N)\) measured here, `ratio_cross_over_ceiling` stays well under
\(1/2\) — closer to \(0\) than to \(1\) — and in most rows well under
\(0.1\). **This measurement is closer to the diagonal-only picture
(\(\Sigma_{\rm cross}(q)\) small relative to its proved ceiling) than to
the cancellation-free ceiling being approached.** It is emphatically not,
by itself, a demonstration that \(\Sigma_{\rm cross}(q)=o(\Sigma_{\rm
diag}(q))\) as \(q,N\to\infty\): the ladder here stops at \(N=10^6\) and
\(q=13\), the ratios do not shrink monotonically as \(N\) grows (e.g. \(q=3\)
goes \(0.085\to0.426\to0.382\to0.131\to0.288\to-0.252\to0.241\) across the
seven cutoffs), and nothing here bounds the ratio uniformly in \(q\) or
proves any rate. A finite measurement at eight moduli and seven cutoffs
does not decide an asymptotic question, and this document does not claim
it does — it reports where the actual numbers landed, which is
substantially inside the proved envelope rather than near its edge, and
leaves whether that persists as \(q\) and \(N\) grow exactly as open as
RANK3_ROUTE_D.md already says it is.

## Reproducing

```
/opt/zeta-venv/bin/python hunts/prime_pair_error/rank3_cross_term_probe.py
```

Wall time on this run: 3.9s (the reported `seconds_total` in the JSON);
peak memory is dominated by a handful of length-\(N\) float64 arrays per
residue, negligible at these cutoffs.
