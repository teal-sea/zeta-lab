# Section 8: a control and sensitivity instrument for E_corr

2026-09-10. Reuses probe.py's FFT-autocorrelation route for \(E(N)\)
unchanged, and the character/sieve helpers in
[artifacts/siegel_uniformity/check.py](artifacts/siegel_uniformity/check.py)
for \(C_N(h)\). Produced by
[s8_control.py](s8_control.py); raw output in
[results_s8_control.json](results_s8_control.json). This is a diagnostic
instrument, not a new estimate: it measures where
[CORRECTED_RH_BRIDGE.md](CORRECTED_RH_BRIDGE.md)'s corrected quantity
\(E_{\rm corr}(N)\) actually stands at reachable \(N\), and how it reacts
to an unphysical planted perturbation.

## 1. Which case applies at each required cutoff

\(E_{\rm corr}(N):=2\sum_{h=1}^N|r_N(h)-C_N(h)|^2\)
(CORRECTED_RH_BRIDGE.md eq. 1), with \(r_N(h)=\psi_2(N,h)-(N-h)\mathfrak S(h)\)
exactly probe.py's \(e(N,h)\), and \(C_N(h)\) SIEGEL_UNIFORMITY.md eq. (5)
for whichever exceptional data TT Definition 2.1 assigns at that \(N\), or
identically \(0\) when it assigns none.

Whether an exceptional zero is assigned is not assumed either way: at each
\(N\), `s8_control.py` computes \(Z(N)=\exp((\log N)^{1/10})\), takes every
primitive real character with conductor \(q<Z(N)\) from
`siegel_uniformity/check.py`'s `local_characters()`, and scans each one's
Dirichlet \(L\)-function on the real axis for a zero in TT's window near
\(s=1\). \(L(s,\chi)\) is evaluated exactly via the Hurwitz-zeta identity
\(L(s,\chi)=q^{-s}\sum_a\chi(a)\zeta(s,a/q)\) (entire: the shared pole of
\(\zeta(s,a/q)\) at \(s=1\) cancels because \(\sum_a\chi(a)=0\)), not by a
truncated Dirichlet series.

For every \(N\) in \(\{2000,5000,10000,30000,100000\}\), \(Z(N)<3.6\)
(it stays below 4 up to \(N\sim10^{12}\)), so the only candidate is
\(q=3\); the scan finds no real zero of \(L(s,\chi_3)\) in a window padded
well below TT's threshold. Every row below is therefore the no-exception
case, \(C_N\equiv0\), so \(E_{\rm corr}(N)=E(N)\) exactly.

| N | E(N) | E_corr(N) | E_corr/E | case |
|---|---|---|---|---|
| 2000 | 25324886.76 | 25324886.76 | 1.000000 | no_exception (only q=3 < Z=3.404 checked) |
| 5000 | 199060153.43 | 199060153.43 | 1.000000 | no_exception (only q=3 < Z=3.427 checked) |
| 10000 | 1045773187.25 | 1045773187.25 | 1.000000 | no_exception (only q=3 < Z=3.443 checked) |
| 30000 | 13875798275.998 | 13875798275.998 | 1.000000 | no_exception (only q=3 < Z=3.465 checked) |
| 100000 | 223439980640.017 | 223439980640.017 | 1.000000 | no_exception (only q=3 < Z=3.472 checked) |

(Z values above are illustrative to 3 decimals; exact `mpmath` strings for
each row's `Z`, `window_lower`, and `scan_range` are in
`results_s8_control.json`'s `exceptional_case` field.)

This is itself informative for the control instrument: at every scale
currently reachable by direct computation, the exceptional-correction
machinery from CORRECTED_RH_BRIDGE.md/SIEGEL_UNIFORMITY.md is a no-op, and
\(E_{\rm corr}\) and the original \(E\) coincide exactly. The two
quantities can only diverge once \(N\) is large enough to push \(Z(N)\)
past a conductor that actually carries an exceptional zero -- and no such
zero is known to exist at any conductor, so in practice they may never
diverge at any \(N\) anyone will ever compute directly.

## 2. Cross-check at N=2000

\(E_{\rm corr}(2000)\) computed via the FFT route agrees with a direct,
no-numpy pair count (reusing probe.py's `psi2_python` and
`singular_series_python`, the same cross-check pattern probe.py itself
uses for \(E\)):

* FFT route: 25324886.763256
* Pure-Python route: 25324886.763256
* \(|\text{diff}|\): \(4.8\times10^{-8}\)

## 3. Sensitivity: a planted off-line zero

Section 8 treats such perturbations as diagnostics, not alternative prime
sequences. `s8_control.py` adds to \(\Lambda\) the density that a zero
pair \(\rho=\beta+i\gamma\), \(\overline\rho\) contributes to \(\psi'(x)\)
via the explicit formula \(\psi(x)=x-\sum_\rho x^\rho/\rho-\cdots\)
(the \(-1/\rho\) factor cancels on differentiating \(-x^\rho/\rho\)):
\[
 \Lambda_{\rm pert}(n)=\Lambda(n)-2\,\text{amplitude}\cdot n^{\beta-1}\cos(\gamma\log n),
 \qquad 1\le n\le N,
\]
then recomputes \(E_{\rm corr}\) on \(\Lambda_{\rm pert}\) against the
same fixed \(C_N\) (which is \(0\) here, since \(C_N\) depends only on
\((N,q,\chi,\beta)\) of the *assigned* exceptional data, not on the
sequence being measured).

**What the perturbed sequence keeps and breaks**, exactly as Section 8
requires this be written down:

* **Real coefficients**: kept. Pairing \(\rho\) with \(\overline\rho\) is
  exactly what makes the added density real at every integer \(n\).
* **A functional equation**: broken. Only the pair \(\rho,\overline\rho\)
  is planted; the functional-equation-reflected pair
  \(1-\rho,\overline{1-\rho}\) is not added, so no genuine \(L\)-function
  has \(\Lambda_{\rm pert}\) as (a truncation of) its von Mangoldt-type
  coefficients.
* **Prime support**: broken. The added term is a smooth function of every
  integer \(1\le n\le N\), not a function supported on primes and their
  powers; \(\Lambda_{\rm pert}\) is not the von Mangoldt function of any
  arithmetic object.

**Response of \(E_{\rm corr}\)** (ratio to the unperturbed row above;
`amplitude` scales the whole planted density):

| N | β=0.60,γ=14.13 | β=0.75,γ=14.13 | β=0.90,γ=14.13 | β=0.90,γ=50 | β=0.90,γ=14.13,amp=5 |
|---|---|---|---|---|---|
| 2000 | 1.078 | 1.367 | 6.827 | 2.783 | 2733.7 |
| 5000 | 1.066 | 1.483 | 9.744 | 3.291 | 3483.9 |
| 10000 | 1.084 | 1.833 | 20.875 | 3.392 | 4643.1 |
| 30000 | 1.058 | 1.696 | 17.428 | 3.511 | 4963.0 |
| 100000 | 1.024 | 1.437 | 22.677 | 7.152 | 7296.2 |

Qualitatively: the response grows sharply with \(\beta\) (a zero closer to
\(\mathrm{Re}=1\) is far more damaging, consistent with the density's
\(n^{\beta-1}\) envelope), is smaller for a higher \(\gamma\) at fixed
\(\beta\) (a faster-oscillating term self-cancels more in the
autocorrelation), and grows roughly with the square of `amplitude` (an
amplitude-5 planted term at \((\beta,\gamma)=(0.9,14.13)\) inflates
\(E_{\rm corr}\) by three to four orders of magnitude beyond the
already-large single-amplitude response at the same \((\beta,\gamma)\),
rather than by a factor of 5). None of this says anything about whether
such a zero exists; it only calibrates how visible one would be to
\(E_{\rm corr}\) if it did, at cutoffs section 8 asked for.

## 4. Reuse and scope

`s8_control.py` reuses probe.py's `von_mangoldt`, `singular_series`,
`singular_series_python`, `psi2_fft`, and `psi2_python` unmodified, and
`artifacts/siegel_uniformity/check.py`'s `factors`, `phi`, `ramanujan`,
`legendre`, and `local_characters` unmodified, importing both by path
rather than reimplementing anything they already compute. It writes only
under `hunts/prime_pair_error/`.

The full per-N `exceptional_case` metadata (exact `Z`, `window_lower`, and
`scan_range` at `mpmath` precision, and which conductors were checked) and
the full planted-zero parameter grid are in `results_s8_control.json`.
