# Route A, attempted: one further candidate priced, and the target quantity
# measured directly

RANK3_SCOPE.md's Route A asks for an unconditional, uniform-in-\(q\)
estimate for \(\Delta(t;q,b)=\psi(t;q,b)-t/\phi(q)\), strong enough to make
\[
 S(N):=\sum_{q=2}^{R_0}\mu(q)^2\sum_{b\bmod q}^*T(q,b)=O_\epsilon(N^{2+\epsilon}),
\qquad
 T(q,b)=\sum_{t=1}^N\Delta(t;q,b)^2+\sum_{t=1}^{N-1}[\Delta(N;q,b)-\Delta(t;q,b)]^2,
\tag{S}\]
for \(R_0=\lfloor Q/L\rfloor\), \(Q=\lfloor\sqrt N/3\rfloor\), \(L=\log N\)
(RANK3_ROUTE_D.md (D5); UPPER_BOUND.md Section 6). RANK3_ARC_TRANSFER.md
(T6) removed the separate transfer-step obstruction RANK3_ROUTE_D.md Section
6 had identified, so \(S(N)\) is now exactly, and only, what stands between
rank 3's \(U\)-side and the target \(O_\epsilon(N^{2+\epsilon})\); nothing
below revisits that reduction. This document does three things: recaps what
two prior attempts already established about Route A (Section 1, citation
only, nothing re-derived); prices one further candidate neither prior
document checked, and finds it strictly worse (Section 2); and measures
\(S(N)\) itself directly, rather than an ingredient of it, from the true
von Mangoldt function (Section 3). It does not assume RH anywhere, and does
not touch \(Z_{(q)}\) or ranks 1-2.

## 1. What RANK3_MEAN_VALUE_TOOLS.md and RANK3_BDH_VERIFY.md already settled

Restated here only to fix notation and the size of the remaining gap; both
documents are cited, not reproduced.

- **Individual-\(q\) uniformity (Route A as originally named) has no
  unconditional route.** RANK3_SCOPE.md Section 3: the only closing route
  the text exhibits for the analogous \(q=1\) case, (31), assumes RH, which
  would be circular against this hunt's own target (UPPER_BOUND.md Section
  1). Nothing here changes that.
- **An averaged-in-\(q\) substitute exists and has been checked against the
  two standard mean-value theorems.** Bombieri-Vinogradov (BV) is the wrong
  *strength* (a log-saving, matching (SW)/rank 1's own bottleneck, never a
  power of \(N\)) — RANK3_MEAN_VALUE_TOOLS.md Section 2, no numerical check
  needed. Barban-Davenport-Halberstam (BDH) is the right *shape* (a sum of
  squares, matching \(T(q,b)\)) and, applied at its single endpoint \(t=N\)
  and then summed crudely over \(t=1,\dots,N\) (RANK3_MEAN_VALUE_TOOLS.md
  (E1)-(E2)), gives
  \[
   S(N)\ \ll\ R_0N^2\log N\ \asymp\ N^{5/2},
  \tag{E2}\]
  exactly matching CHHL's own GRH-conditional order for \(E(N)\)
  (UPPER_BOUND.md Section 1), one full power of \(N^{1/2}\) short of the
  target. RANK3_BDH_VERIFY.md checked, against the primary sources
  themselves (not just the citing document), that no sharper member of the
  natural "for every fixed \(A\)" family is available at this range: BDH's
  sharp asymptotic form reaches large \(Q\), not small \(Q=R_0\); BV's
  arbitrary-\(A\) saving comes with an \(A\)-shrinking range incompatible
  with the fixed range \(Q\le R_0\); and the (SW)-style trick that lets an
  error term absorb a trivial initial segment does not transfer to BDH's
  quantity, which is leading-order content, not an error term. **Confirmed
  cost, from citable sources alone: \(N^{5/2}\), no better.**

## 2. A further candidate, checked and ruled out: the large sieve on the
##    \(K_N\)-continuum directly, rather than pointwise-in-\(t\)

(E1)-(E2)'s route applies BDH once at each fixed \(t\le N\) and adds the
\(N\) resulting bounds — a step both prior documents flag as crude. The
natural next attempt is to avoid that crudeness by applying the
*multiplicative* large sieve directly to the continuous object \(S(N)\)
already is (an integral over \(\beta\), via the same Parseval identity that
built \(T(q,b)\) in RANK3_ROUTE_D.md (D5)), instead of to \(N\) separate
point estimates. This section carries that out and shows it is not an
improvement — it is worse, and by a full power of \(N^{1/2}\) again, in the
*other* direction.

**Setup.** For a Dirichlet character \(\chi\bmod q\) and \(\beta\in\mathbb T\),
write \(\Psi(\beta,\chi)=\sum_{n=1}^N\Lambda(n)\chi(n)e(n\beta)\). By the same
convolution/Parseval computation RANK3_ROUTE_D.md Section 2 uses to derive
(D5) — here with \(\chi(n)\) in place of the indicator of a residue class —
\[
 \int_{\mathbb T}|K_N(\beta)|^2|\Psi(\beta,\chi)|^2\,d\beta
 =\sum_{t=1}^N|\psi(t,\chi)|^2+\sum_{t=1}^{N-1}|\psi(N,\chi)-\psi(t,\chi)|^2,
\qquad\psi(t,\chi):=\sum_{n\le t}\Lambda(n)\chi(n),
\]
and, by the multiplicative-character analogue of the additive-frequency
orthogonality identity RANK3_BDH_VERIFY.md Section 2 derives (that document
relates \(\sum_a^*|\Delta_a(t;q)|^2\) to \(\sum_b^*\Delta(t;q,b)^2\) via the
*additive* characters \(e(\cdot a/q)\); the identity needed here instead
expands \(\psi(t;q,b)\) in the *multiplicative* characters \(\chi\bmod q\) —
a different, but equally standard, orthogonality computation, not claimed
by that document and derived here instead): for \((b,q)=1\),
\(\psi(t;q,b)=\phi(q)^{-1}\sum_{\chi\bmod q}\overline{\chi(b)}\psi(t,\chi)\)
exactly (inverting \(\psi(t,\chi)=\sum_{n\le t}\Lambda(n)\chi(n)=\sum_{b}^*
\chi(b)\psi(t;q,b)+O(\rho_2(q))\), the same \(\rho_2(q)\) of (D3)), and the
\(\chi=\chi_0\) term reproduces \(t/\phi(q)\) up to the same \(O(\rho_2(q)/
\phi(q))\), so \(\Delta(t;q,b)=\phi(q)^{-1}\sum_{\chi\ne\chi_0}\overline{
\chi(b)}\psi(t,\chi)+O(\rho_2(q)/\phi(q))\); squaring, summing over \(b\),
and using \(\sum_b^*\overline{\chi(b)}\chi'(b)=\phi(q)\cdot\mathbf1_{\chi=
\chi'}\) gives
\(\sum_{b}^*\Delta(t;q,b)^2=\phi(q)^{-1}\sum_{\chi\ne\chi_0}|\psi(t,\chi)|^2
+O(\rho_2(q)^2/\phi(q))\), the same order of correction (D3) already tracks
and RANK3_BDH_VERIFY.md Section 2 tracks for its own, additive, version:
\[
 \sum_{q\le Q}W(q)\ \ge\ \sum_{q\le Q}\phi(q)\sum_{b\bmod q}^*T(q,b)
 \ \ge\ \sum_{q\le Q}\sum_{b\bmod q}^*T(q,b)\ \ge\ S(N),
\qquad
 W(q):=\sum_{\chi\bmod q,\,\chi\ne\chi_0}\int_{\mathbb T}|K_N(\beta)|^2|\Psi(\beta,\chi)|^2\,d\beta,
\tag{W1}\]
up to the same negligible \(O(\log^2q\log^2N)\)-type correction tracked
there (the last inequality uses \(\mu(q)^2\le1\le\phi(q)\)). So an upper
bound on \(\sum_{q\le Q}W(q)\), at \(Q=R_0\), is a (lossy, but valid) upper
bound on \(S(N)\).

**Bounding \(\sum_{q\le Q}W(q)\) by the large sieve at each fixed \(\beta\).**
Fix \(\beta\). Apply the multiplicative large sieve inequality
(Montgomery and Vaughan, *Multiplicative Number Theory I*, Theorem 6.7;
Iwaniec and Kowalski, *Analytic Number Theory*, Theorem 7.13 — the same
citation RANK3_MEAN_VALUE_TOOLS.md Section 1 uses) to the sequence
\(a_n=\Lambda(n)e(n\beta)\), \(1\le n\le N\):
\[
 \sum_{q\le Q}\sum_{\chi\bmod q}\Big|\sum_{n=1}^Na_n\chi(n)\Big|^2\le(N+Q^2)\sum_{n=1}^N|a_n|^2.
\]
Since \(|a_n|=\Lambda(n)\) — the phase \(e(n\beta)\) has modulus \(1\) and
drops out of \(|a_n|^2\) entirely — the right side is
\((N+Q^2)\sum_n\Lambda(n)^2=(N+Q^2)d_N\), **with no dependence on \(\beta\)
at all**, where \(d_N=\sum_{n\le N}\Lambda(n)^2\ll NL\) is UPPER_BOUND.md's
own quantity (UPPER_BOUND.md, the line before its equation (20): "\(d_N\le
L\psi(N)\ll NL\), by Chebyshev's bound"). So, for *every* \(\beta\in\mathbb T\):
\[
 \sum_{q\le Q}\sum_{\chi\bmod q}|\Psi(\beta,\chi)|^2\ \le\ (N+Q^2)d_N.
\tag{W2}\]

**Integrating (W2) against \(|K_N(\beta)|^2\,d\beta\).** Both sides of (W2)
are nonnegative; multiply by \(|K_N(\beta)|^2\ge0\) and integrate over
\(\mathbb T\). The right side is a \(\beta\)-independent constant times
\(|K_N(\beta)|^2\), and \(\int_{\mathbb T}|K_N(\beta)|^2\,d\beta=N\) exactly
(Parseval; \(K_N\) has \(N\) unit coefficients), so
\[
 \sum_{q\le Q}\sum_{\chi\bmod q}\int_{\mathbb T}|K_N(\beta)|^2|\Psi(\beta,\chi)|^2\,d\beta
 \ \le\ (N+Q^2)d_N\cdot N.
\]
The left side is (at most) \(\sum_{q\le Q}W(q)\) plus the nonnegative
\(\chi=\chi_0\) term, so in particular
\[
 \sum_{q\le Q}W(q)\ \le\ (N+Q^2)d_N N\ \ll\ (N+Q^2)N^2L.
\tag{W3}\]

**Comparing (W3) to (E2) at \(Q=R_0\).** \(R_0\asymp\sqrt N/(3L)\), so
\(R_0^2\asymp N/(9L^2)=o(N)\), and \(N+R_0^2\asymp N\). Substituting into
(W3):
\[
 \sum_{q\le R_0}W(q)\ \ll\ N\cdot N^2L=N^3L,
\tag{W4}\]
a **full power of \(N^{1/2}\) worse** than (E2)'s \(N^{5/2}\), which is
itself already a power of \(N^{1/2}\) short of the target. Combined with
(W1), this shows \(S(N)\ll N^3L\) via this route — true, but strictly weaker
than what (E2) already gives directly, so this candidate is not a way
forward.

**Why it fails, structurally.** (W2)'s bound is the *same* ceiling
\((N+Q^2)d_N\) at every \(\beta\), because the large sieve, applied this
way, only ever sees \(|a_n|=\Lambda(n)\) — a quantity with no \(\beta\)
dependence — and so cannot distinguish a \(\beta\) where the character sums
happen to be small from one where they are large. Integrating that
\(\beta\)-blind ceiling against \(|K_N(\beta)|^2\,d\beta\) just multiplies it
by \(\int|K_N|^2=N\), converting the large sieve's one saving (the
\((N+Q^2)\) ceiling in place of the trivial \(Q^2\cdot\)(number of
characters)) into the *only* saving available, while adding back, for free,
the same order-\(N\) loss that (E1)'s "sum \(N\) copies of a bound" step
incurs on the \(t\)-side. It is a different bookkeeping path to
(structurally) the same kind of waste, not an independent mechanism, which
is why it lands a power of \(N^{1/2}\) below (E2) rather than above it. To
do better than (E2) via any such continuum route would require exploiting
genuine cancellation of \(\Psi(\beta,\chi)\) *across* \(\beta\) for a
*single* \(\chi\) before invoking the large sieve on \(q,\chi\) — but a
bound on \(\int_{\mathbb T}|K_N(\beta)\Psi(\beta,\chi)|^2\,d\beta\) for one
fixed \(\chi\) is exactly \(\sum_t|\psi(t,\chi)|^2\)-type, i.e. exactly
Route A's original single-modulus uniformity question, restated at the
level of one character rather than one residue class. This document does
not find a way around that restatement, and does not believe, based on the
computation above, that one is available from the large sieve alone; it
records this as a ruled-out direction, not merely an unexplored one.

## 3. Measuring \(S(N)\) directly

Neither RANK3_MEAN_VALUE_TOOLS.md nor RANK3_BDH_VERIFY.md computes \(S(N)\)
or \(T(q,b)\) themselves; both price named theorems against them. This
section measures \(S(N)\) directly from the true von Mangoldt function (
prime-power enumeration, no model, no sampling), at the *actual* \(R_0(N)\)
UPPER_BOUND.md's construction uses, via `rank3_route_a_measure.py`
(results in `results_rank3_route_a_measure.json`). Correctness of the
per-\((q,b)\) computation of \(T(q,b)\) against RANK3_ROUTE_D.md's (D5) was
checked directly (a hand-written running-sum computation of \(\psi(t;q,b)\)
against the vectorized version the probe uses, at \(N=30\), \(q=4\); they
agree to floating-point precision for both reduced residues).

**Experiment 1: \(S(N)\) at the true \(R_0(N)\), across a ladder of \(N\).**

| \(N\) | \(R_0\) | \(S(N)\) | \(S/N^2\) | \(S/N^{2.5}\) | \(S/(R_0N^2\log N)\) |
|---|---|---|---|---|---|
| 20000 | 4 | \(1.043\times10^8\) | 0.261 | \(1.84\times10^{-3}\) | \(6.6\times10^{-3}\) |
| 60000 | 7 | \(5.00\times10^9\) | 1.389 | \(5.67\times10^{-3}\) | \(1.8\times10^{-2}\) |
| 150000 | 10 | \(2.65\times10^{10}\) | 1.179 | \(3.04\times10^{-3}\) | \(9.9\times10^{-3}\) |
| 400000 | 16 | \(6.19\times10^{11}\) | 3.866 | \(6.11\times10^{-3}\) | \(1.9\times10^{-2}\) |
| 1000000 | 24 | \(1.04\times10^{13}\) | 10.41 | \(1.04\times10^{-2}\) | \(3.1\times10^{-2}\) |
| 2000000 | 32 | \(5.33\times10^{13}\) | 13.31 | \(9.41\times10^{-3}\) | \(2.9\times10^{-2}\) |

The local exponent \(\log(S_2/S_1)/\log(N_2/N_1)\) between consecutive rows
is \(3.52,1.82,3.21,3.08,2.35\) — noisy at this scale (only six points,
\(R_0\) itself only \(4\) to \(32\)), but its average, \(2.80\), and every
individual value, sit above \(2\), several comfortably above \(2.5\).
Reading the two normalized columns: \(S/N^2\) climbs by a factor of
\(\approx51\) while \(N\) grows by a factor of \(100\) — far more than any
fixed power of \(\log N\) could plausibly account for (matching that
climb via log powers alone, using \(\log(2\times10^6)/\log(20000)\approx1.46\),
would need an implausible fixed exponent near \(10\) on \(\log N\)) — so
this data does not read as consistent with \(S(N)=O_\epsilon(N^{2+\epsilon})\)
at these scales; it reads as a genuine excess power of \(N\) above \(2\).
By contrast \(S/N^{2.5}\) and \(S/(R_0N^2\log N)\) — the latter being (E2)'s
own crude bound, evaluated with its actual constant \(1\), not just in
\(\asymp\)-notation — both stay within a single order of magnitude across
the whole \(100\)-fold range of \(N\), with no trend toward \(0\): the ratio
to the *proven* \(N^{5/2}\)-order ceiling, if anything, drifts slightly up
(from \(0.007\) to \(0.03\)) rather than down. **What the actual arithmetic
shows, at every scale tested here, tracks the order of the ceiling this
document and its predecessors have already proved (E2), not the order of
the target.** This is consistent with the \(N^{1/2}\) gap being a real
feature of \(S(N)\)'s true size, not merely unproved slack in (E2)'s
derivation — though six points spanning two orders of magnitude in \(N\),
at \(R_0\) still only in the tens, cannot rule out a different asymptotic
regime setting in once \(R_0\) is very large; a finite measurement settles
neither reading of an asymptotic question, and this one is reported as
measured, not as a proof of either.

**Experiments 2a-2b: fixed-\(Q\)/fixed-\(N\) decomposition, matching
`rank3_bdh_probe.py`'s structure.** With \(Q=8\) fixed and \(N\) swept over
the same ladder, the local \(N\)-exponent of \(S\) is \(2.28,1.49,2.12,2.65,
0.98\) — noisy, averaging \(1.90\), i.e. closer to the target's own \(N^2\)
at a *fixed*, small modulus range than the joint experiment above, which
also lets \(R_0\) grow. With \(N=400000\) fixed and \(Q\) swept from \(4\) to
\(30\), the local \(Q\)-exponent is \(2.22,1.53,2.62,2.04,1.64,1.58\),
averaging \(1.94\) — closer to a bare \(Q^2\) (no large-sieve-type saving
visible yet at these small \(Q\)) than to BDH's own asymptotic \(Q\log Q\)
shape, echoing exactly the caveat `rank3_bdh_probe.py`'s own Experiment 1
already recorded for \(D(N,Q)\) itself ("this experiment alone cannot
distinguish an asymptotic regime not yet reached... from a genuinely
steeper \(Q\)-dependence"). Both sub-experiments are reported as measured,
not fit to either shape, for the same reason.

## 4. Verdict

**Route A, as RANK3_SCOPE.md poses it, is not closed here, and no
unconditional closing route is found.** Restated precisely:

- The individual-modulus form of Route A has no unconditional route in
  either source document; its only exhibited closing path is RH-circular
  (Section 1, citing RANK3_SCOPE.md).
- The averaged-in-\(q\) substitute this document's predecessors identify
  (BDH, applied pointwise-in-\(t\) and summed) reaches \(O(N^{5/2})\),
  matching CHHL's GRH-conditional benchmark unconditionally but falling
  short of the target by exactly one power of \(N^{1/2}\), and no sharper
  citable theorem closes that gap (Section 1, citing RANK3_BDH_VERIFY.md).
- This document's own further candidate — applying the same large sieve to
  the \(K_N\)-continuum directly, rather than pointwise-in-\(t\) — is not an
  improvement: it gives \(O(N^3L)\), a full power of \(N^{1/2}\) *worse*
  than (E2), for a structural reason (Section 2) that generalizes: any
  large-sieve application that treats \(\beta\) (or \(t\)) as a parameter to
  integrate a fixed-\(\beta\) ceiling over, rather than as a variable the
  sieve genuinely averages over jointly with \(q\) and \(\chi\), pays for the
  averaging twice — once implicitly in the ceiling, once explicitly in the
  \(\int|K_N|^2=N\) factor.
- Direct measurement of \(S(N)\) itself (Section 3), at the real, jointly
  varying \(R_0(N)\), gives no empirical support for \(S(N)=O_\epsilon(N^{2+
  \epsilon})\) over the range tested, and tracks the shape of the already-
  proved \(N^{5/2}\)-order bound instead — evidence, not proof, that the
  remaining gap reflects a genuine difference in size, not merely a proof
  technique that has not yet been sharpened.

**What would be needed, stated as precisely as this document can:** a
mean-value theorem that bounds \(\sum_{q\le Q}\sum_{\chi\bmod q}\int_{\mathbb
T}|K_N(\beta)\Psi(\beta,\chi)|^2\,d\beta\) — equivalently \(\sum_{q\le
Q}\phi(q)\sum_b^*T(q,b)\) — genuinely jointly in \(q\), \(\chi\), and the
length/frequency variable \(t\)/\(\beta\) at once, at an order beating both
\(O((N+Q^2)Nd_N)\) (Section 2's ceiling) and \(O(QN^2\log N)\) (the crude
\(t\)-summed BDH bound), down to \(O(QN^{1+\epsilon})\) or better. This is
exactly the object RANK3_MEAN_VALUE_TOOLS.md Section 8 already named as
missing; this document adds one further ruled-out route to reach it (the
continuum large sieve of Section 2) and a direct measurement (Section 3)
suggesting the gap it would need to close is real, not an artifact of which
proof technique has been tried so far. Neither of those additions supplies
the missing theorem, and this document does not claim to have found one
under another name.

This document is citation of two prior documents in this hunt (Section 1),
one further exact large-sieve computation with a fully explicit constant
chain (Section 2), and one direct numerical measurement from the true
von Mangoldt function with no model or sampling (Section 3); it assumes and
establishes nothing about zeros of \(L\)-functions or the Riemann
Hypothesis.
