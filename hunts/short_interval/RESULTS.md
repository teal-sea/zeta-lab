# Bounded outcome

**No mathematics has been attempted in this hunt.** It was opened on
2026-09-12 and what follows is everything established on that day: three
findings, all reading and measurement rather than new mathematics, which
between them killed the plan the hunt was opened for and reordered its
routes. Grade: **derived and measured**, nowhere higher. Nothing here bears on
RH (`docs/08`).

`MISSION.md` carries the routes. This file records only what is settled.

## 1. Finding one: the tree already computes Wang's curve

Biao Wang's arXiv:2609.07918 Theorem 1.1 bounds the proportion of simple
on-line zeros in `(T, T + T^theta]` below by
`c(theta) = 2 - theta/2 - (1/sqrt 2) cot(theta/sqrt 2)`.
`hunts/frontier_map/frontier.py:zeta_H_closed(lam)`, taken from the source
paper's eq. (7.4), computes the same function of bandwidth. Measured equal to
1e-16 at five bandwidths, and the lab's curve crosses zero at
`0.5501939647441547` against Wang's printed `theta_0 = 0.550193964744154`.
The same module's `Hd = (1 + H)/2` is Wang's distinct companion. **Both
constants in Wang's Theorem 1.1 were already being computed here.**

What Wang adds is that the dial is physical. `frontier.py` holds bandwidth as
"exactly one dial, capped at 1 by the Rudnick-Sarnak / Montgomery support
restriction", a hypothetical, since the whole game was pushing it up. His
Theorem 2.2, an unconditional short-interval pair-correlation formula valid
for `supp g` in `[-lambda, lambda]` with `lambda < theta` strictly, says
bandwidth theta is exactly what counting in an interval of length `T^theta`
buys. The lab's dial and his exponent are the same number.

Every constant printed in both papers reproduces: `verify.py` checks `C_MT`,
both global proportions, `c(3/4)`, `d(3/4)`, `theta_0`, `theta_d`, Wang's
stated `c'(theta)`, and the closed form of the variational minimum against an
independent Nystrom solve at six bandwidths.

## 2. Finding two: the transplant is dead, and the reason is the second moment

Substituting `c(theta)` into the two kernel-checked bridges fails. In the
coordinate the problem is affine in, `R = 2 - c`, which is the normalized
second moment, `Phi_3` reads `R -> 1.001343 R - 0.002019`. The certificate
buys a fixed absolute `0.002019` and pays a **relative 0.134% of whatever
second moment it consumes**, and `R(theta) = 1/theta + theta/3 - ...` diverges
like `1/theta`. So the overhead is proportional to the one quantity that blows
up in a short window, and break-even is at `theta = 0.8082`. **No
re-optimization repairs that**, which is why §3 matters.

Independently the transplant has no analytic footing: the band is
`(-theta, theta)`, open and strict, while the bridges read `[-1, 1]` with no
free half-length anywhere in `famlib.py`; and the bridges are dyadic, with 21
occurrences of `2 * T` in `Bridge/Main.lean` alone and `S8`, `S9` and `S15`
all absorbing errors against `N(T, 2T)`. A per-block error absorbed against
`N(T, 2T)` and reappearing against `T^theta log T` **carries a hidden
`T^(1-theta)`**, and that hazard recurs on every route here.

## 3. Finding three: window shape is worth nothing in a short interval

Measured in `landscape.py`. Writing the functional as
`R = A(phi)/lambda + lambda B(phi)` with `A = int phi^2/(int phi)^2 >= 1` by
Cauchy-Schwarz, equality iff `phi` is flat, the flat window gives
`R = 1/lambda + lambda/3` **exactly** (verified), whose threshold is the root
of `theta^2 - 6 theta + 3`, that is `3 - sqrt 6 = 0.5505102572`.

Against Wang's optimal-window `theta_0 = 0.5501939647`, **the entire value of
the Montgomery-Taylor window over a flat one is 3.2e-4 of threshold.** The
flat-minus-optimal gap is about `lambda^3/180`: measured `0.00122` at
`lambda = 0.6` against `0.00120`, and `0.00583` at `lambda = 1` against
`0.00556`. The optimal window flattens as bandwidth shrinks.

At `theta = 0.55` the whole window-shape game is therefore worth about `9e-4`,
and an n-point family whose bandwidth-one share of it is `2.4e-4` is worth
roughly `4e-5`. **Wang's `c(theta)` already is the re-optimization.**

## 4. Two literature searches, run 2026-09-12, recorded per the novelty rule

`CLAUDE.md`: where a search has actually been run, say what was searched and
what it found. Both searches below were run by delegated sessions with web
access; every query string and every paper opened is listed so that each
absence is a documented absence rather than an unrun check. The arXiv API
returned HTTP 503 or 429 for most of the day, so the API queries listed as
unrun were substituted by the arXiv web search UI and listing pages.

### 4.1 Short-interval proportions for zeros of xi-prime

**Verdict: not in the literature.** No paper states a proportion of simple,
or critical, zeros of `xi'` (or of `xi^(k)`, `zeta^(k)`) in
`(T, T + T^theta]` as a function of theta, conditional or unconditional.

**The near-miss.** Conrey (JNT 17 (1983)) and Rezvyakova (Izv. Math. 69
(2005), 70 (2006)) work in sub-dyadic windows `U = T (log(T/2 pi))^(-10)`:
on-line proportion of `xi^(k)` zeros above `1 - (3/5) k^(-2)`, simple
on-line above `1 - ((e^2 + 2)/16) k^(-2)`, uniformly in `k` up to
`(1/2) log log T / log log log T`; about `0.413` at `k = 1`. So the claim, if
the route succeeds, is "first power-length statement, as a function of
theta", never "first short-interval statement".

**What was found, per paper.** Farmer-Gonek-Lee (JLMS 90 (2014),
arXiv:0803.0425): RH throughout, `F_1` on `0 < gamma <= T`, Corollary 1.3
gives `0.8584` simple under RH, no short intervals; nineteen citing papers on
Semantic Scholar, none short-interval. Alpöge-Furman (arXiv:2608.13637 v2):
Remark 7.1 gives `0.85838 / 0.92919` flat and `0.86864 / 0.93432` quartic,
unconditional, dyadic `(T, 2T)`, and cites FGL only as comparator; Remark 6.1
states `H(lambda) = 2 - 1/lambda - lambda/3` for the flat window with "no
`lambda < 1` improves the constants". Wang (arXiv:2609.07918): zeta only, no
derivative anywhere. Lamzouri (arXiv:2609.02882 v1, v2): zeta only. Chirre,
Gonçalves, de Laat (arXiv:1810.08843): Corollary 7, `0.8825 / 0.9412` for
`xi'` under RH, full range. Bui (arXiv:0903.4006): `xi'` gaps under RH. Bian
(Rochester thesis 2008): pair correlation of `xi^(k)` zeros, full range.
Sodin (arXiv:1611.10037): microscopic clustering under RH. Malik-Roy (Forum
Math. 32 (2020)): explicit formula and zero density for `xi^(m)`, no
proportion. Ki-Lee (Funct. Approx. 47 (2012)) and Das-Pujahari
(arXiv:2104.10243): `zeta^(k)` in `(T, T + T^a]`, `a > 1/2`, horizontal
sums only. Steuding (Acta Math. Hungar. 96 (2002)): zeta, `H >= T^0.552`,
Levinson method, no theta-curve. Karatsuba (1984): zeta, odd-order zeros,
`H >= T^(27/82 + eps)`. Wu (arXiv:1206.3737): `0.86957` on-line for `xi'`
unconditionally, per AF's citation; §3 not opened. Hua-Yang
(arXiv:2608.16034): Dirichlet family average, not single-function.
Baluyot-Goldston-Suriajaya-Turnage-Butterbaugh (arXiv:2501.14545 v3, revised
2026-09-01): no short intervals, no derivatives. Goldston-Lee-Schettler-
Suriajaya (arXiv:2507.06823) and Goldston-Suriajaya (arXiv:2511.20059):
expository, none. Of 191 `math.NT` listings 2026-09-05 to 2026-09-12, only
Wang concerns short-interval zeros. Semantic Scholar: 0 citations of Wang, 1
of Lamzouri, 3 of Alpöge-Furman.

**Where the xi-prime input lives.** Nowhere in print. Alpöge-Furman's Remark
7.1 says only "the argument of §§4-6 gives, unconditionally"; their §5 is
written for zeta. The unconditional `xi'` prime side exists only as Lean code
in `anthropics/formal-math`, `zeta23/Zeta23/XiPrime/` (formerly
`anthropics/zeta-23-lean`), citing an unpublished write-up `[XF']`:
coefficient family `b_N = C(N; L_T)`, `L_T = l/2 + i pi/4`, density `D_1`;
`XiEF`, the entrywise explicit formula with error
`C T^(-delta) (min(1, |tau_k - tau_l|^(-2)) + 1/T)`,
`delta = (1 - 3 lambda/4)/2`; `CoeffMoments`, the two prime-side moments with
`N = N(T, 2T)`, proved for every `lambda` in `(0, 1)` as
`xiDeriv_fixedLamBounds`. That pair is the `xi'` analogue of BGSTB's Lemma 5
and the object a short-interval theorem must localize. Also formalized there:
Hardy's `Z'` at `0.85838 / 0.92919`, equally absent from the short-interval
literature.

**Not opened, blocked:** Steuding 2002 text (Springer SSO); Chaubey-Malik-
Robles-Zaharescu (JMAA 2017, ScienceDirect 403), which concerns combinations
of `xi^(k)` on the line and by title not short intervals, unverified;
Levinson-Montgomery 1974; Karatsuba 1984; Wu 2015 §3; the `[XF']` write-up.

**WebSearch queries run (34), verbatim:**
1. "zeros of the derivative of the Riemann xi-function" simple zeros proportion critical line
2. "xi'" zeros "short intervals" critical line derivative Riemann xi-function
3. "zeros of derivatives of Riemann's xi-function" Conrey 1983 proportion critical line
4. Farmer Gonek Lee pair correlation zeros derivative xi function simple zeros proportion cited by
5. Bian Bui correlations zeros of xi' derivative Riemann xi-function alternative hypothesis arXiv
6. "simple zeros" "short intervals" derivative zeta function "zeta'" OR "xi'" arXiv 2026
7. "2609.07918" OR "Biao Wang" "short intervals" simple critical zeros distinct zeros Riemann zeta
8. Conrey 1983 "Zeros of derivatives of Riemann's xi-function on the critical line" 81.37% xi' 0.7987 simple zeros xi^(k) proportion table
9. Ki Lee "zeros of the derivatives of the Riemann zeta function" OR "zeros of derivatives" xi-function critical line proportion arXiv
10. Levinson Montgomery 1974 "Zeros of the derivatives of the Riemann zeta-function" Acta Math zeta' left of critical line
11. Karatsuba "short intervals" critical line zeros derivative "zeta" "Hardy function" Z'(t) OR "derivative" short interval zeros
12. pair correlation "short intervals" zeros zeta "T^theta" Montgomery unconditional Baluyot Goldston Suriajaya Turnage-Butterbaugh short interval
13. "pair correlation" upper bound "proportion of simple zeros" best possible limit "form factor" bandwidth "cannot exceed" Montgomery method optimal
14. Bian Bui "zeros of the derivative" xi-function correlations "alternative hypothesis" 2020 OR 2021 OR 2022 OR 2023 OR 2024 OR 2025
15. Wu "Distinct zeros of the Riemann zeta-function" Quart. J. Math. 66 2015 xi' critical line 0.86957 unconditional
16. arXiv September 2026 "short intervals" zeros Dirichlet L-functions simple critical "Lamzouri" OR "Alpöge" OR "Furman" new proof extension
17. Malik Roy "On the distribution of zeros of derivatives of the Riemann xi-function" Forum Math 2019 abstract short intervals zero density
18. Steuding 2002 "On simple zeros of the Riemann zeta-function in short intervals on the critical line" T^{0.552} positive proportion Acta Math Hungar abstract
19. "zeros of \xi'" OR "zeros of xi'" OR "xi-prime" simple critical line unconditional 2024 OR 2025 OR 2026 arXiv Levinson method derivative xi proportion improve Conrey
20. Das Pujahari "Zeros of higher derivatives of Riemann zeta function" short intervals mollifier T^theta proportion zeros critical line derivative
21. "Lean" "Zeta23" OR "xiDeriv_simple_on_line" OR "Alpöge Furman" GitHub formalization zeta zeros simple critical line
22. Ge "zeros of the derivative of the Riemann zeta function" OR "zeta'" critical line proportion arXiv 2017 OR 2018 OR 2019 "left of the critical line" OR "near the critical line"
23. Suriajaya "zeros of the derivatives" OR "zeros of the k-th derivative" Riemann zeta function OR xi function critical line arXiv 1310.6489 OR 1308.5116
24. "Chirre" "Gonçalves" "de Laat" "Pair correlation estimates for the zeros of the zeta function via semidefinite programming" xi' 0.8825 0.9412 Corollary 7 derivative
25. "zeros" "in short intervals" "derivative" "Riemann xi" OR "xi-function" OR "completed zeta" theorem proportion critical line
26. Rezvyakova "zeros of the derivatives of the Riemann" xi-function Izvestiya Mathematics 2005 short intervals critical line
27. Rezvyakova "simple zeros of derivatives of the Riemann" xi-function Izv. Math. 70 2006
28. Karatsuba school "derivatives of the Riemann xi-function" OR "derivative of the Riemann xi-function" zeros "short intervals" critical line Rezvyakova OR Karatsuba OR Voronin proportion
29. "Zeros of the derivatives of the Riemann xi-function" Rezvyakova Izvestiya OR "Izv. Math." OR mathnet.ru abstract proportion 1-(3/5)k^-2 OR "on the critical line"
30. "xi^{(k)}" OR "xi^{(k)}" zeros "critical line" proportion "short" Chaubey Malik OR Rezvyakova OR "normalized combinations" arXiv
31. "pair correlation" zeros "short intervals" "T^{theta}" OR "T^theta" simple zeros proportion Dirichlet L-function OR "L-functions" 2026 arXiv Montgomery short interval theorem
32. Karatsuba "zeros of the function" "short intervals of the critical line" derivative "Z^{(k)}" OR "derivatives of Hardy's function" proportion simple zeros short interval T^{27/82} Izvestiya
33. Conrey 1983 "at least 81.37%" OR "81.37" zeros "xi'" critical line "J. Number Theory 16"
34. "Hardy's function" OR "Hardy's Z-function" derivative "Z'" zeros simple "short intervals" OR "short interval" proportion critical line stationary points

**Other lookups:** Semantic Scholar citations of arXiv:0803.0425 (19),
2608.13637 (3), 2609.02882 (1), 2609.07918 (0); S2 searches for Rezvyakova
(5 hits), Steuding 2002 and Ki-Lee 2012 (HTTP 429, unrun); zbMATH
`au:Steuding & ti:short intervals` (4); Crossref record for Steuding 2002;
mathnet.ru abstracts and Russian full texts of Rezvyakova 2005 and 2006;
arXiv web UI searches for `"short intervals" zeros` (Aug-Sep 2026, 1 hit,
Wang), `"short intervals" zeros derivative` (12), `"xi-function" derivative
zeros` (14), `"derivatives of the Riemann" zeros "critical line"` (11),
`"simple zeros" "short intervals"` (0), `"pair correlation" "short
intervals" zeros` (5); arXiv `list/math.NT/pastweek` (191 entries, titles
scanned). Eight arXiv API queries returned HTTP 503 and are unrun; their
strings are in the delegated session's log.

### 4.2 Upper bounds on Montgomery's form factor beyond the band

**Verdict: no published result gives a `T`-independent upper bound on `F`
over any interval beyond `alpha = 1` unconditionally. Under RH, integrated
bounds exist but tend to a positive constant rather than to zero as the
interval shrinks, so none has the shape `B delta` the pricing in §8 of
`MISSION.md` needs.**

**Unconditionally:** `F >= 0` (positive definiteness; Carneiro-Chandee-
Chirre-Milinovich arXiv:2108.09258 §1.2) and `F(alpha) <= F(0) ~ log T`
(Goldston, math/0412313, (6.2)). BGSTB (arXiv:2306.04799) stop at
`alpha = 1`. Fujii and Tsang (restated in arXiv:2503.15449 §6) give
unconditional Fejér-weighted averages inside the band only. Unconditional
prime-variance bounds (Brun-Titchmarsh; Zaccagnini, Acta Arith. 84 (1998),
via arXiv:1603.02952 §3.2) are of the `H^2 x` shape, not `H x log(x/H)`.

**Under RH:** Goldston's Notes Lemma 1: `integral_B^(B+1) F <= 3` for any
`B`. Carneiro-Chandee-Chirre-Milinovich Theorem 10:
`integral_1^(1+delta) F <= 7/8 + (5/4) delta + O(delta^2) + o(1)`, and their
(2.27): "we cannot rule out the existence of delta spikes in `F(alpha)` for
`|alpha| >= 1`" (Baluyot, JNT 169 (2016), studies the connection to the
alternative hypothesis). Carneiro-Milinovich-Ramos (arXiv:2310.01913):
`0.9303 < (1/l) integral_b^(b+l) F < 1.3208` for long intervals. Pointwise,
nothing: Heath-Brown (Acta Arith. 41 (1982)) and Goldston-Suriajaya
(arXiv:2205.06503) carry `F(alpha) << 1` just past 1 as an unproved
hypothesis, the latter writing "there is probably no hope of proving any of
these conjectures at present". Chirre-Gonçalves-de Laat (arXiv:1810.08843,
Lemma 8) use only `F >= 0` beyond the band; Carneiro-Chandee-Littmann-
Milinovich (arXiv:1406.5462) likewise. Montgomery 1973 §3 already names the
obstruction: for `1 <= alpha < 2` the program needs "a reasonable hypothesis
as to the size of the differences `sum_{n<=y} Lambda(n) Lambda(n+h) - c(h) y`".

**Under stronger hypotheses:** only lower bounds (Goldston-Gonek-Özlük-
Snyder, Proc. LMS 80 (2000), `F >= 3/2 - |alpha| - eps` under GRH; Walker
arXiv:2101.04418 under an `AP(theta)` conjecture) or full asymptotics under
Hardy-Littlewood with power saving (Bolanz 1987; Goldston's Notes (6.3)).

**The obstruction past `alpha = 1` is not RH.** `F(alpha) - alpha` is the
difference of two terms of size about `T^alpha` whose cancellation to
`O(T log T)` needs the prime-pair correlations to relative error
`O(T^(1-alpha) log T)`. Sieve constants (Bombieri-Davenport 4; Wu 2004
3.3995; Lichtman arXiv:2109.02851 3.2996; never below 2 by parity) leave a
residual `(c - 1) T^alpha` against `T log T`; at `alpha = 1.05`,
`log T = 100`, `c = 2`, the residual is already 1.4 times the main term.
Montgomery-Soundararajan (math/0409258) is the second-order singular-series
input that would be needed. The one-line kill for any draft: an argument
that drops the phases beyond the band proves the same bound at `b = 0`,
where `integral_(-delta/2)^(delta/2) F >= 1 + o(1)`.

**WebSearch queries run (21), verbatim:**
1. Montgomery pair correlation form factor F(alpha) upper bound alpha > 1 unconditional
2. Goldston "On the pair correlation conjecture for zeros of the Riemann zeta-function" 1988 F(alpha) 3/2 - alpha
3. "pair correlation" zeros zeta "beyond the band" OR "outside the band" F(alpha) alpha > 1 upper bound RH
4. Goldston Gonek Ozluk Snyder "On the pair correlation of zeros of the Riemann zeta-function" Proc London Math Soc 2000 F(alpha) lower bound 1 < alpha < 3/2
5. Carneiro Chandee Littmann Milinovich "Hilbert spaces and the pair correlation of zeros" F(alpha) integral upper bound A - 1/2
6. Goldston Montgomery "Pair correlation of zeros and primes in short intervals" variance equivalent unconditional upper bound variance primes short intervals
7. "F(\alpha" "\alpha > 1" "sieve" "Lambda(n)Lambda(n+h)" pair correlation upper bound zeta zeros
8. Goldston 1988 Crelle "pair correlation conjecture" "F(alpha" lower bound RH "3/2" OR "A - 1/2" integral of F Lemma A
9. Saffari Vaughan unconditional variance primes short intervals mean square upper bound delta x^2 log^2
10. Montgomery Soundararajan "Primes in short intervals" variance singular series sum (H-h) S(h) = H^2/2 - H log H /2
11. Goldston Gonek "A note on the number of primes in short intervals" 1990 F(alpha) upper bound integral pair correlation RH
12. Baluyot "alternative hypothesis" pair correlation zeros zeta F(alpha) delta spikes Montgomery function
13. Selberg sieve upper bound twin primes "8" prod (1-1/(p-1)^2) x/(log x)^2 Bombieri Davenport constant 4 times Hardy-Littlewood Lambda(n)Lambda(n+h) <=
14. Fujii unconditional pair correlation zeros Riemann zeta "On the zeros of Dirichlet L-functions" OR "distribution of the zeros" sum over pairs of zeros unconditional Montgomery F
15. Baluyot "On the pair correlation conjecture and the alternative hypothesis" Journal of Number Theory 2016 abstract F(alpha) spikes
16. Saffari Vaughan 1977 "On the fractional parts of x/n and related sequences II" Selberg integral unconditional o(x^3 theta^2) range x^{-5/6}
17. "F(\alpha" OR "F(alpha" "alpha >= 1" OR "alpha > 1" "unconditionally" pair correlation zeta zeros upper bound form factor beyond band zero-density
18. Heath-Brown 1982 "Gaps between primes, and the pair correlation of zeros of the zeta-function" hypothesis F(x,T) = o(T log^2 T) T <= x <= T^M
19. Goldston Suriajaya "Fujii" prime number theorem error "F(x,T) << T log x" "T <= x <= T log T" x^{1/2}(log x)^{3/2} arXiv
20. Montgomery 1973 "pair correlation of zeros of the zeta function" F(alpha) "alpha > 1" what Montgomery proved Hardy-Littlewood conjecture strong error term "1 <= alpha <= 2"
21. Carneiro Chirre Milinovich "Bandlimited approximations and estimates for the Riemann zeta-function" arXiv Publicacions Matematiques 2019 abstract

**Papers opened, full text:** arXiv:2108.09258, 2502.05106, 1810.08843,
2306.04799, math/0412313, 2205.06503, 2501.14545, 2310.01913, 1311.0597,
2101.04418, 1406.5462, 1604.06124, 2208.02359, math/0305340, 1603.02952,
2412.20099, 2511.20059, 2503.15449, 2507.06823, 2108.10238, math/0409258,
2109.02851, Montgomery 1973 (scan). **Abstract only:** Goldston-Gonek-
Özlük-Snyder 2000; Baluyot 2016; Carneiro-Chirre-Milinovich 2019
(arXiv:1710.10362). **Not opened, quoted second-hand:** Goldston 1981,
Goldston-Gonek 1990, Goldston-Gonek-Montgomery 2001, Heath-Brown 1982,
Saffari-Vaughan 1977, Halberstam-Richert.

## 5. Two readings withdrawn the same day

Recorded rather than deleted.

**Withdrawn: that the closed form of the variational minimum was this hunt's
finding.** It was derived here before the paper was read, and it is Wang's
published Proposition 4.1 equation (4.2) with a uniqueness proof the
re-derivation does not have. It is also already in this tree as
`frontier.py:zeta_H_closed`. `verify.py` keeps the derivation as a cross-check
of the paper, not as output.

**Withdrawn: that `PALOMAR-2026-08-21-000004` is the `lambda = 1` case of
Wang's Proposition 4.1.** It is not. Two different constants in this tree are
both called `c*`: the zeta one has kernel `|alpha|` with
`1/c*_1 = 1.3274992963205884` and is Wang's; the `xi'` one in
`lean/ZetaLean/Pub1/Setting.lean` has the Farmer-Gonek-Lee kernel `F_1` with
`H* = 0.8686415005` and is a different object. The withdrawn reading conflated
them, and would have sent a session to formalize a generalization of the wrong
theorem. It is the more instructive of the two.

A third recommendation, re-optimizing the certificate window at each
bandwidth, was written into an earlier draft and is killed by §3 rather than
withdrawn on a reading error.

## 6. Corrections owed to the tree

None of them this hunt's mathematics; fixes assigned in `MISSION.md` §11,
which now lists six, the two added by the searches being that
`hunts/wide_search/RESULTS-xiprime.md` cites Alpöge-Furman Remark 7.3 where
the paper says 7.1, and that the Lean dependency cited as
`anthropics/zeta-23-lean` now lives at `anthropics/formal-math`, `zeta23/`.
`docs/35` predates hunt #118's closure and reads as an open opportunity.
`docs/35` and `hunts/outband_intake/RESULTS.md` disagree on the measurement,
`+0.0068` with error `2.2e-3` against `+0.0065` with `1.8e-3`.
`references/papers.md` has **no entry at all** for Baluyot, Goldston,
Suriajaya and Turnage-Butterbaugh, though their Lemma 5 is the arithmetic
engine of this whole line of work. And
`hunts/frontier_map/RESULTS-frontier-map.md` should record that its landscape
now has a theorem attached at each bandwidth.

## 7. Reproduction

```bash
.venv/bin/python hunts/short_interval/verify.py      # the papers' constants
.venv/bin/python hunts/short_interval/landscape.py   # both landscapes, the band price
```

Both are stdlib only, so they also run under a bare `python3` during triage.
`verify.py` exits non-zero if any constant drifts from what the papers print
or from what `frontier.py` computes. `landscape.py` runs pure-Python solves at
`n = 120` to `200` and carries about `1e-5`; it prints the zeta control at
every step so that error is visible rather than assumed. Anything needing more
than four digits should be re-run on the repository's numpy path or with ball
arithmetic.

## The doors

Preliminary: this hunt has measured no ceiling of its own, so the inventory is
what §1 to §4 expose. `MISSION.md` §13 carries the full version with the
information-class column; the ranked summary is:

1. **The band edge at 1**, frozen by the absence of an unconditional upper
   bound on `F` beyond it rather than by choice. Priced as worth more than
   everything else here combined, and **shut by the literature search in
   §4.2**: the required input is a prime-pair fact at second order, blocked
   by parity, and even under RH the best integrated bound tends to `7/8`
   rather than to zero. Would leave the information class; does not open.
2. **The kernel**, fixed to `|alpha|` on the zeta arm while the tree also
   computes the `F_1` landscape that Wang does not. Leaves the class.
3. **The dyadic counting range**, frozen in the Lean bridge by what was
   available to formalize. Stays in the class.
4. **The window shape.** Closed by the measurement in §3, and listed so
   nobody opens it again.
5. **The window's single frequency `sqrt 2`.** `hunts/amtopa_ceiling` proved
   the `2 j pi` harmonics exactly M-orthogonal to it at bandwidth one, so the
   window maximum over the whole coefficient space is the pure `sqrt 2` value.
   Whether that survives at bandwidth theta is unchecked and cheap, though §3
   bounds the prize.

Doors 3, 4 and 5 sit under the configuration ceiling, which is itself a
bandwidth-one number (`0.6818286874638`) and **unmeasured at bandwidth
theta**. Measuring it is `MISSION.md` §7 and it is the stopping criterion for
this whole axis.
