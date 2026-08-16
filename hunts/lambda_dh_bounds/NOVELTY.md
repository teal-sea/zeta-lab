# Novelty record for `lambda_dh_bounds`

Recorded 2026-08-16, from a web sweep run before the hunt opened. Per the
house rule (`ontology/knownness.py`: an unrun check can never read as absence
of prior art), this file says exactly what was searched and what it found.
Nothing below is a claim that anything is *novel*; it is the record a novelty
claim would have to stand on, plus the caveats it would have to carry.

## What is published, and the delta this hunt targets

- **Dobner 2020** (*A proof of Newman's conjecture for the extended Selberg
  class*, arXiv:2005.05142). Theorem 1: for every F in the extended Selberg
  class S# there is a real Lambda_F with all zeros of the deformation on the
  critical line iff t >= Lambda_F (the half-line structure). Theorem 2:
  Lambda_F >= 0. The Davenport-Heilbronn function is in S# (absolutely
  convergent series for Re s > 1, entire completion, functional equation
  with gamma factor (pi/5)^{-(s+1)/2} Gamma((s+1)/2); no Euler product is
  required for S#). So existence, finiteness and nonnegativity of Lambda_DH
  are published, and strict positivity is an immediate corollary of
  Theorem 1 plus any computed off-line zero (Spira 1994). Dobner names no
  member and gives no number. **The delta: quantitative bounds.**
- **Newman-Wu 2020** (Bull. AMS 57, arXiv:1901.06596) computes a strictly
  positive constant of de Bruijn-Newman type exactly, Lambda(rho) = ln 2,
  for a concrete three-atom probability *measure*. Any phrasing of the form
  "first strictly positive constant of this type for a concrete object" is
  therefore false. The sanctioned phrasing is: first quantitative two-sided
  bounds for the de Bruijn-Newman constant of an RH-violating L-function.
- **The zeta record** for calibration: 0 <= Lambda_zeta <= 0.22
  (Rodgers-Tao arXiv:1801.05914; Polymath 15 arXiv:1904.12438), Lambda_zeta
  < 1/2 (Ki-Kim-Lee 2009), historical lower bounds all negative, ending at
  -1.15e-11 (Saouter-Gourdon-Demichel 2011).
- **Generalized Newman lines, all at negative-or-zero values**: quadratic
  Dirichlet L-functions (Stopple arXiv:1301.3158; Andrade-Chang-Miller
  arXiv:1310.3477; best concrete bound Lambda_D > -1.17e-7), function
  fields (Chang-Mehrle-Miller-Reiter-Stahl-Yott arXiv:1411.2071, constants
  <= 0 with sup 0 attained). No RH-violating function is treated anywhere
  in this line.
- **DH zero distribution context**: off-line zeros exist
  (Davenport-Heilbronn 1936), computed instances Spira (Math. Comp. 1994)
  and Balanzario-Sanchez-Ortiz (Math. Comp. 76, 2007); DH also has zeros
  with Re s > 1 (discussed in Ferry et al., arXiv:1602.06328), which is why
  the zero strip needs the coefficient-domination argument; line-zero
  counts Karatsuba 1990/91 and Gritsenko 2017 (Proc. Steklov 296). Note:
  arXiv:2503.24275 (2025) claims DH zeros lie only on the critical line;
  this contradicts the computed zeros above and the repo's own pinned
  50-digit zero, and is treated as unsound.
- **de Bruijn 1950** (Duke Math. J. 17, 197-226), Theorem 13, is the upper
  bound's engine. The restatements consulted (Csordas-Norfolk-Varga 1988;
  Ki-Kim, J. Anal. Math. 91 (2003), where de Bruijn's class conditions are
  integrability, realness/evenness in the sense F(-t) = conj F(t), and
  decay O(e^{-|t|^b}) with b > 2) require **no positivity of Phi**, which
  matters here because Phi_DH has mixed-sign coefficients. The
  all-zeros-in-strip form (zeros of H_0 in |Im z| <= Delta implies H_t
  real-rooted for t >= Delta^2/2) is what the historical citations
  attribute to Theorem 13; confirming that exact form against the original
  text is a standing task of this hunt, and the upper bound is withdrawn if
  it fails (see the kill conditions).

## Searches run (2026-08-15/16)

"de Bruijn-Newman" + "Davenport-Heilbronn"; "de Bruijn-Newman" + Epstein;
Newman's conjecture Dirichlet L-functions (Stopple; ACM; CMMRSY); Ki-Kim-Lee
upper bound; CNV/Odlyzko lower-bound history; "Davenport-Heilbronn" + heat
flow / backward heat; de Bruijn 1950 Theorem 13; Odzak-Smajlovic Li
coefficients for DH-class functions; arXiv 2023-2026 sweeps for DH zeros;
Dobner full text; Newman-Wu full text; Gritsenko 2017; arXiv:2602.20313
(Polya frequency order of the zeta kernel, 2026, evidence the niche is
active). **No publication was found attaching any number, or any heat-flow
computation, to the de Bruijn-Newman constant of DH or of any RH-violating
function.**

## Standing caveat

One item could not be read: an academia.edu preprint (id 166936409, posted
about June 2026, HTTP 403 to every automated fetch attempted) whose title
concerns off-line zeros of the Riemann xi function with a collision model,
and which co-mentions de Bruijn-Newman and Davenport-Heilbronn; the title
suggests DH appears as a negative control rather than as the object being
bounded, but that is an inference from a title. Until a human reads it, the
novelty claim carries this caveat by name. Its provenance should also be
checked against this laboratory's own sibling outputs before it is treated
as external prior art.
