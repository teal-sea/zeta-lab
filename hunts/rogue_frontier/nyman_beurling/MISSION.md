# nyman_beurling: enclosure-checked d_N^2 in the Baez-Duarte criterion

Sub-study of hunt #38 (`hunts/rogue_frontier/MISSION.md` carries the governing
HuntSpec). Opened 2026-08-17.

## Question

Compute the Nyman-Beurling / Baez-Duarte distance

    d_N^2 = inf_{a_1..a_N} || chi_(0,1) - sum_{k<=N} a_k {1/(k t)} ||^2_{L^2(0,infty)}

with rigorous ball arithmetic end to end: exact Gram entries by the Vasyunin
cotangent formula, an arb ball solve of the normal equations, and an enclosure
for every reported d_N^2. Push N as far as one session's budget allows
(powers of 2), then measure the approach of d_N^2 * log N to the conjectured
constant 2 + gamma - log(4 pi) = 0.0461914179... and the conditioning of the
Gram matrix as a function of N.

## Why it is worth a session

Literature numerics (Landreau-Richard 2002) are float runs with no error
control. Prior exact work stops at the formula; nobody appears to publish
d_N^2 with proven enclosures. The repo's own `zeta/criteria.py` computes a
related but different quadratic form (the BBLS basis on L^2(0,1), k >= 2);
this study is the L^2(0,infty) form the Bettin-Conrey-Farmer asymptotic
actually addresses, and the two sequences cross-illuminate.

## Method and oracles

- Gram entries: Vasyunin's formula (two independent published statements
  pinned in `SOURCES.md`), implemented in python-flint arb balls.
- Independent checks: mpmath reimplementation at 50+ digits, direct
  numerical integration of selected entries with a trigamma-exact tail,
  closed forms for the diagonal and the target inner products.
- Solve: `arb_mat.solve`, which proves invertibility and returns enclosures.
  Cross-checked at two precisions, against an mpmath solve at small N, and
  against the residual quadratic form (a rigorous upper bound at any vector).

## Kill conditions (inherited from the parent HuntSpec, specialized)

- Vasyunin values disagree with direct quadrature beyond enclosure widths.
- The arb solve and the mpmath solve disagree at small N.
- d_N^2 fails monotone decrease in N, or the residual form falls below the
  reported ball: either would mean a defect, and the run stops there.

## Scope

Writes only inside `hunts/rogue_frontier/nyman_beurling/`. Grade of every
number here: measured, with enclosure-checked arithmetic where balls are
reported. Nothing in this directory is a result until it leaves `hunts/` by a
sanctioned route, and nothing here is evidence about the truth of RH
(docs/08; Littlewood's caution applies with full force).
