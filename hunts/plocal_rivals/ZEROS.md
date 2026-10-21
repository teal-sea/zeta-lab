# ZEROS: where F_17 and F_73 vanish off the critical line, below height 1000

Hunt #149, step 4 of `MISSION.md`. Instruments: `census.py` (the census and its two
routes), `arb_route.py` (route B), `abscissa.py` (the strip), `assemble.py` (PARI third
routes, the audit, and the table lines below). Data: `zeros.json`. Every number here is
pinned by `test_rivals.py`: the table lines are rendered from `zeros.json` and checked
verbatim against this file, both totals are recomputed live on both routes, and the
audit is run on the file and on six planted corruptions of it. Nothing here is a result
(`hunts/README.md`), and the census says nothing above its last boundary.

**Grades.** Route A is *measured* (one floating-point route). Route B is
*enclosure-carrying given three stated inputs*: the classical functional equation and
Gauss-sum root number of Dirichlet L-functions, Rademacher's convexity bound for
L(s, chi) (cited from memory, not re-derived, and guarded by measured checks), and the
segment decision rule of `hunts/lambda_dh_bounds/winding.py`. The two routes share no
evaluation code. Every count below is the same on both, so the counts are *hardened*;
as a composite, the census takes the grade of its weakest step, the cited bound.
PARI/GP is a third, measured route for the locations.

## 1. What is counted, and when a window is complete

F_q = c L(s, chi) + conj(c) L(s, chi-bar) with c = (1 - i k)/2 (`MATCH.md` section 1).
Both characters are even, and G_q(s) = (q/pi)^{s/2} Gamma(s/2) F_q(s) = G_q(1 - s) is
real on the critical line. **A zero here means a zero of G_q**, a nontrivial zero of F_q;
the zeros of F_q at s = 0, -2, -4, ..., which the poles of Gamma(s/2) cancel, are not
counted.

The census cuts 0 < Im s < T into windows of height about 8, each boundary at the grid
maximum of |Z| between two consecutive sign changes. In each window, each route computes

- n_box: the number of zeros of G_q in the window, from the folded argument principle
  N(0, T) = Psi(T)/pi at the two ends (`rivals.py`, the comment above `_fp_table`): the
  reflection s -> 1 - conj(s) maps G_q to its conjugate, so the arg change around the
  strip [1 - sR, sR] is twice the arg change along its right half, with sR = 1.7 above
  the coefficient-domination abscissa (section 5);
- n_line: the sign changes of Hardy's Z on the route's own grid, read with the route's
  own signs at the two ends;
- n_right: the zeros found in Re s > 1/2.

Every zero rho off the line has the mirror 1 - conj(rho) in Re s < 1/2, and every sign
change marks a zero on the line, so n_box >= n_line + 2 n_right always. **When equality
holds the window is complete**: every zero on the line is simple and sits at a sign
change, and the zeros found in Re s > 1/2 are all of them. A window that does not close
is reported, never absorbed; a route may close it only with its own finer line scan.

**Route A** (`rivals.py`, mpmath's `fp` context): Z on a grid of 1/12 of the mean zero
gap (at most 0.1); the folded count at each boundary, rounded to the nearest integer,
with the distance to it (the integrality defect) recorded and audited; where n_box
exceeds n_line, winding counts on right boxes [1/2 + 0.01, 1.7] x [window], bisected
down to boxes holding one zero, then Newton. **Route B** (`arb_route.py`, python-flint
0.9.0 as installed in this tree's venv on 2026-10-21): its own character from flint's
Conrey table and its own k as an Arb ball from its own Gauss sum; decided signs of Z on
its own dyadic grid (1/10 of the mean gap, at most 1/8, offset start); decided folded
counts, each an Arb ball that must pin one integer; and a zero
counts for route B only through its own decided box of half-width 2^-30 with winding
number 1, lying wholly inside the window and in Re s > 1/2. Route B's segment rule needs
a bound M2 for |F''|; it takes it from Cauchy's estimate on Rademacher's bound
|L(s, chi)| <= (q |1 + s| / (2 pi))^{(1 + eta - sigma)/2} zeta(1 + eta). Measured against
Arb's own |L(s, chi)| on a 7 x 6 grid spanning the census (Re s from -0.4 to 1.4,
heights 1 to 999.5), the cited bound holds with a factor above 2 to spare (largest ratio
0.35 for q = 17, 0.45 for q = 73), and the M2 actually used sits above Arb jets of F''
along a sample segment. Route B takes its window boundaries and box centres from
route A: that steers placement only, since a wrong placement makes a decision fail,
never pass.

## 2. The census

| | q = 17 | q = 73 |
|---|---|---|
| last boundary T | 1000.306640625 | 1000.0185546875 |
| windows | 125 | 125 |
| zeros of G_q with 0 < Im s < T, route A = route B | 1099 | 1330 |
| sign changes of Z on the line, route A = route B | 1007 | 1292 |
| zeros in Re s > 1/2 (each with its mirror in Re s < 1/2) | 46 | 19 |
| lowest zero off the line | 0.6670253 + 25.6907716 i | 0.5763004 + 91.8501602 i |
| largest real part found | 0.8482656 at height 775.0657 | 0.7324814 at height 298.5913 |
| smallest real part found | 0.5508023 at height 603.3177 | 0.5290303 at height 521.4983 |
| windows route A rescanned 8 times finer | 48, 91 | 103 |
| windows route B rescanned 8 times finer | 48, 91 | 103 |
| largest integrality defect of a route A folded count | 7.4e-13 | 4.5e-13 |
| largest distance from a route A root to PARI's | 4.0e-13 | 7.6e-13 |

The parity check sign Z(T_j) = (-1)^{N(0, T_j)} holds at every boundary on both routes,
for both q. A rescanned window is one that did not close on the route's first grid; the
route closed it with its own line scan at 8 times the density, which found sign changes
the first grid had stepped over (they come in pairs, since the signs at the two ends are
fixed). For comparison, Davenport-Heilbronn (q = 5, P = 1) first leaves the line at
height 85.699 (`tests/test_epstein.py`); F_17 leaves it lower, F_73 a little higher.

## 3. Every zero found off the line

Route A's values; each lies inside route B's decided box of half-width 2^-30, and so
does PARI's value (section 4). Each zero's mirror 1 - conj(rho) is a zero too.

| q | # | Re rho | Im rho |
|---|---|---|---|
| 17 | 1 | 0.667025 | 25.690772 |
| 17 | 2 | 0.840762 | 99.877841 |
| 17 | 3 | 0.564136 | 162.255045 |
| 17 | 4 | 0.825744 | 196.940899 |
| 17 | 5 | 0.634438 | 209.350559 |
| 17 | 6 | 0.754854 | 220.184746 |
| 17 | 7 | 0.589182 | 232.291749 |
| 17 | 8 | 0.585906 | 248.518448 |
| 17 | 9 | 0.684568 | 282.983254 |
| 17 | 10 | 0.717811 | 306.591481 |
| 17 | 11 | 0.660686 | 322.590406 |
| 17 | 12 | 0.680821 | 345.554727 |
| 17 | 13 | 0.695926 | 368.659619 |
| 17 | 14 | 0.661152 | 392.534339 |
| 17 | 15 | 0.576439 | 419.700185 |
| 17 | 16 | 0.654920 | 426.753010 |
| 17 | 17 | 0.830502 | 442.953692 |
| 17 | 18 | 0.679906 | 454.950650 |
| 17 | 19 | 0.682797 | 471.228650 |
| 17 | 20 | 0.710796 | 500.703727 |
| 17 | 21 | 0.660920 | 506.088754 |
| 17 | 22 | 0.819116 | 529.234634 |
| 17 | 23 | 0.750061 | 568.435133 |
| 17 | 24 | 0.760624 | 587.050867 |
| 17 | 25 | 0.550802 | 603.317690 |
| 17 | 26 | 0.556708 | 642.888459 |
| 17 | 27 | 0.658739 | 655.203365 |
| 17 | 28 | 0.663654 | 661.377071 |
| 17 | 29 | 0.762458 | 665.520077 |
| 17 | 30 | 0.647292 | 689.062208 |
| 17 | 31 | 0.589113 | 700.524741 |
| 17 | 32 | 0.752614 | 723.396502 |
| 17 | 33 | 0.597100 | 751.994557 |
| 17 | 34 | 0.848266 | 775.065740 |
| 17 | 35 | 0.604726 | 809.982335 |
| 17 | 36 | 0.691480 | 825.881430 |
| 17 | 37 | 0.615911 | 833.114131 |
| 17 | 38 | 0.738012 | 849.354585 |
| 17 | 39 | 0.693660 | 872.096099 |
| 17 | 40 | 0.785818 | 888.301944 |
| 17 | 41 | 0.615073 | 895.568686 |
| 17 | 42 | 0.695662 | 900.281157 |
| 17 | 43 | 0.645154 | 930.180881 |
| 17 | 44 | 0.635032 | 935.458728 |
| 17 | 45 | 0.629506 | 958.354040 |
| 17 | 46 | 0.843457 | 997.914504 |
| 73 | 1 | 0.576300 | 91.850160 |
| 73 | 2 | 0.566682 | 267.105747 |
| 73 | 3 | 0.732481 | 298.591339 |
| 73 | 4 | 0.681519 | 337.857906 |
| 73 | 5 | 0.632783 | 463.008280 |
| 73 | 6 | 0.529030 | 521.498339 |
| 73 | 7 | 0.624249 | 524.578984 |
| 73 | 8 | 0.652947 | 595.295000 |
| 73 | 9 | 0.614657 | 641.864981 |
| 73 | 10 | 0.645454 | 673.301990 |
| 73 | 11 | 0.556768 | 693.221879 |
| 73 | 12 | 0.639045 | 728.101028 |
| 73 | 13 | 0.555007 | 731.615325 |
| 73 | 14 | 0.577700 | 744.189859 |
| 73 | 15 | 0.560080 | 766.885879 |
| 73 | 16 | 0.690816 | 857.021171 |
| 73 | 17 | 0.575463 | 872.778583 |
| 73 | 18 | 0.604300 | 938.376644 |
| 73 | 19 | 0.560445 | 977.401756 |

## 4. Locations on a third route

PARI/GP (version 2.17.2 through cypari2, as installed in this tree's venv on 2026-10-21)
builds its own character (`znstar`, `chareval`) and its own k from `lfunrootres`, and
shares no code with mpmath or Arb.

- **Every zero in section 3** was re-located by Newton on q^{-s} sum_a b(a)
  zetahurwitz(s, a/q) from route A's root, at 45 digits. Every PARI root lies inside
  route B's box; the largest distance from a route A root to PARI's is in the table of
  section 2.
- **The lowest zero of each q** was also located on two routes that do not use the
  Hurwitz formula: PARI's lfun of F's own Dirichlet series, declared as a degree-1
  self-dual L-function with gamma factor [0], conductor q and root number +1, which
  reads only the coefficients b(n) and PARI's functional-equation machinery; and lfun of
  the two genuine characters, combined with A = (1 - i k)/2. Truncated to 40
  significant digits, the three PARI routes give:

      F_17:  0.6670253335339771563145982207134238324630 + 25.69077157780038556074134204260582393293 i
      F_73:  0.5763004291831510525962541753564107750583 + 91.85016017366962695705346968732686963823 i

  For F_17, route B's Arb polish at 160 and 256 bits and route A's mpmath polish at
  dps 30 agree with this value too.
- **A precision artifact, caught by the standing rule.** At real precision 45, PARI's
  generic lfun on F_73's own series lands about 1e-21 from the value above (it loses
  digits with height on a closure-defined series); at precision 60 it agrees to about
  1e-37, and at 80 to every digit shown. The zero holds still and the artifact moves,
  so the lfun route is run at precision 80 in `assemble.py`, and the test pins all
  three distances.

## 5. The strip: how far from the line a zero can be

`abscissa.py` ports the Euler-phase method of `hunts/lambda_dh_bounds/strip2.py`
(`STRIP2.md`) from q = 5 to any prime q = 1 mod 4: for Re s > 1, F_q(s) = 0 forces
L(s, chi)/L(s, chi-bar) = e^{i(pi + theta)}, the quotient is an Euler product over the
non-residue primes alone, each factor has argument at most 2 arctan(p^{-sigma}), and
the sum Theta_q(sigma) of those bounds falls below pi - |theta| at sigma*. Every step is
an Arb ball (sieve limit 10^5, tail closed through the Euler products of zeta and the
Legendre-symbol L-function). At q = 5 it returns strip2's enclosure of DH's abscissa.

| | q = 5 (DH) | q = 17 | q = 73 |
|---|---|---|---|
| first non-residue prime | 2 | 3 | 5 |
| decided sigma*: every zero of G_q has 1 - sigma* < Re s < sigma* | 1.12036249819 | 1.09896904163 | 1.0445906373 |
| coefficient-domination root (`strip.py`'s method), below the census edge 1.7 | | 1.5842597817 to 1.5842597818 | 1.6148802929 to 1.6148802930 |

So no zero of G_17 is farther than 0.59896904163 from the line, and no zero of G_73
farther than 0.5445906373. In these three cases the strip narrows as the first
non-residue moves out (2, 3, 5), which fits the mechanism: the phase budget comes only
from the non-residue primes. The largest real part found below height 1000 is 0.8482656
for q = 17 and 0.7324814 for q = 73, well inside. That gap is not evidence that the
strip is loose. Saias and Weingartner (Acta Arith. 140 (2009); cited from memory, not
consulted here) show that a Dirichlet series with periodic coefficients has infinitely
many zeros in Re s > 1 unless it is a Dirichlet polynomial times a Dirichlet L-function;
whether F_q escapes that exception was not checked here. For Davenport-Heilbronn,
Bombieri and Ghosh's converse says the abscissa is attained, and this tree has not
verified it (`hunts/lambda_dh_bounds/STRIP2.md` section 7). Neither is used.

## 6. What this shows, and what it does not

- **It shows** that F_17 and F_73 have zeros off the critical line below height 1000,
  on two code-disjoint routes that agree on every count and a third that agrees on every
  location: the one numerical input of `OBSTRUCTION.md`. The lowest are at heights
  25.69 (q = 17) and 91.85 (q = 73).
- **Each such zero is a zero of F, not of L(s, chi).** At a zero of F,
  A L(s, chi) = -conj(A) L(s, chi-bar), so the two moduli agree and neither vanishes;
  at F_17's lowest zero |L(s, chi)| = 0.3396173662371325 and at F_73's
  0.42626225788779205362 (measured, pinned). The zero is a phase coincidence of two
  non-vanishing L-values.
- **It does not show** anything above the last boundary, anything about the zeros of
  L(s, chi) itself, or anything about RH. The counts are a finite computation, not a
  theorem; route B's counts carry enclosures only given the cited bound and the
  classical functional equation, and nothing here is kernel-checked.
