# References — an annotated reading list

Companion to the course in `docs/` (each doc cites what it leans on; this is
the consolidated shelf). **[FREE]** marks items legitimately available online
at no cost. Where no link is given, search the exact title — links rot,
titles do not.

## 1. The primary source

- **Riemann, B. — "Ueber die Anzahl der Primzahlen unter einer gegebenen
  Grösse"** (Monatsberichte der Berliner Akademie, November 1859). Eight
  pages containing the analytic continuation, the functional equation, the
  explicit formula in outline, and the hypothesis, stated in passing.
  Astonishingly compressed; read it *after* Edwards, not before. **[FREE]**
  English translations: David Wilkins' translation (hosted at Trinity College
  Dublin, and widely mirrored) and the appendix of Edwards (below). The Clay
  Mathematics Institute also hosts a scan of the original manuscript.
  *For: everyone, eventually.*

## 2. Books

- **Edwards, H. M. — *Riemann's Zeta Function*** (Academic Press, 1974;
  cheap Dover reprint, 2001). Works through Riemann's memoir line by line,
  developing the analysis as needed; the model for this repo's approach.
  *For: the reader of `docs/01–04`. If you buy one book, buy this one.*
- **Titchmarsh, E. C., revised by D. R. Heath-Brown — *The Theory of the
  Riemann Zeta-Function*** (2nd ed., Oxford, 1986). The professional
  reference: every classical theorem with full proofs, plus Heath-Brown's
  end-of-chapter notes updating each topic. Dry, complete, indispensable.
  *For: looking things up once you know what to look up.*
- **Iwaniec, H. and E. Kowalski — *Analytic Number Theory*** (AMS Colloquium
  Publications 53, 2004). The modern graduate text: zeta in the context of
  the whole family of L-functions, the explicit formula done properly,
  zero-density methods, and the large sieve.
  *For: seeing why "prove it for one L-function, prove it for all" is the
  modern frame (`docs/08`).*

## 3. Surveys and problem statements

- **Bombieri, E. — "Problems of the Millennium: The Riemann Hypothesis"**
  (Clay Mathematics Institute official problem description, 2000). Four
  pages: precise statement, history, consequences, and the standard of proof
  required for the prize. **[FREE]** on the Clay Mathematics Institute
  website (claymath.org). *For: the exact statement of what is open.*
- **Conrey, J. B. — "The Riemann Hypothesis"** (Notices of the AMS, March
  2003, 341–353). The best single survey at graduate-accessible level:
  evidence, equivalents, random matrices, and the state of the art circa
  2003 (little of which has changed). **[FREE]** from the AMS Notices
  archive. *For: the reader who has finished `docs/00` and wants one
  professional overview.*

## 4. Zeros as a spectrum: random matrices and Hilbert–Pólya

- **Montgomery, H. L. — "The pair correlation of zeros of the zeta
  function"** (Proc. Sympos. Pure Math. 24, AMS, 1973, 181–193). Where the
  GUE connection begins: the conjecture R₂(r) = 1 − (sin πr/πr)², proved for
  restricted test functions, plus the famous Dyson teatime story.
  *For: the source behind `docs/06` and `scripts/04_gue_statistics.py`.*
- **Odlyzko, A. M. — the zero computations.** "On the distribution of
  spacings between zeros of the zeta function" (Math. Comp. 48, 1987,
  273–308) and the later unpublished report "The 10²⁰-th zero of the Riemann
  zeta function and 175 million of its neighbors". Massive-scale numerics
  confirming the GUE statistics to extraordinary accuracy at extraordinary
  height. **[FREE]** — Odlyzko keeps his papers and zero tables on his
  University of Minnesota homepage. *For: what serious numerical evidence
  looks like, and its limits.*
- **External zero-table data and formats.** [Odlyzko's official table
  index](https://www-users.cse.umn.edu/~odlyzko/zeta_tables/index.html) hosts
  the six text datasets consumed by `zeta/moments.py`. LMFDB documents the
  [source and provenance](https://www.lmfdb.org/knowledge/show/rcs.source.zeros.zeta),
  exposes the plain `index ordinate` format in its
  [route source](https://github.com/LMFDB/lmfdb/blob/main/lmfdb/zeros/zeta/zetazeros.py),
  and publishes the separate bulk-binary
  [reader](https://github.com/LMFDB/lmfdb/blob/main/lmfdb/zeros/zeta/platt_zeros.py).
  *For: the acquisition and parser contracts in `docs/13`.*
- **Hiary, G. A. and A. M. Odlyzko — "The zeta function on the critical
  line: Numerical evidence for moments and random matrix theory models"**
  (*Math. Comp.* 81 (2012), 1723–1752;
  [author PDF](https://www-users.cse.umn.edu/~odlyzko/doc/zeta.moments.pdf)).
  Documents the high-height value evaluation and integration method behind the
  moments programme. The 2026-08-04 data audit found published results but no
  downloadable dense row table. *For: `docs/13` §§6, 9.*
- **Bober, J. and G. A. Hiary — selected high zeta computations.** Their
  [Bristol pages](https://people.maths.bris.ac.uk/~jb12407/data/zeta/index_Z11.html)
  publish extreme values and plots, useful as computation provenance but not as
  an interval-moment sample. *For: the source audit in `docs/13` §9.*
- **Keating, J. P. and N. C. Snaith — "Random Matrix Theory and
  ζ(1/2+it)"** (*Commun. Math. Phys.* 214 (2000), 57–89;
  [author PDF](https://people.maths.bris.ac.uk/~mancs/papers/RMTzeta.pdf)).
  Derives the random-matrix factor in the general leading conjecture for
  critical-line moments. *For: `moment_reference` and `docs/13` §7.*
- **Conrey, J. B., D. W. Farmer, J. P. Keating, M. O. Rubinstein and
  N. C. Snaith — "Integral moments of L-functions"** (*Proc. London Math.
  Soc.* 91 (2005), 33–104; [arXiv:math/0206018](https://arxiv.org/abs/math/0206018)).
  Gives the arithmetic Euler product and full-main-term recipe, recovering the
  Hardy–Littlewood and Ingham leading terms and the sixth/eighth conjectures.
  *For: the theorem/conjecture split and coefficient convention in `docs/13`.*
- **Conrey, J. B., D. W. Farmer, J. P. Keating, M. O. Rubinstein and
  N. C. Snaith — "Lower order terms in the full moment conjecture for the
  Riemann zeta function"** ([arXiv:math/0612843](https://arxiv.org/abs/math/0612843)).
  Gives the full polynomial coefficient recipe and the published `k=3` table.
  *For: `moment_polynomial(3)` and the convention checks in `docs/13` §7.*
- **Rubinstein, M. O. and S. Yamagishi — "Computing the moment polynomials of
  the zeta function"** ([arXiv:1112.2201](https://arxiv.org/abs/1112.2201)).
  Gives a stable coefficient algorithm and the reported stable digits used for
  the degree-16 `k=4` polynomial; these are not interval enclosures.
  *For: `moment_polynomial(4)` and `docs/13` §7.*
- **Berry, M. V. and J. P. Keating — "The Riemann zeros and eigenvalue
  asymptotics"** (SIAM Review 41, 1999, 236–266); also "H = xp and the
  Riemann zeros" (1999). The physicists' Hilbert–Pólya: semiclassical
  analogies between the explicit formula and trace formulae, and the H = xp
  proposal. *For: `docs/06` §Berry–Keating; inspiration, honestly labelled
  as not a construction.*

## 5. The de Bruijn–Newman frontier (the `heatflow.py` story)

- **Rodgers, B. and T. Tao — "The de Bruijn–Newman constant is
  non-negative"** (arXiv:1801.05914, January 2018; published in Forum of
  Mathematics, Pi, 2020). Proof that Λ ≥ 0 — Newman's 1976 conjecture — via
  the rigidity of backward-heat-flow zero statistics. With RH ⟺ Λ ≤ 0 this
  makes RH ⟺ Λ = 0. **[FREE]** on arXiv. *For: the theorem `docs/05` and
  `zeta/heatflow.py` are built around.*
- **Polymath, D. H. J. (Polymath15, led by T. Tao) — "Effective
  approximation of heat flow evolution of the Riemann ξ function, and a new
  upper bound for the de Bruijn–Newman constant"** (Research in the
  Mathematical Sciences 6, 2019, paper 31). The collaborative computation
  pushing de Bruijn's Λ ≤ 1/2 down to Λ ≤ 0.22, with fully effective error
  control — the rigorous version of what `zeta/heatflow.py` does
  illustratively. **[FREE]** on arXiv. *For: what "numerics with proofs
  attached" means; the Platt–Trudgian verification then gives the current
  record Λ ≤ 0.2.*

## 6. Recent unconditional progress

- **Guth, L. and J. Maynard — "New large value estimates for Dirichlet
  polynomials"** (2024). The first improvement since Ingham (1940) on the
  zero-density exponent: roughly, fewer possible zeros far from the critical
  line, improving prime-distribution consequences unconditionally. Not a
  route to RH — a sharpening of how far from RH we are allowed to be.
  **[FREE]** on arXiv. *For: what genuine unconditional progress looks like
  in this subject, per `docs/08`.*

## Reading orders

- *Shortest honest path*: Bombieri → Conrey → Edwards chs. 1–3.
- *This repo's spine*: Edwards (for `docs/01–04`) → Montgomery + Odlyzko
  (for `docs/06`) → Rodgers–Tao + Polymath15 (for `docs/05`).
- *Calibration*: Guth–Maynard, to see the size of a genuine step.
