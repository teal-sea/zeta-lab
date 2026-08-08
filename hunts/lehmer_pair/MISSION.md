# MISSION: The closest call — Lehmer's pair under ball arithmetic

**Agent Persona:** The Hunter (unsupervised-fun edition)
**Scope:** `hunts/lehmer_pair/` only. Nothing outside this directory is
modified except the case-log entry in `hunts/README.md`.

## Objective

Lehmer's phenomenon is the place RH came closest to being false below
height 10⁴: γ₆₇₀₉ ≈ 7005.0629 and γ₆₇₁₀ ≈ 7005.1006 sit 0.0377 apart —
24× tighter than the local mean spacing — and between them Hardy's Z(t)
climbs to only ≈ +0.004 before diving back. Had that bump failed to cross
zero, two zeros would have left the critical line.

The repo has recomputed the pair with floats (`docs/05`) but has never
pointed the ball-arithmetic arm at it. The hunt asks one question:

> **Do the enclosures of `zeta.rigor` decide, on both backends, that the
> near-miss is real — that the bump genuinely clears zero — and how much
> precision does the closest call actually cost?**

## Instruments

`probe.py`, which runs five experiments and writes `results.json` +
`lehmer_zoom.png`. The only rigor-layer entry points used are
`rigor.proven_sign` and `rigor.enclose_Z`; the grid scans are built on
those two so the probe owns its grid and its undecided-point accounting.
The strongest word this hunt uses is *decided*: an enclosure `[lo, hi]`
came back with `lo > 0` or `hi < 0`, an exact comparison on exact
endpoints. The reserved word for that regime belongs to `zeta/rigor.py`
and appears nowhere in this directory — the case log names it.

1. **Three-point sign pattern** — sign of Z at exact rationals flanking
   and inside the pair, both backends. Pattern −,+,− brackets ≥ 2 line
   zeros.
2. **Dense window scan** — sign changes on [7004.9, 7005.3] with a grid
   ~7× finer than the pair, both backends; the window contains no other
   zeros (γ₆₇₀₈ = 7004.04, γ₆₇₁₁ = 7006.74).
3. **Lesion: the default grid policy** — the default scan step at this
   height is mean_spacing/20 ≈ 0.045, *wider than the whole Lehmer gap*.
   Sweep the window phase and measure how often that grid sees the pair
   at all.
4. **Precision response** — enclosure width of Z at the bump vs prec_bits,
   both backends; and the decision cost (bits needed to settle a sign) as
   the probe point slides toward γ₆₇₀₉ at distances 10⁻³ … 10⁻¹².
5. **Rival (gate #1)** — Davenport–Heilbronn owns the *failed* version of
   this bump: near its off-line zero 0.8085 + 85.6993i, Z_dh approaches
   zero and never crosses (2 strip zeros, 0 line crossings — pinned by
   `tests/test_epstein.py`). Measure the closest approach so the two bumps
   can be shown side by side. This is the check that "a small bump" alone
   distinguishes nothing; what distinguishes is *crossing*.

## Rules of engagement

Repo-wide rules apply (`.venv` python, `mp.workdps`, Agg before pyplot,
honest scope). Nothing here is evidence for RH; the deliverable is sign
facts at named rationals decided by enclosure, plus measured instrument
behaviour. The Davenport–Heilbronn scan is the float regime — accurate,
a weaker claim, and labelled as such.
