# MISSION: support arm 517b887f (Erdős #126, original-proof lane)

**Bounded question, set by the parent run 0897a5a7 / Hunt #91 (`r_186989/`):**
reconstruct the Erdős–Turán 1934 proof in modern notation, isolate every place
the factor 2 per prime is lost, and test whether processing primes jointly,
retaining valuation information, or changing the order can provably replace
$2^k$ by $(2-\delta)^k$. Return a proved improvement, or a barrier, or the
smallest missing lemma.

**May touch:** this directory, and the Hunt #92 entry in `hunts/README.md`.

**May not touch:** any other `hunts/` directory, `zeta/`, `harness/`, `lean/`,
`meta/`, or any root markdown file.

**Standing:** nothing here is evidence for or against RH (`docs/08`). The
reserved word belongs to `zeta/rigor.py` and the Lean arm and is not used here.
Everything in `RESULTS.md` is either a proof written out in full or a
measurement from `probe.py` (stdlib only, ~30 s, writes `results.json`).
