# RESULTS: `rh_height_lean` (hunt #137), T = 50 and T = 100

**Grade: kernel-checked by Lean's kernel** (Lean v4.35.0-rc2, Mathlib
065356127b1dc0016f66b7283ce0ce2c4055aa55, zero `sorry`, axioms `propext`,
`Classical.choice`, `Quot.sound` only). The independent `con-ron --verified`
checker accepted the exported whole closure on 2026-10-24. Earlier bounded
attempts remain inconclusive, not rejected.

## The theorems

In `lean/RHHeight/Main.lean`, for Mathlib's own `riemannZeta`:

- `RHHeight.rh_height_fifty : RHHeight.RHHeight50`. Every zero `rho` with
  `0 < Re rho < 1` and `0 < Im rho <= 50` has `Re rho = 1/2` and
  `analyticOrderAt riemannZeta rho = 1`.
- `RHHeight.zero_count_fifty : RHHeight.ZeroCountUpTo 50 10`. There are exactly 10
  distinct such zeros.
- `RHHeight.rh_up_to_height_fiftytwo : RHHeight.RHUpToHeight 52`, the same statement to
  height 52, and `RHHeight.ncount_three_fiftytwo : Zeta23.Ncount 3 52 = 10`, the count
  with multiplicity for `3 < Im rho <= 52`.

The statements are the definitions in `lean/RHHeight/Statement.lean`. They quantify over
`riemannZeta` directly, with no auxiliary hypothesis.

The second target is proved in `lean/RHHeight100/Main100.lean`. `lean/CheckMain100.lean`
pins its unfolded type directly to Mathlib's `riemannZeta`:

- `RHHeight100.rh_height_hundred : RHHeight.RHHeight100`. For **every** zero `ρ`
  with `0 < Re ρ < 1` and `0 < Im ρ ≤ 100`, `Re ρ = 1/2` and
  `analyticOrderAt riemannZeta ρ = 1`.
- `RHHeight100.zero_count_hundred : RHHeight.ZeroCountUpTo 100 29`.
  The set of **distinct** zeros in precisely that open strip, positive-ordinate,
  upper-endpoint-inclusive window has cardinality 29.
- `RHHeight100.ncount_three_hundred : Zeta23.Ncount 3 100 = 29` counts with
  multiplicity in the smaller window `3 < Im ρ ≤ 100`. The low-height exclusion
  covers `0 < Im ρ ≤ 3`.

These final statements have no external computation as a hypothesis. The count
and simplicity are separate conclusions, not consequences inferred solely from
nineteen new sign changes.

## How it is proved

`Skeleton.lean` reduces the statement to four hypotheses, and each piece discharges one:

| Piece | File | What it proves |
|---|---|---|
| Gamma-side increment | `GammaIncrement.lean` | `92/10 <= integral of mu over [3, 52] <= 109/10`, from the vendored Stirling bound `digamma_stirling` |
| Horizontal legs | `HorizontalLegs.lean` and `Legs*.lean` | `Re zeta > 0` on `[1/2, 2] + 3i` and `[1/2, 2] + 52i`, with the two end arguments enclosed, from interval boxes the kernel decides |
| Exact argument | `ExactArgument.lean` | under that positivity, the vendored `zeta23` folded argument principle is the exact identity `Ncount T1 T2 = integral of mu + (arg zeta(1/2 + i T2) - arg zeta(1/2 + i T1))/pi` |
| Low height | `LowHeight.lean` | no zero with `0 < Im rho <= 3`, from hunt #132's Euler-Maclaurin representation at `N = 1` |

The three enclosures put the count for `3 < Im rho <= 52` strictly between 9 and 11, so it
is 10. Hunt #133's ten distinct zeros on the line lie in that window, so they are all of
its zeros, and each is simple. `LowHeight` covers `0 < Im rho <= 3`.

At height 100 the proof reuses `ExactArgument` and `LowHeight`, encloses the
Gamma increment over `[3, 100]` between 28.1 and 29.7, and proves positivity
on the top horizontal leg at ordinate 100. The resulting integer count lies
strictly between 28 and 30. Nineteen generated boxes locate additional zeros
on the critical line beyond hunt #133's ten; matching all 29 to the contour
count excludes off-line and multiple zeros. See `RHHeight100/Main100.lean` and
`RHHeight100/Skeleton100.lean` for the exact assembly.

## Checks

- Each piece was compiled once by its builder and again by a separate checker from its
  own from-source build, on 2026-10-21.
- The integrated build ran on 2026-10-22 from 04:28 to 04:47 UTC on the campaign box:
  `LAKE_DIR=<root>/lean/.lake bash hunts/rh_height_lean/lean/build.sh --full <OUT>`.
  It compiled 74 modules from source plus seven check files and exited 0 with no error.
- `python3 lean/check_axioms.py <log> --full` accepted all 72 axiom reports with only the
  three standard axioms.
- Numerical cross-check, not part of the proof: mpmath `nzeros(50) = 10` and
  `nzeros(52) = 10`, with `gamma_10 = 49.7738...` and `gamma_11 = 52.9703...`.

In the paths below, `<bundle>` is the laboratory's local evidence bundle for this proof
(source snapshot, logs, receipts and SHA-256 manifests), kept but not published, and
`<toolchain>` is the pinned Lean v4.35.0-rc2 toolchain directory.

**Height-100 clean-source build, 2026-10-23.** With the pinned Lean toolchain
and root package's Mathlib checkout, `build.sh --full100` exited 0 from source
at 21:07 UTC after starting at 18:59 UTC. Its retained receipt is
`<bundle>/evidence/full100/receipt.txt`;
the unpublished local bundle has `build.log`, 102 `.olean` objects, `object-hashes.txt`,
`source-hashes.txt`, `rh100-source-hashes.txt`, and `audit.log`. The **final**
`check_axioms.py --full100` run exited 0 and accepted exactly 100 reports,
allowing only the three standard axioms. The receipt also records an initial
`audit_exit=1`; this was not the final audit and is not silently counted as a
pass. `CheckMain100.lean` checked the unfolded final statements. The combined hunt,
docs numbering, doors and probe-discipline suite passed 103 tests; the recorded
context check and diff check exited 0 (`full100/tests.log`). This is a
Lean-kernel source build and axiom audit, not an independent checker verdict.

**Earlier independent attempts, inconclusive.** Retained details are in
`<bundle>/evidence/independent100/VERDICT.md`
and sibling receipts, plus `evidence/fresh100/status.json`. The exported
closure of the three final declarations was produced successfully. `con-ron
--verified` reached the 60,000 of 81,674 progress marker before the first
1,200-second wall bound; its 3,600-second retry stopped after 1,800 seconds
without another `--progress=5000` marker (`conron-retry3600.status.json`).
That observation bounds only marker visibility: fewer than 5,000 completions
since the last marker, not zero completions or a stalled checker. A subsequent
8-worker `--progress=1` diagnostic on the unchanged export and checker binary
completed 61,363/81,674 checks through the 1,200-second wall stop (SIGTERM,
exit -15), with at most 84.089 seconds between logged completions and peak
sampled tree RSS 3,604,783,104 bytes. Its six byte-matched files are appended
at `<bundle>/evidence/gate8/`;
`gate8-sha256.json` gives their SHA-256 hashes and byte counts without changing
the original evidence or source manifests. The archive README's older exact-set
verification snippet predates this append: exclude `evidence/gate8/` when
checking `evidence-sha256.json`, then verify its six files against
`gate8-sha256.json` separately. NanoDa with only the standard
axioms permitted was stopped at its 43 GiB descendant-RSS bound without a
checked-declaration verdict. `leanchecker --fresh RHHeight100.Main100`, a fresh
replay using Lean's own kernel, hit its 1,800-second wall bound without output
(`fresh100/status.json`). None of these earlier attempts accepted or rejected
the theorem; the subsequent completed gate below changes the overall verdict.

**Independent whole-closure acceptance, 2026-10-24.** The unchanged exported
closure of `RHHeight100.rh_height_hundred`, `RHHeight100.zero_count_hundred`,
and `RHHeight100.ncount_three_hundred` was checked with the independent
`con-ron` binary in verified mode. The exact command recorded in the local
receipt is:

```bash
<toolchain>/bin/con-ron \
  --verified --jobs=8 --progress=1 \
  <bundle>/evidence/independent100/rh100.ndjson
```

The receipt at `<bundle>/evidence/gate3h-20261024/receipt.json`
records exit 0, `stop_reason: null`, and 81,674/81,674 completed checks.
`stdout.log` says `con-ron: accepted 82680 declarations (--verified)`;
`stderr.log` says `con-ron: check done: 81674/81674`. Progress also names the
three final declarations and the count assembly. The export SHA-256 is
`16ad4200653aa74e72a6d7cfd0085449050dcaa5d3b496ed774cda56c4c3f2b9`;
the checker binary SHA-256 is
`4e5616d94374cae37324dad2594f6230c2bb2297240249fc78ff508f3bc5acef`.
Both match the receipt's before and after hashes and the retained live bytes.
This is second-kernel acceptance of that export, not a separate NanoDa success,
outside review, a new proof of unbounded RH, or publication. The raw receipt
and logs are durable locally and not part of the earlier evidence manifest.

**Reruns without a wall bound, 2026-10-26.** Both inconclusive checkers were
rerun on the swarm box with no wall limit, an unlimited stack, and one stop
rule: a 20 GiB host MemAvailable floor. The inputs matched their recorded
SHA-256 hashes: the export (`16ad4200…`), `nanoda_bin` (`8241c5e6…`),
`leanchecker` (`9e36e955…`) and `Main100.olean` (`c78cddfd…`). The other 101
project objects matched `object-hashes.txt`. The Mathlib and dependency
objects came from a build at the same pinned revisions.

- **`leanchecker --fresh RHHeight100.Main100` exited 0** after 1 h 39 min 41 s,
  at a peak sampled RSS of 8,485,968 KiB. `--fresh` imports the module and
  replays every constant of its closure, Mathlib included, into an empty kernel
  environment. A kernel rejection raises and exits non-zero (a missing module
  was shown to exit 1), and success is silent. This is a fresh replay by
  Lean's own kernel, which its docstring calls "not an external verifier". It
  is not a third independent checker.
- **NanoDa stopped again without a verdict.** Its config was unchanged apart
  from paths: standard axioms only, unpermitted axioms a hard error. It hit the
  memory floor after 24 min 20 s at 44,674,696 KiB, still growing. A NanoDa
  verdict needs a machine with more free memory.

The receipts and every attempt are in the local rerun directory
`rh100-rerun-20261026`, which is not published. The attempts include a launch
without `lean` on PATH, a NanoDa stack overflow under the 8 MB default stack,
and a memory-floor stop.

**Reproduction from this checkout** (requires the pinned Lean/Mathlib dependency
objects in `lean/.lake`; `OUT` must be a fresh writable directory):

```bash
OUT=/path/to/fresh-output
LEAN="$(cd lean && elan which lean)" LAKE_DIR="$PWD/lean/.lake" \
  bash hunts/rh_height_lean/lean/build.sh --full100 "$OUT" > "$OUT.build.log" 2>&1
.venv/bin/python hunts/rh_height_lean/lean/check_axioms.py "$OUT.build.log" --full100
.venv/bin/python hunts/rh_height_lean/gen_boxes100.py --check
.venv/bin/python hunts/rh_height_lean/gen_legs100.py --check
.venv/bin/python -m pytest -q hunts/rh_height_lean
```

The `--full100` build includes the old height-50 closure and the height-100
modules; `--full` alone stops at height 50. The unpublished durable local
bundle at `<bundle>` preserves all
568 scratch evidence files, a 545-file local source snapshot taken before these
documentation edits, and relative SHA-256 manifests with byte counts. Copied
files were rehashed against the originals; all 102 object receipt hashes,
32 height-100 source receipt hashes, eight independent identity receipt hashes,
and the exported closure hash were verified. `README.md` and `metadata.json`
in that bundle give the verification procedure, pinned toolchain and dependency
revisions, and the original checkout status. Original receipts retain scratch
paths; use the relative manifests to verify relocated files. The later
`evidence/gate3h-20261024/` is appended outside those earlier manifests; verify
its receipt's input hashes and terminal log verdict separately. No dependency
objects or toolchain binaries are bundled.

## What this does not say

Nothing above height 100 and nothing about the Riemann hypothesis (`docs/08`).
The earlier height-50 result could not distinguish `zeta` from the
Davenport-Heilbronn function below that function's first off-line zero at
height 85.699; the height-100 statement is above that counterexample ordinate,
but remains finite. RH has been verified numerically far higher (Platt and
Trudgian, 2021, to 3.0e12). The distinction here is formal kernel checking,
not the numerical range. The proof uses vendored `zeta-23-lean` analytic
infrastructure and the earlier Hardy-zero hunts; no priority claim follows.

**Novelty search, 2026-10-22.** Seven web searches (Lean, Mathlib and its Zulip, Isabelle and
the Archive of Formal Proofs, Coq, HOL Light, PrimeNumberTheoremAnd, arXiv on formalized
Turing-method verification), a read of the vendored `zeta-23-lean` sources, and a second pass
the same day: GitHub code search for Lean files on `riemannZeta` zeros (six queries, including
the identifier `RHUpToHeight`), the Archive of Formal Proofs analysis index, and Mathlib's
`HardyZ.lean`. The closest prior work, and how it differs:

- `gersh/ternary-goldbach-lean` (G. Bialer, 2026), a Lean formalization of ternary Goldbach,
  states RH to height `T` in Lean and reduces it to sign-change scans plus a Turing-method
  count (`RHToHeightPincer.lean`, `XiScanRoute.lean`). Its RH to `3 * 10^12` enters as the
  axiom `finite_check_platt_trudgian_rh_zeta_3e12`, and its zero enumeration through height
  20,000 is a named trust atom computed outside Lean's kernel; its "no zero with
  `|Im s| <= 4`" is derived from that atom. So it has a formal statement of RH to a height,
  but every instance rests on an outside computation taken as an axiom. The theorem here
  uses only Lean's three standard axioms.
- `TristenHarr/thegoldenalgebra`: Lean files bracketing 182 sign changes of Hardy's Z,
  from supplied data. Like hunts #132 and #133 this gives zeros on the line, a lower bound,
  and no upper count.
- `anthropics/zeta-23-lean` (arXiv 2608.13637) and `AxiomMath/ZetaZeros`: proportion
  theorems (about 2/3 of zeros simple and on the line). This hunt vendors zeta-23-lean's
  folded argument principle and Stirling bound. Neither locates an individual zero.
- Formal zero-free regions: the 7/8 half-plane in Lean (OpenAI's quasi-RH and the
  `tomoto0/quasi-riemann-hypothesis-7-8-verification` replay) and the Isabelle AFP
  `PNT_with_Remainder` region near `Re s = 1`. Neither touches the critical strip at finite
  height. The AFP's root-counting entries (W. Li) treat polynomials, not zeta.
- Several self-published "Lean proofs of RH" on Zenodo and GitHub. Those we read assume the
  analytic content as hypotheses.

What the search did not find: a proof of RH to any positive height, or of a complete zero
count to a height, that uses only Lean's (or another prover's) standard axioms. A web search
does not cover unpublished or non-indexed work, and OEIS and zbMATH were not consulted. So
this is a search record, not a novelty claim.

## Open

- Independent `con-ron --verified` replay is complete. Earlier NanoDa and
  bounded checker attempts remain inconclusive; no NanoDa verdict is claimed.
- 2026-10-26: `leanchecker --fresh` completed with exit 0 when rerun without a
  wall bound (see "Reruns without a wall bound"). NanoDa still has no verdict;
  it needs more free memory than the swarm box can give it.
- The local proof and checker-attempt evidence is preserved at
  `<bundle>`, but has not been
  published. Publication remains an owner decision.
