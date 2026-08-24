# The Palomar submission surface

[Palomar](https://palomar-registry.org/) is a registry of Lean-verified
mathematics, incubated by the Lean FRO and ICARM and opened for submissions on
2026-08-18. It is the analogue of a preprint server for Lean proofs: it records
a claim from a fixed commit of a public repository, replays the proof through
Lean's kernel *and* the independent NanoDa kernel, applies an editorial floor
for research interest, and publishes the exact statement together with the
review's findings.

**Four** submission surfaces live here. Two of them, Pub 1 and
Davenport-Heilbronn, have passed review and requested registration; the
Davenport-Heilbronn one took two attempts, and the middle of this file says
why. The third, the bridge, is submitted and awaiting an outcome. The fourth,
**V2 of the bridge entry**, carries the unconditional three-point theorem and is
authored and prechecked but not submitted; the bottom of this file is its record.

| File | Surface | Role |
| --- | --- | --- |
| `Challenge.lean` | Pub 1 | The advertised statements. Imports Mathlib alone. |
| `Solution.lean` | Pub 1 | The same statements, proved from `ZetaLean.Pub1`. |
| `comparator.json` | Pub 1 | Which declarations are compared, and under which axioms. |
| `formalization.yaml` | Pub 1 | Provenance, scope, automation and review metadata. |
| `DHChallenge.lean` | DH | The advertised statement. Imports Mathlib alone. |
| `DHSolution.lean` | DH | The same statement, proved from `ZetaLean.DHAnalytic`. |
| `comparator-dh.json` | DH | Which declaration is compared, and under which axioms. |
| `palomar-dh/formalization.yaml` | DH | Provenance, scope, automation and review metadata. |
| `bridge/BridgeChallenge.lean` | Bridge | The advertised statements. Imports Mathlib alone. |
| `bridge/BridgeSolution.lean` | Bridge | The same statements, proved from `Zeta23Ext.Bridge.Main`. |
| `bridge/comparator.json` | Bridge V1 | Which declarations are compared, and under which axioms. |
| `bridge/formalization.yaml` | Bridge V1 | Provenance, scope, automation and review metadata. |
| `bridge/V2Challenge.lean` | Bridge V2 | The advertised statements. Imports Mathlib alone. |
| `bridge/V2Solution.lean` | Bridge V2 | The same statements, proved from `Zeta23Ext.Bridge.Main` and `ThreePoint.Main`. |
| `bridge/comparator-v2.json` | Bridge V2 | Which declarations are compared, and under which axioms. |
| `bridge/formalization-v2.yaml` | Bridge V2 | Provenance, scope, automation and review metadata. |
| `PALOMAR.md` | all of them | This file. |

The surfaces carry **thirteen** deliberate `sorry`s between them, three in
`Challenge.lean`, one in `DHChallenge.lean`, four in `BridgeChallenge.lean` and
five in `V2Challenge.lean`, one per advertised statement.
Any claim about this tree being sorry-free has to say *which* object it means:
the developments and every Solution module are sorry-free, the Challenge
modules are not, and a submission whose metadata blurs the two gets that pointed
out. One did.

**The bridge surface is a separate Lake project, and has to be.** Pub 1 and DH
are built by the `lean/` package, whose only dependency is Mathlib. The bridge
theorem depends on `anthropics/zeta-23-lean`, which `lean/` does not require, so
its surface lives in a package of its own at `lean/bridge/` — the **selected
project** for that submission, in the sense of CONTRIBUTING.md section 6.1. Its
metadata and Comparator files stay beside the other two entries', because that is
where a reader looks for them; the submission form takes both paths explicitly.

## The Challenge modules contain deliberate `sorry`s. Do not "fix" them.

Three in `Challenge.lean`, one in `DHChallenge.lean`, four in
`BridgeChallenge.lean`, five in `V2Challenge.lean`. They are what the Palomar format requires of an
advertised statement: the Challenge module is the small, trusted surface a
mathematical reader audits, and it states each claim without proving it. The
matching Solution module proves the same statements, and Comparator checks that
the two match. The repository rule that the Lean arm counts nothing with a
`sorry` is untouched: every proof development is sorry-free, and every Solution
module builds with no `sorry` warning.

## Why the definitions are duplicated

`Challenge.lean` may import only Lean core, Mathlib and Tau Ceti, so it cannot
import `ZetaLean`. It therefore restates the definitions the statements need,
verbatim, in a fresh `ZetaLean.Palomar` namespace. `Solution.lean` does **not**
import `Challenge`: under the Palomar layout the two modules independently
declare the same names, and importing one into the other would collide. Its
definition block is byte-identical to the one in `Challenge.lean`, and the
bridge lemmas to `ZetaLean.Pub1` are all `rfl`, except that `SourceWindow` is a
structure and therefore two distinct inductive types, so `sourceAdmissible_eq`
transports its ten fields in both directions.

If you edit a definition in `ZetaLean/Pub1/Setting.lean`, `Window.lean`,
`Main.lean` or `Aristotle/E1.lean` that an advertised statement mentions, the
`rfl` bridges in `Solution.lean` will break. That is the intended alarm: the
registry entry pins a commit, and the statements it advertises must keep
matching the development.

## What is submitted

The three declarations the companion note names in its formal-verification
section, mirrored into `ZetaLean.Palomar`:

- `pub1_strong_closure`: the supremum orientation,
  `sup ⟨1,v⟩²/⟨Av,v⟩ = c*` over the compactly supported monotone admissible
  class.
- `pub1_strong_closure_reciprocal`: the matching infimum, `1/c*`.
- `pub1_strong_closure_exists`: the same identity with the profile and both
  uniform constants existentially quantified, so it carries no hypothesis and
  cannot be vacuous.

These are statements about a Fredholm operator on `[-1/2, 1/2]` and about a
class of test profiles. They say nothing about the zeros of ζ and nothing about
the Riemann Hypothesis, and `formalization.yaml` says so in `status.scope`.

## Relation to the companion note

The informal note pins this repository at tag `xi-prime-ceiling-support-v1`,
commit `197cee922270a3ceba7c21de0a21dd816a29adad`. Between that commit and this
one the only file changed under `lean/` is `ZetaLean/HardyRamanujantheorem.lean`,
which is in the import closure of no advertised declaration. The mathematics
being advertised is therefore the same tree the note describes.

## Re-verifying before a resubmission

```bash
cd lean && PATH="$HOME/.elan/bin:$PATH" lake build Challenge Solution
# expect: three `sorry` warnings from Challenge.lean, none from Solution.lean
cat > /tmp/Ax.lean <<'EOF'
import Solution
#print axioms ZetaLean.Palomar.pub1_strong_closure
#print axioms ZetaLean.Palomar.pub1_strong_closure_reciprocal
#print axioms ZetaLean.Palomar.pub1_strong_closure_exists
EOF
PATH="$HOME/.elan/bin:$PATH" lake env lean /tmp/Ax.lean
# expect each: [propext, Classical.choice, Quot.sound]
```

Both were run on 2026-08-21 against Mathlib `v4.33.0-rc2` and passed.

## The Davenport-Heilbronn surface, and why it advertises one declaration

Submitted 2026-08-21 as `m135pipw9ldb` at commit `e474535` advertising three
declarations, it cleared the mechanical gate clean and was then refused by the
editorial review. Two findings, both recorded in full in
`docs/32-the-palomar-arm.md` §8:

1. `review.notes` claimed "the tree is sorry-free", which the Challenge modules
   make false. The table above now states the split explicitly.
2. The two minimum-modulus criteria were a **separate selected result group**,
   and an elementary consequence of the maximum-modulus principle does not
   clear the notability floor on its own account. Usefulness to a later
   certified search is not research interest.

So the surface now advertises `ZetaLean.PalomarDH.dh_analytic_half` alone.
`ZetaLean.DH.exists_zero_of_norm_lt_on_sphere` and
`..._on_frontier` remain in the development, where `DHZeroCriterion.lean` uses
them; they are simply no longer offered to an editor to score. **Do not add
them back to `DHChallenge.lean` without a reason that answers finding 2.**

Palomar does not re-review a refused submission, and permits one submission in
progress per repository, so `m135pipw9ldb` was abandoned and the corrected
commit `097215a` went in as a new one. That one returned **no problems were
identified** and registration was requested on 2026-08-21. A submission's review
is private and reachable only through its own access link, which is a
credential: it does not belong in this repository.

```bash
cd lean && PATH="$HOME/.elan/bin:$PATH" lake build DHChallenge DHSolution
# expect: one `sorry` warning from DHChallenge.lean, none from DHSolution.lean
.venv/bin/python scripts/palomar_precheck.py . lean \
  lean/comparator-dh.json lean/palomar-dh/formalization.yaml
```

## The bridge surface: authored 2026-08-23, prechecked, not submitted

The third entry advertises Ainta's seven-point simple-zero bound as a theorem
about Mathlib's `riemannZeta`, **conditional on the seven-point inequality**,
which is a named hypothesis of every advertised statement and is not a Lean
fact. The development is Hunt #79 (`hunts/ainta_seven_point/BRIDGE.md`).

Four declarations are advertised, all in `Zeta23Ext.Palomar`:

- `seven_point_bound`: the parametric theorem. For `c > 0`, `m ≥ 7`, `p > 0`
  with `c(m−6) ≤ 1`, and `hCert : ∀ g ≥ 0, c ≤ F6 p g`, for every `ε > 0` and
  all large `T`, `(Φ(c,m,p) − ε)·N(T,2T) ≤ N₀ˢ(T,2T)` with
  `Φ(c,m,p) = (H − 6(m−1)/(pm))/(1 − c(m−6)/m)`.
- `seven_point_bound_paper`: at Ainta's `(19/5000, 269, 3000)`, constant
  `(1345000 H − 2680)/1340003 = 0.6730085279277797…`.
- `seven_point_bound_lab`: at this laboratory's own `(34697/10⁷, 294, 3400)`,
  constant `(520625000 H − 915625)/518855453 = 0.6730295534796928…`.
- `seven_point_bound_lab_ratio`: the same conclusion as a bound on the ratio
  `N₀ˢ(T,2T)/N(T,2T)`, with no positivity guard on the denominator.

**What is not advertised, deliberately.** The eight-point statement of
`hunts/ainta_seven_point/RESULTS.md`: its interval-arithmetic run is done, but
the bridge from that certificate to a proportion is *stated, not proved*, and an
unproved bridge has no business on a registry surface. Nothing about the
Riemann Hypothesis, and no numerical value of `H` beyond its closed form.

**`H` is written out in the Challenge.** The Challenge may import only Mathlib,
so it cannot reach the dependency's `HD 1 = 2 − 1/c₁*`. It declares
`H = 3/2 − (1/√2)cot(1/√2)` instead, which is what the dependency's `HD_one`
proves that equals. `BridgeSolution.lean`'s `H_eq` is exactly `HD_one`, and is
the one bridge in that file which is not `rfl`.

**Licence.** The bridge development carried Apache-2.0 headers copied from the
dependency's house style until 2026-08-23; they are MIT now, matching the
repository. `lean/bridge/Zeta23Ext/Bridge/Helpers_S8.lean` is the one file that
adapts the dependency's proof bodies rather than importing them, and it keeps
its attribution to Anthropic, PBC and the Apache-2.0 licence of those bodies in
a notice, in its own header and in `lean/bridge/NOTICE`.

```bash
cd lean/bridge && PATH="$HOME/.elan/bin:$PATH" lake build
# or: bash lean/bridge/assemble.sh   (symlinks the prebuilt stores in first)
# expect: Build completed successfully (8860 jobs), and exactly four `sorry`
# warnings, all from BridgeChallenge.lean
.venv/bin/python scripts/palomar_precheck.py . lean/bridge \
  lean/bridge/comparator.json lean/bridge/formalization.yaml
# expect: 66 pass, 1 warn (the rc toolchain, standing), 0 FAIL
```

Run on 2026-08-23 and passed. **Not submitted.** Palomar permits one submission
in progress per repository, and whether a conditional refinement of a theorem
already registered from the upstream repository clears the notability floor is
the registry's call, not this file's.

## The bridge entry, submitted 2026-08-23

Submitted 2026-08-23T17:09:18Z at commit `58bd44cadb5881540af744a152492d2c25420008`,
project directory `lean/bridge`, comparator `lean/bridge/comparator.json`, advertising four
declarations: `seven_point_bound`, `seven_point_bound_paper`, `seven_point_bound_lab` and
`seven_point_bound_lab_ratio`. Derived origin `source-based`, relationship `adapts`: the
mathematics between the finite inequality and the zero count is Ainta's draft, and the
formalization, the closed form `Phi(c, m, p)` with its block-size cap, the sharp stability
form and the pinching proof are this laboratory's.

The certificate is a hypothesis, `hCert`, the way the upstream development takes `EnclOK`.
Nothing here bears on the Riemann Hypothesis, and `status.scope` says so.

Mechanical verification and the editorial review were queued at submission. **No outcome is
recorded here yet, and no identifier is guessed.** Registration is public and is the owner's
click alone; the private access link is not recorded in this repository.

## V2 of the bridge entry: the three-point theorem is unconditional

**Authored 2026-08-24. Prechecked, not submitted, no identifier guessed.** Registration and
submission are the owner's, and Palomar permits one submission in progress per repository.

V2 replaces V1's four seven-point statements with the parametric `n`-point theorem and two
instances of it, five declarations in the namespace `Zeta23Ext.PalomarV2`:

| Declaration | Hypothesis | Constant |
| --- | --- | --- |
| `n_point_bound` | `hCert` | `Φₙ(c,m,p) = (H − (n−1)(m−1)/(pm)) / (1 − c(m−(n−1))/m)` |
| `eight_point_bound` | `hCert` at `(41763/10⁷, 3200)` | `(2460000000·H − 5359375)/2450018643 = 0.67305298298962888…` |
| `eight_point_bound_ratio` | the same | the same, as `N₀ˢ/N` |
| `three_point_bound` | **none** | `(149000000·H − 99200)/148800133 = 0.67273733450380946…` |
| `three_point_bound_ratio` | **none** | the same, as `N₀ˢ/N` |

**The two three-point statements are the point of V2.** Their certificate,
`1345/10⁶ ≤ F 3 3000 g` at every pair of nonnegative gaps, is not assumed: it is
`Zeta23Ext.Bridge.ThreePoint.three_point_cert`, proved in Lean from a twelve-term Taylor
enclosure of `cos` and `sin`, the closed form of `K`, and 368 interval cell lemmas applied
1515 times over 487 leaves. `Φ₃` exceeds the unconditional `H = 0.67250070367941164…` of the
pinned dependency by `2.3663·10⁻⁴`, so for Mathlib's `riemannZeta` this is an **unconditional
improvement of that development's Theorem D**, under the same three axioms and no hypothesis.

The eight-point pair stays conditional and is advertised beside it deliberately: the gap
between `0.67305298…` and `0.67273733…` is exactly what is still owed to an
interval-arithmetic verifier.

### Layout: `ThreePoint` is a `lean_lib` of `lean/bridge`, not a package of its own

The three-point development was a Lake package at `hunts/ainta_seven_point/lean-three-point/`
requiring `lean/bridge` **by path** (`../../../lean/bridge`). As the selected project that
would have been a gamble: **whether Palomar's replay resolves a `path` dependency pointing
outside the selected project directory is not something this repository can determine**, and
the published policy does not say. `lake build` in a fresh clone resolves it, which is
evidence about Lake and none about the registry's harness.

So the modules moved into `lean/bridge` as a second `lean_lib`, and the project directory is
`lean/bridge` — the same directory the V1 entry already replays, whose only dependency is
`anthropics/zeta-23-lean` at a pinned 40-character SHA. The move changes `lake-manifest.json`
not at all. What it costs: `lake build` at that root now also builds the 20 000 lines of
generated cell tables, so a replay of *any* entry from this project pays for them. That is
the trade taken, and it is the cheap side.

Two things were preserved through the move. `autoImplicit` and `relaxedAutoImplicit` are off
for the `ThreePoint` library alone, through `leanOptions` on its `lean_lib` — the old package
set them package-wide, and the reason is in that lakefile: with them on, an unresolved name in
a theorem *statement* is silently bound as an implicit variable, which for material whose
whole claim is that a named constant is unconditional is a failure mode that has to be
impossible rather than unlikely. And `BridgeChallenge.lean`, `BridgeSolution.lean`,
`comparator.json` and `formalization.yaml` are **byte-identical**: V1 is live at commit
`58bd44ca` and nothing about it moved.

### What was renamed, and why the file names are not `Three*`

The staged eight-point surface (`EightChallenge.lean`, `EightSolution.lean`,
`comparator-eight.json`, `formalization-eight.yaml`) became `V2Challenge.lean`,
`V2Solution.lean`, `comparator-v2.json`, `formalization-v2.yaml`, and its namespace
`Zeta23Ext.PalomarEight` became `Zeta23Ext.PalomarV2`. That is forced by the format:
`comparator.json` names **one** `challenge_module` and **one** `solution_module`, so a single
comparator advertising both the eight-point and the three-point statements requires them in
one Challenge module and one Solution module. Keeping "Eight" in the names of a module that
also advertises the three-point bound would have been the misleading option.

### Origin: `source-based`, not `original`

`scripts/palomar_precheck.py` reimplements the derivation from `sources`: `original` requires
a source of type `original-proof` whose relationship is `other`, **and** every source's
relationship in `{background, other}`; `source-based` is any source related as `formalizes`,
`adapts` or `independently-proves`. The Ainta paper is related as `adapts` — the argument from
the finite inequality to the zero count is his, and the generalisation in `n`, the Lean, the
certificates and the enclosure are this laboratory's. Under those rules that derives
**`source-based`**, and the precheck confirms it. The dependency is cited under
`related_formalizations` as `builds-on`, exactly as V1 does. Asserting `original` here would
require declaring the Ainta paper mere `background`, which would be false.

### Kept small on purpose

V1's `formalization.yaml` is 23.9 KB and the staged eight-point one was 29.1 KB; V2's is
**13.0 KB**, and `V2Challenge.lean` is 276 lines / 12.7 KB, inside the mechanical warning
threshold of 300 lines / 32 KiB. The live entry's editorial review has crashed four times and
input size is the best hypothesis available for it, so the write-up, the module documentation
and the metadata were all cut rather than extended. **This reasoning appears here and nowhere
in the submitted files.**

```bash
cd lean/bridge && PATH="$HOME/.elan/bin:$PATH" lake build
# expect: exactly five `sorry` warnings, all from V2Challenge.lean
.venv/bin/python scripts/palomar_precheck.py . lean/bridge \
  lean/bridge/comparator-v2.json lean/bridge/formalization-v2.yaml
# expect: 63 pass, 1 warn (the rc toolchain, standing), 0 FAIL
```

The local `lake build` is not runnable on the author's machine; `.github/workflows/three-point.yml`
is the build loop and runs the same three checks — the eleven-declaration axiom audit, the
sorry accounting, and the precheck.
