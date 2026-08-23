# The Palomar submission surface

[Palomar](https://palomar-registry.org/) is a registry of Lean-verified
mathematics, incubated by the Lean FRO and ICARM and opened for submissions on
2026-08-18. It is the analogue of a preprint server for Lean proofs: it records
a claim from a fixed commit of a public repository, replays the proof through
Lean's kernel *and* the independent NanoDa kernel, applies an editorial floor
for research interest, and publishes the exact statement together with the
review's findings.

**Three** submission surfaces live here. Two of them, Pub 1 and
Davenport-Heilbronn, have passed review and requested registration; the
Davenport-Heilbronn one took two attempts, and the bottom of this file says
why. The third, the bridge, is **authored and prechecked but not submitted**.

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
| `bridge/comparator.json` | Bridge | Which declarations are compared, and under which axioms. |
| `bridge/formalization.yaml` | Bridge | Provenance, scope, automation and review metadata. |
| `PALOMAR.md` | all three | This file. |

The three surfaces carry **eight** deliberate `sorry`s between them, three in
`Challenge.lean`, one in `DHChallenge.lean` and four in `BridgeChallenge.lean`,
one per advertised statement.
Any claim about this tree being sorry-free has to say *which* object it means:
the developments and all three Solution modules are sorry-free, the Challenge
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
`BridgeChallenge.lean`. They are what the Palomar format requires of an
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
