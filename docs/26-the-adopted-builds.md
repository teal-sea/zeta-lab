# 26 — The adopted builds: the decision of 2026-08-11, made runnable

`ROADMAP.md` ("The outside memos, triaged") records the decision; this
document records what landed the same day, what each piece can and cannot
claim, and where each one's honest edge is. The pattern of `docs/20` and
`docs/21` applies: machinery is described together with the negative space
around it, because the blank spots are where the next failure comes from.

## 1. Verification independence, measurable (`harness/independence.py`)

The director run (`docs/25`) ended with a sentence that was true and
unusable: *a cross-check bounds only what is actually duplicated.* Unusable
because nothing carried the bound — which layers the two rigor backends
share lived in one HANDOFF paragraph, invisible to every audit.

`harness/independence.py` makes the bound a declared structure. A
`VerificationPath` is an ordered list of named layers from input to verdict;
`compare()` reports the **independence radius** (how deep the paths run
through the same leading layers), the **shared** layers (one implementation
run twice — faults there are invisible to agreement), the **reconvergent**
layers (shared *after* the divergence, the director-run shape), and the
**distinct** segments, which are the only thing an agreement between the two
paths is evidence about. There is no aggregate boolean; `bool(report)`
raises, the same refusal `dossier.status.Support` makes and for the same
reason.

The worked subject is the rigor cross-check itself, declared in
`harness/departments/zeta_department.py` from HANDOFF's enumeration: radius
3 of 5, one reconvergent layer (the S(T)/N(T) interval summation), and
exactly one layer implemented twice — the ball arithmetic. In sentences,
via `agreement_bounds()`: backend agreement is evidence about the ball
arithmetic and nothing else.

**The honest edge.** A declaration is not attestation (the same caveat as
`harness/provenance.py`): nothing checks a layer list is *complete*, and an
undeclared shared layer is exactly what the structure cannot see. One anchor
is pinned by test — the declaration names `zeta.rigor._exact`, and the test
fails if that attribute disappears — but one anchor is not a completeness
proof. The declaration is as good as its next audit.

## 2. The guard offensive's ledger (`harness/guards.py`)

Three of the director run's six defects were guards that could not do their
job. The offensive's question — *what exact incorrect computation is this
guard supposed to detect, and has that detection power actually been
demonstrated?* — now has a place where the answer accumulates.

A `GuardRecord`'s `fired` is tri-state: `None` is "nobody has demonstrated
anything" (the default state of every guard in this repository today), and
an outcome in either direction costs a named, runnable demonstration
artifact. A guard demonstrated *not* to fire stays in the ledger as a
finding. `offensive_worklist()` renders everything the ledger implies —
undemonstrated guards, dead guards, known misses — as disputable sentences.

The ledger opens with five records in
`harness/departments/guard_ledger.py`. Three are demonstrated live in
`tests/test_guard_ledger.py`, each by constructing the smallest mutant and
watching the guard's own logic fire on it, with a passing control alongside:

| guard | mutant | control |
| --- | --- | --- |
| the `_exact` repr-parse regression (docs/25 defect #1) | `Fraction(str(np.float32(...)))` differs from the binary value | the fixed parse equals it |
| doc-number uniqueness (the 2026-08-10 collision) | a docs tree with `05-a.md` and `05-b.md` | duplicate removed, guard silent |
| the reserved-word scan under `hunts/` | one overclaiming probe file | same file reworded, guard silent |

Two records are honestly `fired: None` — `tests/test_doors.py` and
`scripts/make_context.py --check` — the visible head of the worklist.

**The honest edge.** Five records is an opening, not coverage. The offensive
proper — sweeping *every* guard the tree relies on — is destroyer work that
runs one guard at a time, and the ledger's rule for it is fixed: `fired`
moves off `None` only in the change that adds the demonstration.

## 3. HuntSpec, on probation (`hunts/HUNTSPEC.md`)

New hunts carry a fenced contract block in `MISSION.md`: question, frontier,
dead routes, the non-model oracles allowed to assign truth, kill conditions,
and the agents' permitted and withheld actions. The parser and validator
live inside `tests/test_huntspec.py` — deliberately not a module — and the
spec page's own template is parsed by the test, so page and validator cannot
drift apart silently. One rule is enforced lexically: an oracle entry that
names a model is refused. Crude, stated as crude, and running.

**The honest edge.** The resumption benchmark (2026-08-09) is the standing
warning: typed machinery does not earn its keep by existing. HuntSpec is on
the dossier rule — it is promoted to a real module the first time a kill
condition fires mechanically or an oracle requirement blocks an ungrounded
status claim, and if a year passes without either, the right move is
removal, recorded. Existing hunts are not retrofitted; the two live hunts
run to their own kill conditions as written.

## 4. The proof-agent adapter (`lean/proof_adapter.py`)

External provers plug in as *generators*; the kernel — this machine's
`lake build` of the pinned ZetaLean toolchain — decides. Acceptance has two
legs, both local: a conservative static refusal scan (`sorry`, `admit`,
`axiom` declarations, `native_decide`; a match inside a comment still
refuses, because over-refusal is a gate's safe failure mode) and the kernel
check, whose "could not run" is `build_ok: None` — not decided, never a
pass. A rejected artifact never stays landed in the package; an existing
module is never overwritten. The published Aristotle case study (arXiv
2605.20120) supplied the lesson the tests pin: an artifact can compile while
its main theorem is one `sorry`, so the service's own verification claim is
input, not evidence.

Exercised end to end once: a trivial theorem, the real `lake build`, an
`accepted: True`, and the probe removed. The submission half
(`submit_to_aristotle`) waits on an API key and is the only part of the
adapter no test has run.

**The honest edge.** The adapter gates *soundness*, not *value*: a
kernel-checked trivial lemma passes it as cleanly as a kernel-checked deep
one. Which statements are worth a generator's hours is the operator's
question — the Mathlib-track Sturm lemmas are the standing first targets
(`ROADMAP.md`, the upstream track) — and the case-study economics (roughly
eight hours for a hard problem) say submissions batch overnight and stay at
the grain of local lemmas.

## 5. The alpha ecosystem, local (machine state, not repository state)

Recorded here because it exists and is invisible to git: `external/` in the
working checkout holds shallow clones of the surrounding ecosystem —
DeepMind's AlphaProof Nexus results (a Lean package: kernel-checkable here,
not taken on faith), `formal-conjectures` (open conjectures already stated
in Lean, `Millenium/RiemannHypothesis.lean` included), the AlphaEvolve
results and problems repositories, and two open evolutionary-search
implementations (OpenEvolve, CodeEvolve). A separate `.venv-tools`
interpreter carries `openevolve` and `aristotlelib`, kept out of the pinned
lab venv on purpose. The inventory and the remaining human steps (a Google
Cloud onboarding for the GA AlphaEvolve service; an Aristotle key) are in
`external/README.md`.

The rule that binds all of it is the phase charter's: these systems
generate; the lab's oracles decide. An evolutionary search runs only behind
a HuntSpec naming an exact non-model evaluator, and an external prover's
output goes through the adapter above or it does not count.

## What this document does not claim

Nothing here is a mathematical result, and none of it moved a bound. Four
instruments and an inventory landed in one day, on the strength of one
decision record; the first time any of them catches something real — a
declared shared layer that explains a false agreement, a guard demonstrated
dead before it lies, a kill condition that fires on a live hunt, a generated
lemma the kernel accepts into a rung — is when this document gets its first
follow-up section. Until then, the honest description of the whole build is:
the decision of 2026-08-11, made runnable.
