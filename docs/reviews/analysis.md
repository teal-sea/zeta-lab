A. CURRENT-HEAD FACTS
1. In `ontology/schema.py`, to even exist, a candidate must have: a `kind` (one of five decision procedures), a `claim` (the hashed, identity-bearing assertion), an `evidence` mapping, a `Provenance` record (to ensure reproducibility), and a `Verdict`. Optional typed `related_to` graph links are also permitted.
2. In `ontology/README.md` (section 7, bullet 5), the explicit blind spot is that the schema cannot express "Anything about the reason a claim might be true." It cannot represent mechanisms, proof sketches, or heuristics; `proof_gap` is just human-written prose.
3. In `ROADMAP.md`, the exact policy is that representing ontology proposals inside the discovery funnel is deliberately **not** being attempted. Because the schema has no representation of mechanism, forcing proposals in would make the schema "pretend". Ontology work stays in `docs/` and is judged directly against the gates in `docs/09`.
4. In `harness/README.md`, the admission rule is: **"No department without a battery."** A department must have a battery that satisfies structural checks, a door (documentation), and reference claims with known verdicts (at least one it kills and one it passes) to prove it is calibrated.
5. The four instrument roles in a `Battery` are: **Rival**, **Decoy**, **Surrogate**, and **Lesion**.

B. ADVERSARIAL MATCH
6. The lab already implements these primitives in:
   - `ontology/schema.py`: Implements "Claims" via the `Candidate` object (strictly splitting `claim` from `evidence`) and "Artifacts" via `Provenance` and `Verdict`.
   - `dossier/schema.py` (and `docs/19-research-dossiers.md`): Specifically designed as an "experiment in AI-native mathematical state", implementing claims as semantic obligations and axes of verification.
7. Yes, the lab already has this. It is implemented in `harness/protocol.py` (which defines the `Battery` and its four roles).
8. Yes, they are structurally the exact same rule. The consultant's rule that "agents may not promote their own proposals" is already enforced by the funnel's rule that it "will not promote anything to `survives` on its own authority." Promotion requires passing independent tests (`known`/`trivial`/`refutation`) at a strictly higher verification effort than the generation step. The system cannot self-certify.
9. The consultant's claim is false. The repository uses `validate_battery` (in `harness/protocol.py`) and `tests/test_department_conformance.py` as strict admission control. If an agent tries to add a department without a battery, or a battery missing any of the four roles, `validate_battery` will raise an exception and the conformance test suite will structurally fail the build.
10. No. Under the lab's "honest-scope" rule, passing or fixing a planted failure (a lesion) merely proves that the agent can satisfy the software engineering and validation constraints of the referee. It produces no evidence for the mathematics itself. Equating the passing of a software benchmark with doing mathematical research violates the core premise of the laboratory.

C. ACTIONABLE DECISION
11. The consultant's proposal **does not** require pivoting zeta-lab. The requested "intervention ledger" (already existing as `conjectures/ledger.jsonl` and `ledger.runs.jsonl`) and "agent admission control" (the `Department`/`Battery` conformance suite) are already structurally present and strictly enforced. They are simply documented as scientific refereeing tools rather than AI-agent features.
12. **Recommendation: Reject the consultant's proposal to build new primitives.** 
    The requested architecture already exists in the repository, but with much stricter epistemic controls (e.g., hash-based deduplication of claims vs. evidence, and forced lesion tests) than the consultant is proposing.
    - **Path forward:** Do not rewrite `harness/` or `ontology/` to adopt the consultant's vocabulary. Instruct the consultant that if they want to run their "Lab Rotation Benchmark", they must do so by writing new `Department` modules that plug directly into the existing `harness/protocol.py` battery interface.
    - **Explicit Kill Conditions:** Reject any pull request that attempts to bypass `validate_battery`, attempts to remove the Rival/Decoy/Surrogate/Lesion requirement, or attempts to flatten the strict `claim` vs `evidence` schema into an unstructured "Artifact".
