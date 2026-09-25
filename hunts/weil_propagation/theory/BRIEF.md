# Brief: theory worker

Read first: `hunts/weil_propagation/MISSION.md`, `AGENTS.md` (certainty
ladder, original vs novel), `ALIGNMENT.md`, then
`hunts/rogue_frontier/weil_trunc/RESULTS.md` and `THEOREM_FEASIBILITY.md`
(the Davenport-Heilbronn negativity at c = 31), and `docs/24`, `docs/35`.

## Question

Is there any known or constructible mechanism by which positivity of the
Weil form on window L, together with the Euler product, forces positivity on
window L + delta? What does the literature already know about how positivity
or the ground state changes with the window?

## Tasks, in order

1. Primary sources, read and cite with arXiv IDs and section numbers:
   Connes-Consani semilocal trace formula and "Weil positivity and trace
   formula, the archimedean place"; Connes-Consani-Moscovici (arXiv:2511.22755);
   Connes-van Suijlekom (arXiv:2511.23257); Connes (arXiv:2602.04022) s6;
   arXiv:2608.24827 (support-1.6 positivity and the doubly exponential decay
   law); Yoshida's original result. Summarize only what each proves about
   dependence on the window, the role of each prime entering, and where each
   program says it is stuck.
2. Write down the exact derivative or difference of the form in L: the
   archimedean change, the new prime-power atoms entering at n = e^L, and
   the effect on the admissible function space. Derive, don't recall;
   check any constant numerically with the lab's `zeta/weil.py` where cheap.
3. Propose at most three candidate propagation lemmas. For each: exact
   statement, what it would imply, where the Euler product enters, and the
   DH test (DH must violate the lemma's hypothesis or conclusion at the
   c = 30 -> 31 crossing, otherwise the lemma is refuted as stated).
4. For each candidate, give the smallest check the numerics worker could run,
   and say whether it is a restatement of RH with no new estimate.

## Output

Write only in `hunts/weil_propagation/theory/`: `RESULTS.md` with sources,
derivations, candidates and their status on the certainty ladder. Commit to
this branch in small commits. Do not push. No heavy computation; nothing over
a few minutes locally. No `lake build`.

Finish with a five-line summary at the top of RESULTS.md: strongest
candidate, what it would give, what refutes it, whether it is new or known
(state what was searched), next step.
