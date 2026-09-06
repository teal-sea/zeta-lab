# Handoff: LeanEval Board First Prove Pass & Ostoyae Engine Upgrade

**Date:** 2026-09-03  
**Box:** `orca-agent-box` (user `thomaslincez`)  
**Status:** All work committed, pushed to GitHub across all repositories, and PRs merged. Safe to power off VM.

---

## 1. Summary of What Happened

During this session, Claude Code hit the session token limit immediately after completing the first real prove pass on the `lean-eval-board`.

Before the session cut off, user requested:
> *"Stop . were about to runout of tokens. need to commit push document merge to main to gh the whole shebang cause this session is about to close and ill turn off the vm machine off until the next session"*

Every piece of code, graph state, Lean proof, refutation, and documentation has been verified, committed, pushed to GitHub, and merged.

---

## 2. Ostoyae Engine Upgrade (PR #38 Merged to Main)

- **Repository:** `teal-sea/Ostoyae`
- **PR:** [#38](https://github.com/teal-sea/Ostoyae/pull/38), *Merged into `main`* (Commit: `23c716c`)
- **Key fixes delivered:**
  1. **Lean execution in cells:** Cell execution previously denied `lake` and `lean` commands in headless mode. `executors/claude.sh` now grants Lean cells permission to invoke `lake`, `lean`, and `OSTOYAE_LEAN_MCP` without requiring interactive prompts.
  2. **Read-only Mathlib cache:** Added `--add-dir` for deduplicated read access to shared Mathlib while strictly denying file-modification tools on linked paths.
  3. **Lean Language Server integration:** Enabled `OSTOYAE_LEAN_MCP=~/.lean-mcp-venv/bin/lean-lsp-mcp` for proof state inspection and premise search.
  4. **Scout tools:**
     - `bin/ask-web`: Perplexity cited queries (~$0.005/call).
     - `bin/ask-aristotle`: Submits to Harmonic Aristotle at its pinned toolchain (Lean v4.28.0), returning proof terms to be ported and re-elaborated at our rev (v4.33.0).
  5. **`confirm-scoped` safety:** Fixed `--dry-run` flag handling so dry runs do not modify graph state.
  6. **Rehearsal suite:** `bin/rehearse-judge` 33 of 33 tests passing.

---

## 3. LeanEval Board Results (`graphs/lean-eval-unsolved.json`)

- **Repository:** `teal-sea/lean-eval-board`
- **Branch:** `main` (Pushed commit `869ebf6`)
- **Total attempts recorded:** 46 attempts (a-0001 through a-0046).

### A. Successfully Proved Definitions (Merged into `trunk`):
Eight definitions were proved sorry-free against pinned Mathlib and merged into the pursuit `trunk`:
1. `a-0036`: `Group.LocallyIndicable`
2. `a-0037`: `ErdosFaberLovaszConjecture.Hypergraph.degree`
3. `a-0038`: `MonoidAlgebra.augmentation`
4. `a-0039`: `ErdosFaberLovaszConjecture.Hypergraph.maxDegree`
5. `a-0040`: `MonoidAlgebra.augmentationIdeal`
6. `a-0041`: `Group.CohomologicalDimensionLE`
7. `a-0043`: `ErdosFaberLovaszConjecture.Hypergraph.IsLinear`
8. `a-0044`: `Group.IsFPOver`

### B. Machine-Checked Refutations:
Instead of hallucinating proofs for ill-posed statements, the prove cells produced formal Lean 4 refutations:
1. **`a-0042` & `a-0046` (`Group.LocallyIndicable.exists_divisionRing_embedding`):**
   - **Finding:** The mapper had a universe slip: `{G : Type*}` and `(K : Type*)` with `∃ (D : Type)`. Forcing an injection into `Type 0` forces `Small.{0} (MonoidAlgebra K G)`.
   - **Refutation:** Proved `not_proposed : ¬ Proposed.{0, 1}` sorry-free using `G = PUnit` and `K = FractionRing (MvPolynomial Type ℚ) : Type 1`. Kernel reported only `[propext, Classical.choice, Quot.sound]`.
2. **`a-0045` (`BoseGases.exists_unique_isScatteringSolution`):**
   - Statement false as written in benchmark notes; formally refuted against definitions.

---

## 4. GitHub Remote Sync Status

All repositories are fully in sync with GitHub remotes:

| Repository | Local Path | Branch | GitHub Remote Status |
|---|---|---|---|
| **Ostoyae** | `~/ostoyae/Ostoyae` | `main` | Synced to `origin/main` (`23c716c`), PR #38 merged |
| **lean-eval-board** | `~/lean-eval-board` | `main` | Committed & pushed to `origin/main` (`869ebf6`) |
| **lean-eval** | `~/lean-eval` | `trunk`, `board` | Pushed to `teal-sea/lean-eval` (`main`, `board`, and refutations) |
| **erdos-frontier** | `~/erdos-frontier` | `main` | Committed & pushed to `origin/main` (`80ed4ac`) |
| **zeta-lab** | `~/zeta-lab-houndshark` | `handoff-lean-eval-board` | Committed & pushed to `origin/handoff-lean-eval-board` |

---

## 5. VM Resumption Runbook (Next Session)

When the VM is powered back on:

```bash
# 1. Check Ostoyae and Board status
cd ~/ostoyae/Ostoyae && git status
cd ~/lean-eval-board && git status

# 2. Source environment credentials (if running paid tools)
set -a; . ~/.config/ostoyae/env; set +a

# 3. Launch graph viewer (if desired)
cd ~/ostoyae/Ostoyae
node viewer/serve.mjs ~/lean-eval-board/graphs/lean-eval-unsolved.json --port 4300

# 4. Next board launch (remember: --usd N is CUMULATIVE over the board!)
# Check current spend first:
python3 -c "from pathlib import Path; import json; g=json.load(open(Path.home() / 'lean-eval-board/graphs/lean-eval-unsolved.json')); print('Total spend so far: $', sum(a.get('usage',{}).get('cost_usd',0) for a in g.get('attempts',[])))"
```
