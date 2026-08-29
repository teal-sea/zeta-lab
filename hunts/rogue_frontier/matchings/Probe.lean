/-
Gap evidence for the perfect-matching count.
Compiled against the pin in lean/lake-manifest.json (mathlib 51e6992e,
toolchain v4.33.0-rc2).  Every claim below is resolved by the elaborator,
not by grep.
-/
import Mathlib

open Nat

section Present
-- Mathlib HAS the double factorial and its basic API.
#check @Nat.doubleFactorial
#check @Nat.doubleFactorial_two_mul
#check @Nat.factorial_eq_mul_doubleFactorial
#check @Nat.doubleFactorial_add_two
#check @Nat.doubleFactorial_add_one

-- Mathlib HAS perfect matchings as a predicate on subgraphs.
#check @SimpleGraph.Subgraph.IsPerfectMatching
#check @SimpleGraph.Subgraph.IsPerfectMatching.even_card

-- Involution / permutation infrastructure that does exist.
#check @Function.Involutive
#check @Equiv.Perm.card_support_eq_two
#check @Finset.card_eq_sum_card_fiberwise
#check @Finset.card_bij
#check @Finset.card_nbij'
end Present

section Absent
/-
The following names do NOT resolve at this pin.  Each is commented out
because an unresolved name is an elaboration error, which is precisely the
evidence wanted; uncommenting any one of them reproduces the error.

  #check @SimpleGraph.Subgraph.IsPerfectMatching.card_eq          -- no such decl
  #check @SimpleGraph.card_perfectMatchings                       -- no such decl
  #check Isserlis                                                 -- no such decl
  #check Wick                                                     -- no such decl
  #check @Nat.card_involutive                                     -- no such decl
  #check @Equiv.Perm.card_fixedPointFree_involutions              -- no such decl
-/
-- Instead of trusting the comment, probe the environment programmatically.
open Lean Elab Meta in
run_cmd do
  let names : List Name :=
    [`SimpleGraph.Subgraph.IsPerfectMatching.card_eq,
     `SimpleGraph.Subgraph.IsPerfectMatching.card,
     `SimpleGraph.card_perfectMatchings,
     `SimpleGraph.Subgraph.card_isPerfectMatching,
     `Isserlis, `isserlis, `Wick, `wick,
     `Nat.card_involutive,
     `Equiv.Perm.card_fixedPointFree_involutions,
     `Finset.card_pairings, `Finset.card_perfectMatchings,
     `Nat.card_perfectMatchings]
  let env ← getEnv
  for n in names do
    if env.contains n then
      logInfo m!"PRESENT: {n}"
    else
      logInfo m!"ABSENT:  {n}"

-- Enumerate every declaration whose name mentions PerfectMatching, so the
-- claim "the only cardinality result is even_card" is checked, not recalled.
open Lean Elab Meta in
run_cmd do
  let env ← getEnv
  let mut hits : Array Name := #[]
  for (n, _) in env.constants.toList do
    let s := n.toString
    if (s.splitOn "PerfectMatching").length > 1 && !n.isInternal then
      hits := hits.push n
  logInfo m!"declarations mentioning PerfectMatching: {hits.qsort (fun a b => a.toString < b.toString)}"

-- Same sweep for Isserlis / Wick / doubleFactorial.
open Lean Elab Meta in
run_cmd do
  let env ← getEnv
  let mut wick : Array Name := #[]
  let mut dfac : Array Name := #[]
  for (n, _) in env.constants.toList do
    let s := n.toString.toLower
    if !n.isInternal then
      if (s.splitOn "isserlis").length > 1 || (s.splitOn "wick").length > 1 then
        wick := wick.push n
      if (s.splitOn "doublefactorial").length > 1 then
        dfac := dfac.push n
  logInfo m!"Isserlis/Wick declarations: {wick.qsort (fun a b => a.toString < b.toString)}"
  logInfo m!"doubleFactorial declarations: {dfac.qsort (fun a b => a.toString < b.toString)}"
end Absent
