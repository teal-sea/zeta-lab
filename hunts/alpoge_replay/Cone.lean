/-
How much of an environment do given theorems depend on?

A small program. It loads the `.olean` files of one module and everything it
imports, walks the constants reachable from a list of root declarations (the
same walk `#print axioms` makes in `Lean.CollectAxioms`), and counts what it
meets by the module each constant was defined in.

  cone <module> <root,root,...> <prefix,prefix,...> <out.json> [dir for module lists]

The prefixes are the root components of the module names that count as "the
archive"; everything else (Mathlib, Lean, Std, Batteries) is its libraries.
The output says how many of the archive's modules and declarations lie in
the cone of the first root alone and of all the roots together, and how many
do not.

A constant is in the cone if a root mentions it in its type or value, or a
constant in the cone does. Constructors come with their inductive type, as in
`CollectAxioms`. Nothing here checks a proof or runs any code of the modules
it loads; it reads which names a term mentions. Compiled, not interpreted: an
environment of several million declarations is too slow to walk under `#eval`.

It also answers, from the stored terms alone, the two questions that
`#print axioms` and a reading of the source answer through the elaborator of
the environment they run in, which modules of the archive are free to extend:

  axioms            every axiom in the cone, the list `#print axioms` prints
  roots_as_stored   for each root its kind, its statement as a term, and,
                    where the statement is one constant, the module that
                    defines that constant and the term it unfolds to

No command, notation or macro of the loaded modules takes part in either.
-/
module

import Lean

open Lean

namespace Cone

/-- Constants a declaration mentions directly. -/
def uses (ci : ConstantInfo) : Array Name := Id.run do
  let mut out := ci.type.getUsedConstants
  if let some v := ci.value? (allowOpaque := true) then
    out := out ++ v.getUsedConstants
  if let .inductInfo v := ci then
    out := out ++ v.ctors.toArray
  return out

/-- Every constant reachable from `roots`; names the environment lacks come back apart. -/
def closure (env : Environment) (roots : Array Name) : Std.HashSet Name × Array Name := Id.run do
  let mut seen : Std.HashSet Name := {}
  let mut missing : Array Name := #[]
  let mut stack := roots
  while !stack.isEmpty do
    let c := stack.back!
    stack := stack.pop
    if seen.contains c then continue
    seen := seen.insert c
    match env.find? c with
    | none => missing := missing.push c
    | some ci =>
      for d in uses ci do
        unless seen.contains d do stack := stack.push d
  return (seen, missing)

/-- `names` is `env.header.moduleNames`, taken once by the caller: in this
version of Lean that projection rebuilds the array on every call, which made a
walk over Mathlib's 569,189 declarations take five minutes instead of
seconds. -/
def moduleOf (names : Array Name) (env : Environment) (c : Name) : Name :=
  match env.getModuleIdxFor? c with
  | some i => names[i.toNat]!
  | none => `_no_module_

def isArchive (prefixes : Array Name) (m : Name) : Bool :=
  prefixes.any fun p => p == m.getRoot

def splitNames (s : String) : Array Name :=
  (s.splitOn ",").toArray.filterMap fun x =>
    let x := x.trimAscii.toString
    if x.isEmpty then none else some x.toName

/-- The word `#print` would use for a constant. -/
def kindOf : ConstantInfo → String
  | .axiomInfo _ => "axiom"
  | .defnInfo _ => "def"
  | .thmInfo _ => "theorem"
  | .opaqueInfo _ => "opaque"
  | .quotInfo _ => "quot"
  | .inductInfo _ => "inductive"
  | .ctorInfo _ => "constructor"
  | .recInfo _ => "recursor"

/-- A root as the environment stores it. -/
def rootFacts (names : Array Name) (env : Environment) (c : Name) : Json :=
  match env.find? c with
  | none => Json.mkObj [("name", toJson c.toString), ("found", toJson false)]
  | some ci =>
    let base := [("name", toJson c.toString), ("found", toJson true), ("kind", toJson (kindOf ci)),
      ("defined_in", toJson (moduleOf names env c).toString), ("statement", toJson (toString ci.type))]
    match ci.type with
    | .const t _ =>
      let unfolded := match env.find? t with
        | some (.defnInfo d) => toString d.value
        | _ => ""
      Json.mkObj (base ++ [("statement_is_the_constant", toJson t.toString),
        ("statement_defined_in", toJson (moduleOf names env t).toString),
        ("statement_unfolds_to", toJson unfolded)])
    | _ => Json.mkObj base

structure Totals where
  modules : Nat
  decls : Nat
  thms : Nat

/-- Everything the archive defines, counted once. -/
def totals (names : Array Name) (env : Environment) (prefixes : Array Name) : Totals := Id.run do
  let mut modules := 0
  for m in names do
    if isArchive prefixes m then modules := modules + 1
  let mut decls := 0
  let mut thms := 0
  for (c, ci) in env.constants.map₁ do
    if isArchive prefixes (moduleOf names env c) then
      decls := decls + 1
      if ci matches .thmInfo _ then thms := thms + 1
  return { modules, decls, thms }

def report (names : Array Name) (env : Environment) (t : Totals) (label : String)
    (roots prefixes : Array Name) (modulesDir : Option String) : IO Json := do
  let (seen, missing) := closure env roots
  let mut coneDecls : Nat := 0
  let mut coneThms : Nat := 0
  let mut coneModules : Std.HashSet Name := {}
  let mut byRoot : Std.HashMap Name Nat := {}
  let mut axioms : Array String := #[]
  for c in seen do
    if let some (.axiomInfo _) := env.find? c then axioms := axioms.push c.toString
    let m := moduleOf names env c
    byRoot := byRoot.insert m.getRoot (byRoot.getD m.getRoot 0 + 1)
    if isArchive prefixes m then
      coneDecls := coneDecls + 1
      coneModules := coneModules.insert m
      if let some (.thmInfo _) := env.find? c then coneThms := coneThms + 1
  if let some dir := modulesDir then
    let names := coneModules.toArray.map (·.toString) |>.qsort (· < ·)
    IO.FS.writeFile (System.FilePath.mk dir / s!"cone-modules-{label}.txt")
      (String.intercalate "\n" names.toList ++ "\n")
  return Json.mkObj [
    ("label", toJson label),
    ("roots", toJson (roots.map (·.toString))),
    ("names_not_found", toJson (missing.map (·.toString))),
    ("axioms", toJson (axioms.qsort (· < ·))),
    ("roots_as_stored", Json.arr (roots.map (rootFacts names env))),
    ("constants_in_cone", toJson seen.size),
    ("constants_in_cone_by_library", Json.mkObj (byRoot.toList.map fun (k, v) => (k.toString, toJson v))),
    ("archive_modules", toJson t.modules),
    ("archive_modules_in_cone", toJson coneModules.size),
    ("archive_declarations", toJson t.decls),
    ("archive_declarations_in_cone", toJson coneDecls),
    ("archive_theorems", toJson t.thms),
    ("archive_theorems_in_cone", toJson coneThms)]

end Cone

open Cone in
public unsafe def main (args : List String) : IO UInt32 := do
  let (mod, rootsArg, prefixesArg, out, modulesDir) ←
    match args with
    | [m, r, p, o] => pure (m, r, p, o, none)
    | [m, r, p, o, d] => pure (m, r, p, o, some d)
    | _ => do
      IO.eprintln "usage: cone <module> <root,...> <prefix,...> <out.json> [dir for module lists]"
      return 2
  let roots := splitNames rootsArg
  let prefixes := splitNames prefixesArg
  if roots.isEmpty then
    IO.eprintln "no roots given"
    return 2
  initSearchPath (← findSysroot)
  Lean.withImportModules #[{ module := mod.toName }] {} fun env => do
    let names := env.header.moduleNames
    let t := totals names env prefixes
    let mut all : Array Json := #[]
    all := all.push (← report names env t "first-root" #[roots[0]!] prefixes modulesDir)
    if roots.size > 1 then
      all := all.push (← report names env t "all-roots" roots prefixes modulesDir)
    let j := Json.arr all
    IO.println j.pretty
    IO.FS.writeFile out (j.pretty ++ "\n")
    return 0
