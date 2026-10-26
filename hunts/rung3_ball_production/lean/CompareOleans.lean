module

public import Lean

/-!
Hunt #145: are two builds of one module the same declarations?

`lean --run CompareOleans.lean A.olean B.olean` reads both modules' data (the `.olean`
and, where present, its `.server` and `.private` parts) and compares every part's
constants by name, kind, type and value (`Expr` structural equality), and their imports.
It prints `SAME` and exits 0 only if every part has the same names and every pair agrees.
Used to decide whether hunt #137's build of `ZetaLean.Rigor`, `IntervalExp` and
`IntervalCExp` may stand in for this checkout's in one `LEAN_PATH`, where byte
comparison of the oleans fails.
-/

open Lean

public def constKey (c : ConstantInfo) : String :=
  match c with
  | .axiomInfo _ => "axiom" | .defnInfo _ => "def" | .thmInfo _ => "thm"
  | .opaqueInfo _ => "opaque" | .quotInfo _ => "quot" | .inductInfo _ => "induct"
  | .ctorInfo _ => "ctor" | .recInfo _ => "rec"

/-- Compare one part's constants; returns the differences. -/
public def comparePart (tag : String) (ma mb : ModuleData) : Array String := Id.run do
  let mapB : Std.HashMap Name ConstantInfo :=
    mb.constants.foldl (fun m c => m.insert c.name c) {}
  let mut bad : Array String := #[]
  if ma.constants.size != mb.constants.size then
    bad := bad.push s!"{tag}: count {ma.constants.size} vs {mb.constants.size}"
  for c in ma.constants do
    match mapB.get? c.name with
    | none => bad := bad.push s!"{tag}: missing {c.name}"
    | some d =>
      if constKey c != constKey d || c.type != d.type || c.value? != d.value? then
        bad := bad.push s!"{tag}: differs {c.name}"
  if ma.imports.map (·.module) != mb.imports.map (·.module) then
    bad := bad.push s!"{tag}: imports differ"
  return bad

/-- The parts of a module-system olean, in the order `saveModuleDataParts` wrote them. -/
public def parts (base : String) : IO (Array (ModuleData × CompactedRegion)) := do
  let fs : Array System.FilePath := #[base, base ++ ".server", base ++ ".private"]
  let present ← fs.filterM (·.pathExists)
  readModuleDataParts present

public def main (args : List String) : IO UInt32 := do
  let [a, b] := args | IO.eprintln "usage: CompareOleans A.olean B.olean"; return 2
  let pa ← parts a
  let pb ← parts b
  let mut bad : Array String := #[]
  if pa.size != pb.size then bad := bad.push s!"parts {pa.size} vs {pb.size}"
  let tags := #["public", "server", "private"]
  let mut n := 0
  for i in [:min pa.size pb.size] do
    match pa[i]?, pb[i]? with
    | some (ma, _), some (mb, _) =>
      bad := bad ++ comparePart (tags.getD i "part") ma mb
      n := n + ma.constants.size
    | _, _ => bad := bad.push s!"part {i} unreadable"
  if bad.isEmpty then
    IO.println s!"SAME {pa.size} parts, {n} constants"
    return 0
  else
    for x in bad[:20] do IO.println x
    IO.println s!"DIFFERENT {bad.size}"
    return 1
