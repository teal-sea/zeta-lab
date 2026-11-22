/-
The constants one module declares, read from its `.olean` files.

  lean --run ModuleConsts.lean <module>

One JSON object per line: `{"name": [components], "kind": "theorem", "unsafe":
false, "partial": false}`. A name is given as its components, strings and
numbers, so that it can be compared with the names of an export file without
either side having to print and parse a dotted name.

Why: `export_check.py` exports one declaration and what it depends on, and has
to say whether that covered the whole module or only the part the declaration
reaches. It reads the stored constants and runs no code of the module, like
the replay drivers beside it.
-/
module

import Lean.CoreM

open Lean

/-- A name as a list of its components. -/
def components : Name → List Json
  | .anonymous => []
  | .str p s => components p ++ [Json.str s]
  | .num p n => components p ++ [toJson n]

def kindOf : ConstantInfo → String
  | .axiomInfo _ => "axiom"
  | .defnInfo _ => "def"
  | .thmInfo _ => "theorem"
  | .opaqueInfo _ => "opaque"
  | .quotInfo _ => "quot"
  | .inductInfo _ => "inductive"
  | .ctorInfo _ => "constructor"
  | .recInfo _ => "recursor"

public unsafe def main (args : List String) : IO UInt32 := do
  let [name] := args
    | do IO.eprintln "usage: lean --run ModuleConsts.lean <module>"; return 2
  initSearchPath (← findSysroot)
  let mFile ← findOLean name.toName
  unless (← mFile.pathExists) do
    IO.eprintln s!"object file '{mFile}' of module {name} does not exist"
    return 1
  -- every part the module has (exported, server, private); the last holds all
  let mut fnames := #[mFile]
  let sFile := OLeanLevel.server.adjustFileName mFile
  if (← sFile.pathExists) then
    fnames := fnames.push sFile
    let pFile := OLeanLevel.private.adjustFileName mFile
    if (← pFile.pathExists) then
      fnames := fnames.push pFile
  let parts ← readModuleDataParts fnames
  if h : parts.size = 0 then
    IO.eprintln "failed to read module data"
    return 1
  else
    let mod := parts[parts.size - 1].1
    for n in mod.constNames, ci in mod.constants do
      IO.println (Json.mkObj [("name", Json.arr (components n).toArray), ("kind", toJson (kindOf ci)),
        ("unsafe", toJson ci.isUnsafe), ("partial", toJson ci.isPartial)]).compress
    return 0
