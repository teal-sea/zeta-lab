/-
A list-driven front end to the kernel replay that ships with Lean as
`leanchecker`. `replayFromImports` below is copied verbatim from
`src/lean/LeanChecker.lean` of Lean 4.33.1 (commit 819816b2e0a3, Apache 2.0,
authors Kim Morrison and Sebastian Ullrich). Only `main` is new. The file is a
`module`, as this repository asks of its Lean sources, which upstream's is
not: that is the `module` line and the `public` on `main`, and it changes
no line of the copied function.

Why not the `leanchecker` binary itself: it takes module-name prefixes and
walks every `.olean` on the search path once per target. The archive this
hunt replays keeps 42,424 modules in one directory, so there is no prefix
that selects a workable slice, and one walk per exact module name costs more
than the replay. This driver takes exact module names from a file, replays
them one after another in one process, and prints one line per module, so a
run that is stopped keeps what it finished and one bad module does not hide
the rest.

It runs no code of the modules it checks. It reads their `.olean` files,
imports their imports, and sends every constant of the module through the
kernel again (`Lean.Environment.replay`). As the upstream file says of
itself, this is not an external verifier; it detects declarations that
reached an `.olean` without passing the kernel.

One addition to the upstream function, marked below: the module's own
`.olean` is unmapped when its replay is done. Upstream leaves it mapped,
which costs nothing in a process that replays one module. In a process that
replays thousands in import order it costs gigabytes: a later module that
imports an earlier one cannot map that file at its address again, because
the first mapping is still there, and Lean then reads the whole file into
the heap instead. Check round 6 measured the result, driver processes
holding 2 to 5.6 GB of anonymous memory each and a runner out of swap.
-/
module

import Lean.CoreM
import Lean.Replay

open Lean

unsafe def replayFromImports (module : Name) : IO Unit := do
  let mFile ← findOLean module
  unless (← mFile.pathExists) do
    throw <| IO.userError s!"object file '{mFile}' of module {module} does not exist"
  -- Load all module data parts (exported, server, private)
  let mut fnames := #[mFile]
  let sFile := OLeanLevel.server.adjustFileName mFile
  if (← sFile.pathExists) then
    fnames := fnames.push sFile
    let pFile := OLeanLevel.private.adjustFileName mFile
    if (← pFile.pathExists) then
      fnames := fnames.push pFile
  let parts ← readModuleDataParts fnames
  if h : parts.size = 0 then throw <| IO.userError "failed to read module data" else
  -- (addition) the regions of the module's own files, to unmap at the end
  let ownRegions := parts.map (·.2)
  let (mod, _) := parts[0]
  let (_, s) ← importModulesCore mod.imports |>.run
  let env ← finalizeImport s mod.imports {} 0 false false (isModule := true)
  let mut newConstants := {}
  -- Collect constants from last ("most private") part, which subsumes all prior ones
  for name in parts[parts.size-1].1.constNames, ci in parts[parts.size-1].1.constants do
    newConstants := newConstants.insert name ci
  let env' ← env.replay newConstants
  env'.freeRegions
  -- (addition) Nothing that points into the module's own files is alive any
  -- more: `parts`, `mod` and `newConstants` were last used above and the
  -- environment built from them is gone.
  ownRegions.forM (·.free)

/-- Anonymous memory this process holds, in kB, from `/proc/self/status`; 0 where there is none. -/
def rssAnonKb : IO Nat := do
  try
    let status ← IO.FS.readFile "/proc/self/status"
    for line in status.splitOn "\n" do
      if line.startsWith "RssAnon:" then
        return line.foldl (fun acc c => if c.isDigit then acc * 10 + (c.toNat - 48) else acc) 0
    return 0
  catch _ => return 0

/-- `lean --run ReplayDriver.lean <file of module names>`: one line per module,
`OK<tab>module<tab>milliseconds<tab>anonymous kB` or
`FAIL<tab>module<tab>milliseconds<tab>message`. The fourth field of an `OK`
line is the anonymous memory the process holds once the module is done.
Exit code 0 if every module replayed, 1 otherwise. -/
public unsafe def main (args : List String) : IO UInt32 := do
  let [listFile] := args
    | do IO.eprintln "usage: lean --run ReplayDriver.lean <file of module names>"; return 2
  initSearchPath (← findSysroot)
  let out ← IO.getStdout
  let mut bad := 0
  for line in (← IO.FS.lines listFile) do
    let name := line.trimAscii.toString
    if name.isEmpty then continue
    let t0 ← IO.monoMsNow
    try
      replayFromImports name.toName
      out.putStrLn s!"OK\t{name}\t{(← IO.monoMsNow) - t0}\t{← rssAnonKb}"
    catch e =>
      bad := bad + 1
      let msg := (toString e).replace "\n" " | "
      out.putStrLn s!"FAIL\t{name}\t{(← IO.monoMsNow) - t0}\t{msg}"
    out.flush
  return if bad == 0 then 0 else 1
