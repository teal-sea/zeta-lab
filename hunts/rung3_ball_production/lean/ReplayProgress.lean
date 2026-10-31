module

public import Lean
public import Lean.Replay

/-!
Hunt #145, door 1: the estimator for `leanchecker --fresh`, which prints nothing until it ends.

* `lean --run ReplayProgress.lean census MOD OUT` imports `MOD` as `leanchecker --fresh MOD`
  does (`importModules` with `loadExts := false`, at the private level, so every olean part)
  and writes `OUT`: each imported module's index, name and number of constants, by the
  environment's constant-to-module map. These are the constants `--fresh` replays.
* `lean --run ReplayProgress.lean sample OUT MOD...` replays each `MOD`'s own constants into
  the environment of its imports, as `leanchecker MOD` (without `--fresh`) does, and appends
  to `OUT` one line per module: name, constants, milliseconds to import, milliseconds to
  replay. The replay time is the kernel's work on that module's constants alone, so a random
  sample of modules estimates the whole replay.

A first version replayed the whole closure module by module in import order, to log
progress. That order is not valid, so its stop is not a verdict on the environment: at
`List.drop.eq_def` it met `(kernel) unknown constant` for a private splitter that the
constant-to-module map files under a later module, because constants realized on demand
(`eq_def`, splitters) are filed out of dependency order. A sample replays each module's own
olean, which is self-consistent, as `leanchecker` does.
-/

open Lean

/-- `leanchecker`'s `replayFromImports`, timed. -/
unsafe def sampleOne (h : IO.FS.Handle) (module : Name) : IO Unit := do
  let mFile ← findOLean module
  let mut fnames := #[mFile]
  let sFile := OLeanLevel.server.adjustFileName mFile
  if (← sFile.pathExists) then
    fnames := fnames.push sFile
    let pFile := OLeanLevel.private.adjustFileName mFile
    if (← pFile.pathExists) then
      fnames := fnames.push pFile
  let parts ← readModuleDataParts fnames
  let some (mod, _) := parts[0]? | throw <| IO.userError s!"no data for {module}"
  let some (last, _) := parts[parts.size - 1]? | throw <| IO.userError s!"no data for {module}"
  let a ← IO.monoMsNow
  let (_, s) ← importModulesCore mod.imports |>.run
  let env ← finalizeImport s mod.imports {} 0 false false (isModule := true)
  let mut newConstants : Std.HashMap Name ConstantInfo := {}
  for name in last.constNames, ci in last.constants do
    newConstants := newConstants.insert name ci
  let b ← IO.monoMsNow
  discard <| env.toKernelEnv.replay newConstants
  let c ← IO.monoMsNow
  h.putStrLn s!"{module}\t{newConstants.size}\t{b - a}\t{c - b}"
  h.flush
  env.freeRegions

public unsafe def main (args : List String) : IO UInt32 := do
  initSearchPath (← findSysroot)
  match args with
  | ["census", mod, out] =>
    let env ← importModules (loadExts := false) #[{ module := mod.toName }] {} 0
    let names := env.header.moduleNames
    let counts := env.constants.map₁.fold (init := Array.replicate names.size 0) fun acc n _ =>
      match env.getModuleIdxFor? n with
      | some i => acc.modify i.toNat (· + 1)
      | none => acc
    let h ← IO.FS.Handle.mk out .write
    for i in [:names.size] do
      h.putStrLn s!"{i}\t{names[i]!}\t{counts[i]!}"
    IO.println s!"{names.size} modules, {env.constants.map₁.size} constants"
    return 0
  | "sample" :: out :: mods =>
    let h ← IO.FS.Handle.mk out .append
    for m in mods do
      sampleOne h m.toName
    return 0
  | _ =>
    IO.eprintln "usage: ReplayProgress (census MOD OUT | sample OUT MOD...)"
    return 2
