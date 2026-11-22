/-
A list-driven front end to lean4lean's replay, as `ReplayDriver.lean` is to
the replay behind `leanchecker`.

lean4lean (github.com/digama0/lean4lean, Apache 2.0) is a type checker for
Lean 4 written in Lean. Its `Lean4Lean.Replay.replayFromImports` does what
the function in `ReplayDriver.lean` does, with its own checker in place of
the C++ kernel: it reads a module's `.olean`, imports its imports, and sends
every constant of the module through `Lean4Lean.addDecl`. This file adds the
same `main` as `ReplayDriver.lean`: exact module names from a file, one after
another in one process, one line per module.

What it is and is not. It is a second implementation of the checking logic.
Its own README says it "is derived directly from the C++ kernel
implementation, and as such likely shares some implementation bugs with it",
and it runs on the same runtime, so it is a second route and not an
independent one. It runs no code of the modules it checks.

Unlike the other Lean files of this repository it is not a `module`:
lean4lean's files are not, and a `module` may not import one
(`tests/test_palomar_module_port.py` names this file as the exception). It is
compiled on the runner against lean4lean at the commit the workflow pins,
because a checker written in Lean is far too slow under `lean --run`.
-/
import Lean4Lean.Replay

open Lean hiding Environment Exception
open Lean4Lean.Replay

/-- Anonymous memory this process holds, in kB, from `/proc/self/status`; 0 where there is none. -/
def rssAnonKb : IO Nat := do
  try
    let status ← IO.FS.readFile "/proc/self/status"
    for line in status.splitOn "\n" do
      if line.startsWith "RssAnon:" then
        return line.foldl (fun acc c => if c.isDigit then acc * 10 + (c.toNat - 48) else acc) 0
    return 0
  catch _ => return 0

/-- lean4lean's fuel, every counter times `k`, the recursion depth times at
most ten. Its loops are bounded by counters "set so mathlib passes"
(`Lean4Lean/FuelConfig.lean`); a declaration that needs more ends in
`deterministic timeout` or `deep recursion`, which says that lean4lean gave
up and nothing about the declaration. The depth is the one counter that
costs stack, so it is raised less. -/
def scaledFuel (k : Nat) : Lean4Lean.FuelConfig :=
  let f : Lean4Lean.FuelConfig := {}
  { f with
    whnf := f.whnf * k
    whnfEager := f.whnfEager * k
    lazyDelta := f.lazyDelta * k
    etaExpand := f.etaExpand * k
    recDepth := f.recDepth * (min k 10)
    inductiveFuel := f.inductiveFuel * k }

/-- `l4ldriver <file of module names>`: one line per module,
`OK<tab>module<tab>milliseconds<tab>anonymous kB<tab>declarations` or
`FAIL<tab>module<tab>milliseconds<tab>message`. The fourth field of an `OK`
line is the anonymous memory the process holds once the module is done, the
fifth the number of declarations lean4lean added. Exit code 0 if every module
replayed, 1 otherwise. The environment variable `L4L_FUEL_SCALE`, a whole
number of at least 1, multiplies lean4lean's fuel (`scaledFuel`); without it
the fuel is lean4lean's own. -/
unsafe def main (args : List String) : IO UInt32 := do
  let [listFile] := args
    | do IO.eprintln "usage: l4ldriver <file of module names>"; return 2
  let scale := max 1 (((← IO.getEnv "L4L_FUEL_SCALE").bind (·.trimAscii.toString.toNat?)).getD 1)
  let fuel := scaledFuel scale
  if scale != 1 then IO.eprintln s!"l4ldriver: fuel times {scale}"
  initSearchPath (← findSysroot)
  let out ← IO.getStdout
  let mut bad := 0
  for line in (← IO.FS.lines listFile) do
    let name := line.trimAscii.toString
    if name.isEmpty then continue
    let t0 ← IO.monoMsNow
    try
      let n ← replayFromImports name.toName (fuel := fuel)
      out.putStrLn s!"OK\t{name}\t{(← IO.monoMsNow) - t0}\t{← rssAnonKb}\t{n}"
    catch e =>
      bad := bad + 1
      let msg := (toString e).replace "\n" " | "
      out.putStrLn s!"FAIL\t{name}\t{(← IO.monoMsNow) - t0}\t{msg}"
    out.flush
  return if bad == 0 then 0 else 1
