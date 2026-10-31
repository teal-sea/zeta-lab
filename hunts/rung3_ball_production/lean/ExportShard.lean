module

public import Lean
public import LeanExport.Basic

/-!
Hunt #145, door 1, Stage B: the shard exporter for the site-wise `con-ron --verified` check.

Every shard is written by the toolchain's own exporter, `LeanExport.dumpEnv` (the code of
`leanexport`, format 3.1.0); this program only chooses the names and, for the top shard,
builds the declarations it exports. Compiled with `lean -c` and `leanc`, never with Lake.

* `names MOD NAME...`: `leanexport MOD -- NAME...` exactly (the control for this wrapper).
* `site ID`: imports the site root `C<ID>` and exports, to stdout, every constant whose module
  is `C<ID>` or `C<ID>.*` (in module order, then declaration order), each with its closure.
  So a site shard holds all of the site's own constants, not only its theorem's closure.
* `census MOD OUT`: imports `MOD` as `leanchecker --fresh MOD` does and writes one line per
  imported constant: name, module, kind.
* `closure MOD OUT NAME...`: the dependency closure of the given constants (types, values,
  an inductive's whole block with its constructors and recursors, the `Quot` package, and
  `Nat`, `Char.ofNat`, `String.ofList` for literals, as the exporter adds them), one name a
  line.
* `top MOD INFO NAME...`: the top shard. `con-ron --verified` declines any axiom but the three
  standard ones, so the 215 site theorems cannot enter as axioms. Instead every constant of a
  `Rung3Assembly.*` module that depends on a site theorem is abstracted over all of them: for
  each site theorem `S` (a theorem of a site module used by an assembly module) a definition
  `Rung3Glue.T.S : Prop := <the type of S>`, and for each such constant `c` a declaration
  `Rung3Glue.c : ∀ (h₁ : Rung3Glue.T.S₁) … (hₙ : Rung3Glue.T.Sₙ), <type of c>` whose value is
  `c`'s own value with each `Sᵢ` replaced by `hᵢ` and each such `c'` by `Rung3Glue.c' h₁ … hₙ`.
  Every new declaration goes through Lean's kernel first (`addDeclCore`, checking on). The
  export holds the given names, each replaced by its `Rung3Glue` form where it has one, and
  `INFO` records the site theorems, the abstracted constants and the site constants the
  assembly reaches other than through the site theorems. Applying `Rung3Glue.c` to the site
  theorems gives back `c`'s value exactly, so the top shard and the 215 site shards together
  check the assembly's own proof terms, with the types matched by hash across the shards.
-/

open Lean

namespace ExportShard

def str (n : Name) : String := n.toString (escape := false)

def moduleOf (env : Environment) (n : Name) : Option Name := do
  let i ← env.getModuleIdxFor? n
  env.header.moduleNames[i.toNat]?

def kindOf : ConstantInfo → String
  | .axiomInfo _ => "axiom" | .defnInfo _ => "def" | .thmInfo _ => "thm"
  | .opaqueInfo _ => "opaque" | .quotInfo _ => "quot" | .inductInfo _ => "induct"
  | .ctorInfo _ => "ctor" | .recInfo _ => "rec"

/-- A module of a site: `C<id>` or `C<id>.*` for a plan v2 id (`B_*`, `g_*`, `centre`).
`Cli`, a dependency, also starts with `C`, so the prefix alone is not enough. -/
def isSiteModule (m : Name) : Bool :=
  match m.components.head? with
  | some (.str .anonymous s) => s.startsWith "CB_" || s.startsWith "Cg_" || s == "Ccentre"
  | _ => false

def isAsmModule (m : Name) : Bool :=
  m.components.head? == some `Rung3Assembly

def exprDeps (e : Expr) : Array Name := Id.run do
  let mut out := e.getUsedConstants
  if (e.find? (· matches .lit (.natVal _))).isSome then out := out.push ``Nat
  if (e.find? (· matches .lit (.strVal _))).isSome then
    out := out.push ``Char.ofNat |>.push ``String.ofList
  return out

/-- What the exporter dumps along with `ci`. -/
def deps (env : Environment) (recs : NameMap (Array Name)) (ci : ConstantInfo) : Array Name :=
  let base := exprDeps ci.type
  match ci with
  | .defnInfo v => base ++ exprDeps v.value
  | .thmInfo v => base ++ exprDeps v.value
  | .opaqueInfo v => base ++ exprDeps v.value
  | .axiomInfo _ => base
  | .quotInfo _ => base ++ #[``Eq, ``Quot, ``Quot.mk, ``Quot.lift, ``Quot.ind]
  | .inductInfo v => Id.run do
      let mut out := base ++ v.all.toArray
      for i in v.all do
        if let some (.inductInfo w) := env.find? i then
          out := out ++ w.ctors.toArray
        out := out ++ (recs.find? i).getD #[]
      return out
  | .ctorInfo v => base.push v.induct
  | .recInfo v => Id.run do
      let mut out := base ++ v.all.toArray
      for r in v.rules do out := out ++ exprDeps r.rhs
      return out

def recursorMap (env : Environment) : NameMap (Array Name) := Id.run do
  let mut m : NameMap (Array Name) := {}
  for (_, ci) in env.constants.map₁.toList do
    if let .recInfo r := ci then
      for i in r.all do
        m := m.insert i ((m.find? i).getD #[] |>.push r.name)
  return m

def closure (env : Environment) (roots : Array Name) : IO NameHashSet := do
  let recs := recursorMap env
  let mut seen : NameHashSet := {}
  let mut stack := roots
  while h : stack.size > 0 do
    let n := stack[stack.size - 1]
    stack := stack.pop
    if seen.contains n then continue
    let some ci := env.find? n | throw <| IO.userError s!"closure: unknown constant {n}"
    seen := seen.insert n
    for d in deps env recs ci do
      unless seen.contains d do stack := stack.push d
  return seen

def importOne (mod : String) : IO Environment :=
  importModules (loadExts := false) #[{ module := mod.toName }] {} 0

def glueName (n : Name) : Name := `Rung3Glue ++ n
def typeName (n : Name) : Name := `Rung3Glue.T ++ n

def addChecked (env : Environment) (d : Declaration) : IO Environment := do
  match env.addDeclCore 0 0 d none (doCheck := true) with
  | .ok e => pure e
  | .error ex =>
    let msg ← (ex.toMessageData {}).toString
    throw <| IO.userError s!"Lean's kernel refused {d.getNames}: {msg.take 400}"

/-- The top shard: see the module docstring. Returns the names to export. -/
def buildTop (env0 : Environment) (finals : Array Name) (info : System.FilePath) :
    IO (Environment × Array Name) := do
  let asm := env0.constants.map₁.toList.filter fun (n, _) =>
    (moduleOf env0 n).any isAsmModule
  let asmSet : NameHashSet := asm.foldl (fun s (n, _) => s.insert n) {}
  -- the site theorems the assembly modules name, and the site constants they reach otherwise
  let mut siteThms : NameHashSet := {}
  let mut siteOther : NameHashSet := {}
  for (_, ci) in asm do
    let ds := exprDeps ci.type ++ ((ci.value? (allowOpaque := true)).map exprDeps |>.getD #[])
    for d in ds do
      if (moduleOf env0 d).any isSiteModule then
        match env0.find? d with
        | some (.thmInfo _) => siteThms := siteThms.insert d
        | _ => siteOther := siteOther.insert d
  let sArr := siteThms.toArray.qsort (fun a b => str a < str b)
  -- every assembly constant whose value reaches a site theorem, in dependency order
  let mut order : Array Name := #[]
  let mut dep? : NameMap Bool := {}
  let mut visiting : NameHashSet := {}
  let asmSorted := asm.toArray.map (·.1) |>.qsort (fun a b => str a < str b)
  for root in asmSorted do
    -- iterative post-order over assembly constants
    let mut stack : Array (Name × Bool) := #[(root, false)]
    while h : stack.size > 0 do
      let (n, done) := stack[stack.size - 1]
      stack := stack.pop
      if dep?.contains n then continue
      let some ci := env0.find? n | throw <| IO.userError s!"unknown {n}"
      let ds := (exprDeps ci.type ++ ((ci.value? (allowOpaque := true)).map exprDeps |>.getD #[]))
      let asmDs := ds.filter (fun d => asmSet.contains d && d != n)
      if done then
        let hits := ds.any siteThms.contains || asmDs.any (fun d => (dep?.find? d).getD false)
        dep? := dep?.insert n hits
        if hits then order := order.push n
        visiting := visiting.erase n
      else
        if visiting.contains n then throw <| IO.userError s!"cycle at {n}"
        visiting := visiting.insert n
        stack := stack.push (n, true)
        for d in asmDs do
          unless dep?.contains d do stack := stack.push (d, false)
  let abs : NameHashSet := order.foldl (·.insert ·) {}
  -- no type may mention a site theorem or an abstracted constant
  for (n, ci) in asm do
    let tds := exprDeps ci.type
    if tds.any (fun d => siteThms.contains d || abs.contains d) then
      throw <| IO.userError s!"the type of {n} mentions a site theorem or an abstracted constant"
  let mut env := env0
  -- Rung3Glue.T.S : Prop := type of S
  for s in sArr do
    let some (.thmInfo v) := env.find? s | throw <| IO.userError s!"{s} is not a theorem"
    unless v.levelParams.isEmpty do throw <| IO.userError s!"{s} has universe parameters"
    env ← addChecked env <| .defnDecl {
      name := typeName s, levelParams := [], type := .sort .zero, value := v.type,
      hints := .abbrev, safety := .safe, all := [typeName s] }
  let fvars : Array Expr := (Array.range sArr.size).map fun i => .fvar ⟨.num `_rung3glue i⟩
  let idx : NameMap Nat := (Array.range sArr.size).foldl (fun m i => m.insert sArr[i]! i) {}
  let wrap (body : Expr) (lam : Bool) : Expr := Id.run do
    let mut e := body.abstract fvars
    for j in [:sArr.size] do
      let i := sArr.size - 1 - j
      let t : Expr := .const (typeName sArr[i]!) []
      let bn : Name := .num `h i
      e := if lam then .lam bn t e .default else .forallE bn t e .default
    return e
  let subst (e : Expr) : Expr := e.replace fun x => match x with
    | .const n us =>
      if let some i := idx.find? n then some fvars[i]!
      else if abs.contains n then some (mkAppN (.const (glueName n) us) fvars)
      else none
    | _ => none
  for c in order do
    let some ci := env.find? c | throw <| IO.userError s!"unknown {c}"
    let ty := wrap ci.type false
    match ci with
    | .thmInfo v =>
      env ← addChecked env <| .thmDecl {
        name := glueName c, levelParams := v.levelParams, type := ty,
        value := wrap (subst v.value) true, all := [glueName c] }
    | .defnInfo v =>
      env ← addChecked env <| .defnDecl {
        name := glueName c, levelParams := v.levelParams, type := ty,
        value := wrap (subst v.value) true, hints := v.hints, safety := v.safety,
        all := [glueName c] }
    | _ => throw <| IO.userError s!"{c} is neither a theorem nor a definition"
  let exportNames := finals.map fun f => if abs.contains f then glueName f else f
  let j := Json.mkObj [
    ("site_theorems", toJson (sArr.map str)),
    ("abstracted", toJson (order.map str)),
    ("site_constants_reached_otherwise", toJson ((siteOther.toArray.map str).qsort (· < ·))),
    ("assembly_constants", toJson ((asm.toArray.map (str ·.1)).qsort (· < ·))),
    ("export_names", toJson (exportNames.map str))]
  IO.FS.writeFile info (j.pretty ++ "\n")
  return (env, exportNames)

end ExportShard

open ExportShard in
public unsafe def main (args : List String) : IO UInt32 := do
  initSearchPath (← findSysroot)
  match args with
  | ["site", sid] =>
    let root := "C" ++ sid
    let env ← importOne root
    let mods := env.header.moduleNames
    let mut names : Array Name := #[]
    let mut perModule : Array (String × Nat) := #[]
    for i in [:mods.size] do
      let m := mods[i]!
      if m == root.toName || (root.toName).isPrefixOf m then
        let some md := env.header.moduleData[i]? | throw <| IO.userError s!"no data for {m}"
        names := names ++ md.constNames
        perModule := perModule.push (str m, md.constNames.size)
    IO.eprintln s!"site {sid}: {names.size} constants in {perModule}"
    LeanExport.dumpEnv env (some names.toList)
    return 0
  | "names" :: mod :: names =>
    -- `leanexport MOD -- NAME...` exactly, the control that this wrapper changes nothing
    let env ← importOne mod
    LeanExport.dumpEnv env (some (names.map String.toName))
    return 0
  | ["census", mod, out] =>
    let env ← importOne mod
    let h ← IO.FS.Handle.mk out .write
    let mut k := 0
    for (n, ci) in env.constants.map₁.toList do
      let m := (moduleOf env n).map str |>.getD "?"
      h.putStrLn s!"{str n}\t{m}\t{kindOf ci}"
      k := k + 1
    h.flush
    IO.eprintln s!"census: {k} constants, {env.header.moduleNames.size} modules"
    return 0
  | "closure" :: mod :: out :: roots =>
    let env ← importOne mod
    let seen ← closure env (roots.toArray.map String.toName)
    let h ← IO.FS.Handle.mk out .write
    for n in seen.toArray do h.putStrLn (str n)
    h.flush
    IO.eprintln s!"closure: {seen.size} constants"
    return 0
  | "top" :: mod :: info :: finals =>
    let env ← importOne mod
    let (env, names) ← buildTop env (finals.toArray.map String.toName) info
    IO.eprintln s!"top: exporting {names}"
    LeanExport.dumpEnv env (some names.toList)
    return 0
  | _ =>
    IO.eprintln "usage: ExportShard (names MOD NAME... | site ID | census MOD OUT | closure MOD OUT NAME... | top MOD INFO NAME...)"
    return 2
