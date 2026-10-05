import Lean
import GSArith.Ledger

/-!
# `axioms`: the axiom audit for the `GSArith` library

Adapted from TauCeti's `scripts/Axioms.lean` (The Tau Ceti contributors, Apache 2.0), whose
memoized reachability pass is reused verbatim.  Run via `lake exe axioms` after `lake build`.

Three checks, on the kernel environment rather than on source text:

1. **No home-rolled axioms anywhere.**  Every declaration defined in `GSArith` may depend only
   on `propext`, `Classical.choice`, `Quot.sound` and `sorryAx`.  This catches `native_decide`
   (`Lean.ofReduceBool`) and any `axiom` command, including ones reaching in through imports.
2. **Headline theorems are sorry-free.**  Every declaration tagged `@[gs_public]` must not
   depend on `sorryAx` either.
3. **Sorries are listed.**  Every declaration that reaches `sorryAx` is printed, so the list
   can be cross-checked against `LEDGER.md` (each such declaration should sit under an
   `OBLIGATION` tag).

Oracle *classes* are hypotheses of the theorems that use them, so they never show up here;
that is the point of bundling them instead of declaring axioms (`LEAN-PLAN.md`, §3.2).
-/

open Lean

/-- The library whose declarations are audited. -/
def auditedRoot : Name := `GSArith

/-- Axioms permitted in a `gs_public` declaration. -/
def standardAxioms : List Name := [``propext, ``Classical.choice, ``Quot.sound]

/-- Axioms tolerated in the library at large: the standard three, plus `sorry` (tracked by the
ledger rather than forbidden). -/
def toleratedAxioms : List Name := standardAxioms ++ [``sorryAx]

/-- Build the environment from the given imported modules and run `act` in `CoreM`.
`trustLevel := 1024`: imported constants are taken as type-correct, because `lake build` has
already kernel-checked them; this audit only asks *which axioms* a declaration depends on. -/
def withImportedEnv {α} (modules : Array Name) (act : CoreM α) : IO α := do
  initSearchPath (← findSysroot)
  unsafe Lean.withImportModules (modules.map (fun m => { module := m })) {} (trustLevel := 1024)
    fun env => Prod.fst <$> Core.CoreM.toIO act
      (ctx := { fileName := "<axioms>", fileMap := default }) (s := { env := env })

/-- Is `mod` the audited library root or one of its submodules? -/
def inAuditedLib (mod : Name) : Bool := mod == auditedRoot || auditedRoot.isPrefixOf mod

/-- The module name for a `.lean` source path, e.g. `GSArith/Foo/Bar.lean ↦ GSArith.Foo.Bar`. -/
def pathToModule (p : System.FilePath) : Name :=
  (p.withExtension "").components.foldl (fun n s => Name.mkStr n s) Name.anonymous

/-- Every `.lean` module under `dir`, recursively. -/
partial def collectLeanModules (dir : System.FilePath) : IO (Array Name) := do
  let mut acc := #[]
  for entry in (← dir.readDir) do
    if (← entry.path.isDir) then
      acc := acc ++ (← collectLeanModules entry.path)
    else if entry.path.extension == some "lean" then
      acc := acc.push (pathToModule entry.path)
  return acc

/-- Every module in the library: the root plus all `GSArith/**/*.lean`, enumerated from the
source tree so that a module missing from the root is still audited. -/
def auditedModules : IO (Array Name) :=
  return #[auditedRoot] ++ (← collectLeanModules (auditedRoot.toString : System.FilePath))

/-- Reader/State monad for the memoized axiom-reachability pass: the `Environment` and the
allowlist are read-only; the `NameMap Bool` memoizes, per constant, whether it transitively
depends on an axiom outside the allowlist. -/
abbrev AxiomCacheM := ReaderT (Environment × List Name) (StateM (Lean.NameMap Bool))

/-- Does `c` transitively depend on an axiom outside the allowlist?  Memoized; a constant is
marked `false` before recursing so cycles terminate (axioms are leaves, so this never lets a
violation pass, though it may under-report other members of a cyclic cluster).  Adapted from
Robin Arnez's mathlib-wide version via TauCeti. -/
partial def reachesDisallowedAxiom (c : Name) : AxiomCacheM Bool := do
  if let some res := (← get).find? c then return res
  modify (·.insert c false)
  let (env, allowed) ← read
  let anyExpr (es : Array Expr) : AxiomCacheM Bool :=
    es.anyM fun e => e.getUsedConstants.anyM reachesDisallowedAxiom
  let res ← match env.checked.get.find? c with
    | some (.axiomInfo v) =>
        if !allowed.contains c then pure true else anyExpr #[v.type]
    | some (.defnInfo v)   => anyExpr #[v.type, v.value]
    | some (.thmInfo v)    => anyExpr #[v.type, v.value]
    | some (.opaqueInfo v) => anyExpr #[v.type, v.value]
    | some (.quotInfo _)   => pure false
    | some (.ctorInfo v)   => anyExpr #[v.type]
    | some (.recInfo v)    => anyExpr #[v.type]
    | some (.inductInfo v) =>
        if (← anyExpr #[v.type]) then pure true else v.ctors.anyM reachesDisallowedAxiom
    | none                 => pure false
  modify (·.insert c res)
  return res

/-- Run the memoized pass over `candidates` with the given allowlist. -/
def offendersAgainst (env : Environment) (allowed : List Name) (candidates : Array Name) :
    Array Name :=
  (candidates.filterM reachesDisallowedAxiom |>.run (env, allowed)).run' {}

/-- The audit.  Returns `(audited, headline, violations, sorried)` with all names already
rendered to `String` (names loaded from `.olean`s are memory-mapped and unmapped once
`withImportModules` returns). -/
def audit : CoreM (Nat × Nat × Array String × Array String) := do
  let env ← getEnv
  let modNames := env.allImportedModuleNames
  let candidates : Array Name := env.constants.fold (init := #[]) fun acc declName _ =>
    match env.getModuleIdxFor? declName with
    | some idx =>
      match modNames[idx.toNat]? with
      | some m => if inAuditedLib m then acc.push declName else acc
      | none => acc
    | none => acc
  -- (1) anything beyond the tolerated axioms, anywhere in the library
  let hard := offendersAgainst env toleratedAxioms candidates
  let mut violations : Array String := #[]
  for declName in hard do
    let axs ← collectAxioms declName
    let bad := axs.filter fun a => !toleratedAxioms.contains a
    violations := violations.push s!"  {declName} → {bad.toList}"
  -- (2)+(3) sorry users; a gs_public sorry user is a violation
  let sorried := offendersAgainst env standardAxioms candidates
  let headline := candidates.filter (gsPublicAttr.hasTag env ·)
  let mut sorriedMsgs : Array String := #[]
  for declName in sorried do
    if gsPublicAttr.hasTag env declName then
      violations := violations.push s!"  {declName} is @[gs_public] but depends on sorryAx"
    sorriedMsgs := sorriedMsgs.push s!"  {declName}"
  return (candidates.size, headline.size, violations, sorriedMsgs)

-- Return the exit code rather than calling `IO.Process.exit`, so the imported environment is
-- torn down in order.
def main : IO UInt32 := do
  let modules ← auditedModules
  let (audited, headline, violations, sorried) ← withImportedEnv modules audit
  if audited == 0 then
    IO.eprintln s!"axioms: audited 0 declarations in {auditedRoot}: the audit is miswired."
    return 1
  IO.println s!"axioms: audited {audited} {auditedRoot} declaration(s), {headline} tagged @[gs_public]."
  if sorried.isEmpty then
    IO.println "axioms: no declaration depends on sorryAx."
  else
    IO.println s!"axioms: {sorried.size} declaration(s) depend on sorryAx (cross-check LEDGER.md):"
    for m in sorried do IO.println m
  if violations.isEmpty then
    IO.println s!"axioms: OK — no axiom beyond {toleratedAxioms}; every @[gs_public] declaration is sorry-free."
    return 0
  else
    IO.eprintln s!"axioms: {violations.size} violation(s):"
    for m in violations do IO.eprintln m
    return 1
