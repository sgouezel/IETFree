/-
Copyright (c) 2026 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/

import Lean

/-!
# A local stand-in for the comparator

The genuine comparator has been run on this pair — `Comparator/README.md` records the revision pair
(comparator `3927ad3` with `lean4export` at the `v4.33.0` tag, both built with the local Lean 4.33.1),
the shim used in place of the sandbox (`landrun` is not installed here), and the verdict.  It is not part of the build, though: it exports both modules, compares them declaration by
declaration and replays the whole solution into the kernel, and it needs a Lake project.  This file is
the cheap always-on guard instead: it runs the *same algorithm* as `Comparator/Compare.lean` and
`Comparator/Axioms.lean` directly on the two `.olean` environments, which is what the comparator does
on the two `lean4export` exports:

* each name in `theorem_names` is looked up in both environments, must be a theorem in both, and its
  statement (`ConstantVal`: name, universe parameters, type) is compared, up to `Expr.eqv` (alpha
  equivalence, which ignores binder names and `mdata`);
* each name in `definition_names` is a *definition hole*: it must be a definition in both, its
  statement and safety must agree, and — as in the comparator — its **body is not compared**, so a
  challenge need not reproduce the proofs inside a definition; the solution's definition must
  nevertheless be axiom-clean;
* every other constant reachable from those statements — walking types, values (proofs included) and
  the constructor fields of inductive declarations, exactly as `Comparator.runForUsedConsts` does —
  must be the **same** `ConstantInfo` in both environments;
* the solution's proofs and definitions must not use an axiom outside `permitted_axioms`.

Differences with the real thing: the comparator runs on exported declarations, where `mdata` is
erased anyway, and it replays the solution into the kernel; here the kernel check is the one `lean`
already did when it produced the solution's `.olean`.

Usage, from `IET2/`:

    lean --run Comparator/Check.lean

which is what `Build.sh` does, so a drift between the challenge and the library breaks the build.
-/

open Lean

namespace ComparatorCheck

deriving instance BEq for Lean.QuotKind
deriving instance BEq for Lean.QuotVal
deriving instance BEq for Lean.InductiveVal
deriving instance BEq for Lean.ConstantInfo

/-- The constants a declaration uses, exactly as `Comparator.runForUsedConsts` collects them: its
type, itself, its value (proofs included), and for inductive declarations the constructors and the
auxiliary fields. -/
def usedConsts (info : ConstantInfo) : Array Name := Id.run do
  let mut cs := info.type.getUsedConstants
  cs := cs.push info.name
  if let some v := info.value? (allowOpaque := true) then
    cs := cs ++ v.getUsedConstants
  match info with
  | .inductInfo i => return cs ++ i.ctors.toArray ++ i.all.toArray
  | .ctorInfo i => return cs.push i.induct
  | .recInfo i =>
    for r in i.rules do
      cs := cs.push r.ctor
      cs := cs ++ r.rhs.getUsedConstants
    return cs
  | _ => return cs

/-- The two environments, the exempt targets, and a bound on the work. -/
structure Ctx where
  challenge : Environment
  solution : Environment
  targets : Std.HashSet Name
  fuel : Nat

/-- The state of the comparison: what is left to visit, what was visited, and what went wrong. -/
structure St where
  worklist : Array Name
  checked : Std.HashSet Name
  mismatches : Array String
  compared : Nat

/-- `Comparator.Compare.loop`: visit every constant reachable from the statements, check that it is
the same in both environments, and collect the mismatches.  The targets (the theorems and the
definition holes) are exempt from the value comparison: only the constants of their statements are
visited. -/
partial def go (ctx : Ctx) (st : St) : St :=
  if st.compared ≥ ctx.fuel then
    { st with mismatches := st.mismatches.push "out of fuel (the comparison did not terminate)" }
  else if st.worklist.isEmpty then st
  else
    let target := st.worklist.back!
    let worklist := st.worklist.pop
    if st.checked.contains target then go ctx { st with worklist }
    else
      let st : St :=
        { st with worklist, checked := st.checked.insert target, compared := st.compared + 1 }
      match ctx.challenge.find? target, ctx.solution.find? target with
      | none, _ =>
        go ctx { st with mismatches := st.mismatches.push s!"not in the challenge: {target}" }
      | _, none =>
        go ctx { st with mismatches := st.mismatches.push s!"not in the solution: {target}" }
      | some c, some s =>
        if ctx.targets.contains s.name then
          go ctx { st with worklist := st.worklist ++ s.type.getUsedConstants }
        else if c != s then
          go ctx { st with mismatches := st.mismatches.push s!"differs: {target}" }
        else
          go ctx { st with worklist := st.worklist ++ usedConsts s }

/-- The axioms used by `targets` in `env`, as `Comparator.Axioms` collects them. -/
partial def axiomsOf (env : Environment) (targets : Array Name) : Std.HashSet Name :=
  let rec loop (todo : Array Name) (seen acc : Std.HashSet Name) : Std.HashSet Name :=
    if todo.isEmpty then acc
    else
      let n := todo.back!
      let todo := todo.pop
      if seen.contains n then loop todo seen acc
      else
        let seen := seen.insert n
        match env.find? n with
        | none => loop todo seen acc
        | some info =>
          let acc := match info with
            | .axiomInfo _ => if acc.contains n then acc else acc.insert n
            | _ => acc
          loop (todo ++ usedConsts info) seen acc
  loop targets {} {}

/-- The fields of `comparator.json` this check needs. -/
structure Config where
  challenge : Name
  solution : Name
  theorems : Array Name
  definitions : Array Name
  permitted : Array Name

def readConfig (path : String) : IO Config := do
  let text ← IO.FS.readFile path
  let .ok json := Json.parse text | throw (IO.userError s!"cannot parse {path}")
  let str (k : String) : Except String String := json.getObjVal? k >>= Json.getStr?
  let strs (k : String) : Except String (Array Name) := do
    (← (← json.getObjVal? k).getArr?).mapM (fun j => return (← j.getStr?).toName)
  -- `definition_names` is optional in the comparator's configuration
  let strs? (k : String) : Except String (Array Name) := do
    let .ok j := json.getObjVal? k | return #[]
    (← j.getArr?).mapM (fun j => return (← j.getStr?).toName)
  return {
    challenge := (← IO.ofExcept (str "challenge_module")).toName
    solution := (← IO.ofExcept (str "solution_module")).toName
    theorems := ← IO.ofExcept (strs "theorem_names")
    definitions := ← IO.ofExcept (strs? "definition_names")
    permitted := ← IO.ofExcept (strs "permitted_axioms")
  }

def main : IO UInt32 := do
  let cfg ← readConfig "comparator.json"
  IO.println s!"challenge module:  {cfg.challenge}"
  IO.println s!"solution module:   {cfg.solution}"
  IO.println s!"theorem targets:   {cfg.theorems}"
  IO.println s!"definition holes:  {cfg.definitions}"
  let challenge ← importModules #[{ module := cfg.challenge }] {}
  let solution ← importModules #[{ module := cfg.solution }] {}
  let mut problems : Array String := #[]
  let mut worklist : Array Name := #[]
  -- 1. the statements: same name, same universe parameters, same type
  for t in cfg.theorems do
    match challenge.find? t, solution.find? t with
    | some (.thmInfo c), some (.thmInfo s) =>
      if c.toConstantVal != s.toConstantVal then
        problems := problems.push s!"the statement differs: {t}"
      worklist := worklist ++ c.type.getUsedConstants
    | none, _ => problems := problems.push s!"the statement is missing from the challenge: {t}"
    | _, none => problems := problems.push s!"the statement is missing from the solution: {t}"
    | _, _ => problems := problems.push s!"not a theorem: {t}"
  -- 2. the definition holes: same statement and safety, body not compared
  for t in cfg.definitions do
    match challenge.find? t, solution.find? t with
    | some (.defnInfo c), some (.defnInfo s) =>
      if c.toConstantVal != s.toConstantVal then
        problems := problems.push s!"the definition's type differs: {t}"
      if c.safety != s.safety then
        problems := problems.push s!"the definition's safety differs: {t}"
      worklist := worklist.push t
    | none, _ => problems := problems.push s!"the definition is missing from the challenge: {t}"
    | _, none => problems := problems.push s!"the definition is missing from the solution: {t}"
    | _, _ => problems := problems.push s!"not a definition: {t}"
  -- 3. every declaration the statements use
  let targets := Std.HashSet.ofArray (cfg.theorems ++ cfg.definitions)
  let st := go { challenge, solution, targets, fuel := 5000000 }
    { worklist, checked := {}, mismatches := problems, compared := 0 }
  -- 4. the axioms of the solution's proofs and definitions
  let axioms := axiomsOf solution (cfg.theorems ++ cfg.definitions)
  let illegal := axioms.toArray.filter (fun a => !cfg.permitted.contains a)
  IO.println s!"declarations compared: {st.compared}"
  IO.println s!"axioms of the solution:    {axioms.toArray.qsort (fun a b => a.toString < b.toString)}"
  IO.println s!"permitted by the config:   {cfg.permitted}"
  if st.mismatches.isEmpty && illegal.isEmpty then
    IO.println "OK: the statements agree, every declaration they use is the same in both, and the \
      proofs use only the permitted axioms -- the comparator would accept this pair."
    return 0
  else
    for m in st.mismatches do
      IO.println s!"  PROBLEM: {m}"
    for a in illegal do
      IO.println s!"  PROBLEM: axiom not permitted: {a}"
    IO.println "NOT OK: see above."
    return 1

end ComparatorCheck

def main : IO UInt32 := ComparatorCheck.main
