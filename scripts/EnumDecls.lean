/-
Print every public declaration of the owner-authored libraries, one per line, as
`<library>\t<name>`.

The subsystem audits are hand-maintained lists, and `check_audit.py` compares
what a run printed against what the file commanded -- so a listed name that
disappears breaks the build, and a new declaration nobody listed is invisible.
`scripts/check_audit_complete.py` closes the other direction by diffing this
sweep against the lists.

Run: `lake env lean scripts/EnumDecls.lean`

Auto-generated constructions are filtered here rather than in the consumer,
because the environment is where the information lives: `.casesOn`, `.recOn`,
`.noConfusion`, `.injEq`, and the `match_`/`proof_` internals are produced by
declaring an inductive or by tactic elaboration, and no audit should list them.
-/
import DerivedAlgGeoLean
import DGLean
import CohLean.Development.AlgebraicGeometry.Divisors.API
import CohLean.Numerical.Specializations.Surface
import CohLean.Numerical.Specializations.Threefold
import CohLean.Numerical.Specializations.Fourfold

open Lean

/-- Suffixes Lean generates on the author's behalf. -/
private def autoSuffixes : List String :=
  [".casesOn", ".recOn", ".rec", ".brecOn", ".below", ".ibelow", ".binductionOn",
   ".noConfusion", ".noConfusionType", ".ctorIdx", ".toCtorIdx", ".sizeOf",
   ".injEq", ".mk", ".ofNat", ".eq_def", ".induct"]

/-- Is this a name a human wrote, rather than one elaboration produced? -/
private def isAuthored (n : Name) : Bool := Id.run do
  let s := n.toString
  if autoSuffixes.any (fun suf => s.endsWith suf) then return false
  -- `_proof_1`, `match_2`, `eq_3`, and the `._` internals.
  if (s.splitOn "._").length > 1 then return false
  if (s.splitOn "proof_").length > 1 then return false
  if (s.splitOn "match_").length > 1 then return false
  -- Equation lemmas: `prodD.eq_1`, `foo.eq_2`, … Missing these was what made a
  -- complete `DGLean` audit look like it was one declaration short.
  if (s.splitOn ".eq_").length > 1 then return false
  return true

/-- The owning library of a module, i.e. its first name component. -/
private def libraryOf (m : Name) : Option String :=
  match m.components with
  | root :: _ =>
    let r := root.toString
    if r == "CohLean" || r == "BridgelandStabLean" || r == "DGLean" then some r else none
  | _ => none

run_cmd do
  let env ← Lean.getEnv
  let mut rows : Array String := #[]
  for (n, ci) in env.constants.toList do
    if n.isInternal || !isAuthored n then continue
    unless ci.isTheorem || ci.isDefinition || ci.isInductive || ci.isCtor do continue
    match env.getModuleIdxFor? n with
    | some idx =>
      match libraryOf env.header.moduleNames[idx.toNat]! with
      | some lib => rows := rows.push s!"{lib}\t{n}"
      | none => pure ()
    | none => pure ()
  for r in rows.qsort (· < ·) do
    IO.println r
