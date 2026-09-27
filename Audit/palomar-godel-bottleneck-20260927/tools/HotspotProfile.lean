import FailureOfComposition.Palomar.SolutionThree
import Lean
import Lean.Meta.Sym.ExprPtr

set_option autoImplicit false

open Lean Elab Command

namespace FailureOfComposition.Palomar.GodelHotspotProfile

private abbrev PhysicalSet := Std.HashSet Lean.Meta.Sym.ExprPtr
private abbrev StructuralSet := Std.HashSet Expr

private def dependencies (info : ConstantInfo) : Array Name :=
  match info with
  | .axiomInfo value => value.type.getUsedConstants
  | .defnInfo value => value.type.getUsedConstants ++ value.value.getUsedConstants
  | .thmInfo value => value.type.getUsedConstants ++ value.value.getUsedConstants
  | .opaqueInfo value => value.type.getUsedConstants ++ value.value.getUsedConstants
  | .ctorInfo value => value.type.getUsedConstants
  | .recInfo value => value.type.getUsedConstants
  | .inductInfo value => value.type.getUsedConstants ++ value.ctors.toArray
  | .quotInfo value => value.type.getUsedConstants

private partial def closure (env : Environment) (todo : List Name)
    (seen : NameSet := {}) : Except String NameSet := do
  match todo with
  | [] => return seen
  | name :: rest =>
    if seen.contains name then closure env rest seen
    else
      let some info := env.checked.get.find? name
        | throw s!"unresolved dependency: {name}"
      closure env ((dependencies info).toList ++ rest) (seen.insert name)

private partial def findPathAux (env : Environment) (target : Name)
    (todo : List (Name × List Name)) (seen : NameSet := {}) : Option (List Name) :=
  match todo with
  | [] => none
  | (name, reversedPath) :: rest =>
    if seen.contains name then findPathAux env target rest seen
    else if name == target then some (name :: reversedPath).reverse
    else
      match env.checked.get.find? name with
      | none => findPathAux env target rest (seen.insert name)
      | some info =>
        let next := dependencies info |>.toList.map fun dep => (dep, name :: reversedPath)
        findPathAux env target (next ++ rest) (seen.insert name)

private unsafe def visitDistinct (expr : Expr)
    (physical : PhysicalSet) (structural : StructuralSet) :
    PhysicalSet × StructuralSet :=
  let pointer : Lean.Meta.Sym.ExprPtr := ⟨expr⟩
  if physical.contains pointer then (physical, structural)
  else
    let physical := physical.insert pointer
    let structural := structural.insert expr
    match expr with
    | .app f a =>
      let (physical, structural) := visitDistinct f physical structural
      visitDistinct a physical structural
    | .lam _ type body _ | .forallE _ type body _ =>
      let (physical, structural) := visitDistinct type physical structural
      visitDistinct body physical structural
    | .letE _ type value body _ =>
      let (physical, structural) := visitDistinct type physical structural
      let (physical, structural) := visitDistinct value physical structural
      visitDistinct body physical structural
    | .mdata _ body | .proj _ _ body => visitDistinct body physical structural
    | _ => (physical, structural)

private unsafe def pair (expr : Expr) : Nat × Nat :=
  let result := visitDistinct expr {} {}
  (result.1.size, result.2.size)

private def equalityHead (name : Name) : Bool :=
  name == ``Eq.rec || name == ``Eq.ndrec || name == ``Eq.mp || name == ``Eq.mpr ||
    name == ``Eq.symm || name == ``Eq.trans

private unsafe def equalityApplications (root : Expr) : Array (Name × Nat × Nat) := Id.run do
  let mut seen : PhysicalSet := {}
  let mut todo := [root]
  let mut result := #[]
  while let expr :: rest := todo do
    todo := rest
    let pointer : Lean.Meta.Sym.ExprPtr := ⟨expr⟩
    unless seen.contains pointer do
      seen := seen.insert pointer
      if let .const name _ := expr.getAppFn then
        if equalityHead name then
          let size := pair expr
          result := result.push (name, size.1, size.2)
      todo := match expr with
        | .app f a => f :: a :: todo
        | .lam _ type body _ | .forallE _ type body _ => type :: body :: todo
        | .letE _ type value body _ => type :: value :: body :: todo
        | .mdata _ body | .proj _ _ body => body :: todo
        | _ => todo
  return result.qsort fun left right => decide (left.2.1 > right.2.1)

run_cmd do
  let env ← getEnv
  let name := `FFL.FirstOrder.Arithmetic.Bootstrapping.IsUTerm.BV.construction._proof_4
  let reBridge := ``FailureOfComposition.Palomar.Arithmetic.reAxiomCodes_toFoundation_iff
  let some info := env.checked.get.find? name | throwError "missing hotspot declaration"
  let some body := info.value? (allowOpaque := true) | throwError "missing hotspot body"
  let typeSize := pair info.type
  let bodySize := pair body
  let selected ← match closure env [name] with
    | .ok result => pure result
    | .error message => throwError message
  logInfo m!"HOTSPOT\tname={name}\tclosure={selected.size}\tphysicalType={typeSize.1}\tstructuralType={typeSize.2}\tphysicalBody={bodySize.1}\tstructuralBody={bodySize.2}"
  for dep in body.getUsedConstants.qsort (fun left right => decide (left.toString < right.toString)) do
    logInfo m!"HOTSPOT_DIRECT_BODY_DEP\t{dep}"
  let equalities := equalityApplications body
  logInfo m!"HOTSPOT_EQUALITIES\tcount={equalities.size}"
  for item in equalities[:30] do
    logInfo m!"HOTSPOT_EQUALITY\thead={item.1}\tphysical={item.2.1}\tstructural={item.2.2}"
  match findPathAux env name [(reBridge, [])] with
  | some path =>
    logInfo m!"RE_BRIDGE_TO_HOTSPOT\t{String.intercalate " -> " (path.map Name.toString)}"
  | none => throwError "hotspot is not reachable from the axiom-code bridge"

#print FFL.FirstOrder.Arithmetic.Bootstrapping.IsUTerm.BV.construction._proof_4

end FailureOfComposition.Palomar.GodelHotspotProfile
