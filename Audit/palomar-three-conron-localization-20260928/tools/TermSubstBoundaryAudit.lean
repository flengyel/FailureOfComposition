import FailureOfComposition.Palomar.SolutionThree
import Lean

set_option autoImplicit false

open Lean Elab Command

namespace FailureOfComposition.Palomar.TermSubstBoundaryAudit

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
    if seen.contains name then
      closure env rest seen
    else
      let some info := env.checked.get.find? name
        | throw s!"unresolved dependency: {name}"
      closure env ((dependencies info).toList ++ rest) (seen.insert name)

private def getClosure (env : Environment) (roots : List Name) : CommandElabM NameSet :=
  match closure env roots with
  | .ok names => pure names
  | .error message => throwError message

private def axioms (env : Environment) (names : NameSet) : Array Name :=
  names.toArray.filter fun name =>
    match env.checked.get.find? name with
    | some (.axiomInfo _) => true
    | _ => false

run_cmd do
  let env ← getEnv
  let proof7 := `FFL.FirstOrder.Arithmetic.Bootstrapping.TermSubst.construction._proof_7
  let proof2 := `FFL.FirstOrder.Arithmetic.Bootstrapping.TermSubst.construction._proof_2
  let proof8 := `FFL.FirstOrder.Arithmetic.Bootstrapping.TermSubst.construction._proof_8
  let proof9 := `FFL.FirstOrder.Arithmetic.Bootstrapping.TermSubst.construction._proof_9
  let proof12 := `FFL.FirstOrder.Arithmetic.Bootstrapping.TermSubst.construction._proof_12
  let construction := `FFL.FirstOrder.Arithmetic.Bootstrapping.TermSubst.construction
  let closure7 ← getClosure env [proof7]
  let closure2 ← getClosure env [proof2]
  let closureBoth ← getClosure env [proof7, proof2]
  let closure8 ← getClosure env [proof8]
  let closure9 ← getClosure env [proof9]
  let closure12 ← getClosure env [proof12]
  let closureConstruction ← getClosure env [construction]
  logInfo m!"SUMMARY\tproof7={closure7.size}\tproof2={closure2.size}\tboth={closureBoth.size}\tconstruction={closureConstruction.size}"
  logInfo m!"RELATION\tproof2_contains_proof7={closure2.contains proof7}\tproof7_contains_proof2={closure7.contains proof2}"
  logInfo m!"FIELD_PATH\tproof8_contains_proof2={closure8.contains proof2}\tproof9_contains_proof2={closure9.contains proof2}\tproof12_contains_proof2={closure12.contains proof2}"
  logInfo m!"AXIOMS_PROOF7\t{axioms env closure7}"
  logInfo m!"AXIOMS_PROOF2\t{axioms env closure2}"
  logInfo m!"AXIOMS_CONSTRUCTION\t{axioms env closureConstruction}"

end FailureOfComposition.Palomar.TermSubstBoundaryAudit

