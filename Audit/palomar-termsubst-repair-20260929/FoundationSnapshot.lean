import Foundation.FirstOrder.Arithmetic.Bootstrapping.Syntax.Term.Functions
import Lean

set_option autoImplicit false

open Lean Elab Command

namespace FailureOfComposition.Palomar.TermSubstFoundationSnapshot

private partial def canonicalBinders : Expr → Expr
  | .app f a => .app (canonicalBinders f) (canonicalBinders a)
  | .lam _ type body binderInfo =>
    .lam .anonymous (canonicalBinders type) (canonicalBinders body) binderInfo
  | .forallE _ type body binderInfo =>
    .forallE .anonymous (canonicalBinders type) (canonicalBinders body) binderInfo
  | .letE _ type value body nondep =>
    .letE .anonymous (canonicalBinders type) (canonicalBinders value)
      (canonicalBinders body) nondep
  | .mdata data body => .mdata data (canonicalBinders body)
  | .proj name index body => .proj name index (canonicalBinders body)
  | expr => expr

private def normalized (info : ConstantInfo) (expr : Expr) : Expr :=
  let levels := (List.range info.levelParams.length).map fun index =>
    Level.param (Name.num `_termsubst_snapshot_universe index)
  canonicalBinders (expr.instantiateLevelParams info.levelParams levels)

private def escapedRepr (expr : Expr) : String :=
  (reprStr expr).replace "\n" "\\n"

private def emit (env : Environment) (label : String) (name : Name)
    (includeBody : Bool := false) : CommandElabM Unit := do
  let some info := env.checked.get.find? name
    | throwError m!"missing declaration: {name}"
  logInfo s!"SNAPSHOT\t{label}\tNAME\t{name}"
  logInfo s!"SNAPSHOT\t{label}\tLEVELS\t{info.levelParams.length}"
  logInfo s!"SNAPSHOT\t{label}\tTYPE\t{escapedRepr (normalized info info.type)}"
  if includeBody then
    let some body := info.value? (allowOpaque := true)
      | throwError m!"declaration has no body: {name}"
    logInfo s!"SNAPSHOT\t{label}\tBODY\t{escapedRepr (normalized info body)}"

private partial def stripBinders : Expr → Expr
  | .lam _ _ body _ => stripBinders body
  | .letE _ _ value body _ => stripBinders (body.instantiate1 value)
  | .mdata _ body => stripBinders body
  | expr => expr

private def emitConstructionArgs (env : Environment) : CommandElabM Unit := do
  let name := `FFL.FirstOrder.Arithmetic.Bootstrapping.TermSubst.construction
  let some info := env.checked.get.find? name
    | throwError "missing construction"
  let some body := info.value? (allowOpaque := true)
    | throwError "construction has no body"
  let core := stripBinders (normalized info body)
  let fn := core.getAppFn
  let args := core.getAppArgs
  logInfo s!"CONSTRUCTION_HEAD\t{escapedRepr fn}"
  logInfo s!"CONSTRUCTION_ARG_COUNT\t{args.size}"
  let mut index := 0
  for arg in args do
    logInfo s!"CONSTRUCTION_ARG\t{index}\t{escapedRepr arg}"
    index := index + 1

run_cmd do
  let env ← getEnv
  emit env "blueprint" `FFL.FirstOrder.Arithmetic.Bootstrapping.TermSubst.blueprint true
  emit env "construction" `FFL.FirstOrder.Arithmetic.Bootstrapping.TermSubst.construction false
  emitConstructionArgs env
  let original :=
    `FFL.FirstOrder.Arithmetic.Bootstrapping.TermSubst.construction._proof_2
  if (env.checked.get.find? original).isSome then
    emit env "generated_proof_2" original true
  let replacement :=
    `FFL.FirstOrder.Arithmetic.Bootstrapping.TermSubst.constructionBvarDefinedExact
  if (env.checked.get.find? replacement).isSome then
    emit env "replacement_exact" replacement true
    emit env "replacement_field"
      `FFL.FirstOrder.Arithmetic.Bootstrapping.TermSubst.constructionBvarDefined true
    emit env "replacement_assignment"
      `FFL.FirstOrder.Arithmetic.Bootstrapping.TermSubst.constructionBvarAssignment true
    emit env "replacement_terms_val"
      `FFL.FirstOrder.Arithmetic.Bootstrapping.TermSubst.constructionBvarTerms_val true
    emit env "replacement_substitution_eval"
      `FFL.FirstOrder.Arithmetic.Bootstrapping.TermSubst.constructionBvarSubstitution_eval true
    emit env "replacement_result"
      `FFL.FirstOrder.Arithmetic.Bootstrapping.TermSubst.constructionBvarResult true
  let generatedPairs :=
    if (env.checked.get.find? replacement).isSome then
      [
        ("computational_bvar_index_proof",
          `FFL.FirstOrder.Arithmetic.Bootstrapping.TermSubst.construction._proof_4),
        ("fvar_defined_proof",
          `FFL.FirstOrder.Arithmetic.Bootstrapping.TermSubst.construction._proof_7),
        ("func_defined_proof",
          `FFL.FirstOrder.Arithmetic.Bootstrapping.TermSubst.construction._proof_10)
      ]
    else
      [
        ("computational_bvar_index_proof",
          `FFL.FirstOrder.Arithmetic.Bootstrapping.TermSubst.construction._proof_5),
        ("fvar_defined_proof",
          `FFL.FirstOrder.Arithmetic.Bootstrapping.TermSubst.construction._proof_9),
        ("func_defined_proof",
          `FFL.FirstOrder.Arithmetic.Bootstrapping.TermSubst.construction._proof_12)
      ]
  for (label, name) in generatedPairs do
    emit env label name true

end FailureOfComposition.Palomar.TermSubstFoundationSnapshot
