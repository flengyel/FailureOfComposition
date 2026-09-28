import Foundation.FirstOrder.Arithmetic.Bootstrapping.Syntax.Term.Basic
import Lean

set_option autoImplicit false

open Lean Elab Command

namespace FailureOfComposition.Palomar.BaselineFoundationSnapshot

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
    Level.param (Name.num `_foundation_snapshot_universe index)
  canonicalBinders (expr.instantiateLevelParams info.levelParams levels)

private def emit (env : Environment) (label : String) (name : Name)
    (includeBody : Bool := false) : CommandElabM Unit := do
  let some info := env.checked.get.find? name
    | throwError m!"missing declaration: {name}"
  let typeText := (reprStr (normalized info info.type)).replace "\n" "\\n"
  logInfo s!"SNAPSHOT\t{label}\tTYPE\t{typeText}"
  if includeBody then
    let some body := info.value? (allowOpaque := true)
      | throwError m!"declaration has no body: {name}"
    let bodyText := (reprStr (normalized info body)).replace "\n" "\\n"
    logInfo s!"SNAPSHOT\t{label}\tBODY\t{bodyText}"

run_cmd do
  let env ← getEnv
  emit env "blueprint" `FFL.FirstOrder.Arithmetic.Bootstrapping.IsUTerm.BV.blueprint true
  emit env "construction" `FFL.FirstOrder.Arithmetic.Bootstrapping.IsUTerm.BV.construction
  emit env "func_obligation" `FFL.FirstOrder.Arithmetic.Bootstrapping.IsUTerm.BV.construction._proof_4

end FailureOfComposition.Palomar.BaselineFoundationSnapshot
