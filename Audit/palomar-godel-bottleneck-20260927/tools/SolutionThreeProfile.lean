import FailureOfComposition.Palomar.SolutionThree
import Lean
import Lean.Meta.Sym.ExprPtr

set_option autoImplicit false

open Lean Elab Command

namespace FailureOfComposition.Palomar.GodelBottleneckProfile

private abbrev PhysicalSet := Std.HashSet Lean.Meta.Sym.ExprPtr
private abbrev StructuralSet := Std.HashSet Expr

private structure Metric where
  name : Name
  physicalType : Nat
  structuralType : Nat
  physicalBody : Nat
  structuralBody : Nat

private def declarationTypeBody
    (env : Environment) (name : Name) : Option (Expr × Option Expr) := do
  let info ← env.checked.get.find? name
  return (info.type, info.value? (allowOpaque := true))

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
        | throw s!"Unresolved selected-proof dependency: {name}"
      closure env ((dependencies info).toList ++ rest) (seen.insert name)

private def getClosure (env : Environment) (roots : List Name) : CommandElabM NameSet :=
  match closure env roots with
  | .ok result => pure result
  | .error message => throwError message

/-- Traverse only pointer-distinct nodes. Structural distinctness uses Expr's
cached structural hash and alpha-equivalence. There is deliberately no raw
recursive tree traversal: shared terms are never expanded repeatedly. -/
private unsafe def visitDistinct (expr : Expr)
    (physical : PhysicalSet) (structural : StructuralSet) :
    PhysicalSet × StructuralSet :=
  let pointer : Lean.Meta.Sym.ExprPtr := ⟨expr⟩
  if physical.contains pointer then
    (physical, structural)
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

private unsafe def distinctPair (expressions : Array Expr) : Nat × Nat :=
  let (physical, structural) := expressions.foldl
    (fun (sets : PhysicalSet × StructuralSet) expr =>
      visitDistinct expr sets.1 sets.2) ({}, {})
  (physical.size, structural.size)

private unsafe def metric (env : Environment) (name : Name) : Except String Metric := do
  let some (type, body?) := declarationTypeBody env name
    | throw s!"Missing selected-proof declaration {name}"
  let (physicalType, structuralType) := distinctPair #[type]
  let (physicalBody, structuralBody) :=
    body?.map (fun body => distinctPair #[body]) |>.getD (0, 0)
  return { name, physicalType, structuralType, physicalBody, structuralBody }

private unsafe def profileSet (env : Environment) (label : String)
    (selected : NameSet) : CommandElabM (Array Metric) := do
  let mut perDeclPhysicalType := 0
  let mut perDeclStructuralType := 0
  let mut perDeclPhysicalBody := 0
  let mut perDeclStructuralBody := 0
  let mut globalPhysicalType : PhysicalSet := {}
  let mut globalStructuralType : StructuralSet := {}
  let mut globalPhysicalBody : PhysicalSet := {}
  let mut globalStructuralBody : StructuralSet := {}
  let mut metrics : Array Metric := #[]
  for name in selected.toArray do
    let some (type, body?) := declarationTypeBody env name
      | throwError "Missing selected-proof declaration {name}"
    let item ← match metric env name with
      | .ok result => pure result
      | .error message => throwError message
    metrics := metrics.push item
    perDeclPhysicalType := perDeclPhysicalType + item.physicalType
    perDeclStructuralType := perDeclStructuralType + item.structuralType
    perDeclPhysicalBody := perDeclPhysicalBody + item.physicalBody
    perDeclStructuralBody := perDeclStructuralBody + item.structuralBody
    let typeResult := visitDistinct type globalPhysicalType globalStructuralType
    globalPhysicalType := typeResult.1
    globalStructuralType := typeResult.2
    if let some body := body? then
      let bodyResult := visitDistinct body globalPhysicalBody globalStructuralBody
      globalPhysicalBody := bodyResult.1
      globalStructuralBody := bodyResult.2
  logInfo m!"PROFILE_DEFINITION\tphysical=runtime Expr pointer identities; structural=Expr.eqv alpha-equivalent nodes with cached structural hash; global deduplicates across all declarations in the named closure; perDecl sums separately deduplicated declaration DAGs; types and bodies are separate; no normalization, reduction, or raw recursive traversal"
  logInfo m!"CLOSURE_DAG\tlabel={label}\tdeclarations={selected.size}\tperDeclPhysicalType={perDeclPhysicalType}\tperDeclStructuralType={perDeclStructuralType}\tperDeclPhysicalBody={perDeclPhysicalBody}\tperDeclStructuralBody={perDeclStructuralBody}\tglobalPhysicalType={globalPhysicalType.size}\tglobalStructuralType={globalStructuralType.size}\tglobalPhysicalBody={globalPhysicalBody.size}\tglobalStructuralBody={globalStructuralBody.size}"
  return metrics

private def difference (left right : NameSet) : NameSet :=
  left.toArray.foldl (init := {}) fun result name =>
    if right.contains name then result else result.insert name

private def intersectionSize (left right : NameSet) : Nat :=
  left.toArray.foldl (init := 0) fun result name =>
    if right.contains name then result + 1 else result

private partial def findPathAux (env : Environment) (target : Name)
    (todo : List (Name × List Name)) (seen : NameSet := {}) : Option (List Name) :=
  match todo with
  | [] => none
  | (name, reversedPath) :: rest =>
    if seen.contains name then
      findPathAux env target rest seen
    else if name == target then
      some (name :: reversedPath).reverse
    else
      match env.checked.get.find? name with
      | none => findPathAux env target rest (seen.insert name)
      | some info =>
        let next := dependencies info |>.toList.map fun dep => (dep, name :: reversedPath)
        findPathAux env target (next ++ rest) (seen.insert name)

private def findPath (env : Environment) (root target : Name) : Option (List Name) :=
  findPathAux env target [(root, [])]

private def pathString (path : List Name) : String :=
  String.intercalate " -> " (path.map Name.toString)

private unsafe def printLargest (label : String) (metrics : Array Metric) : CommandElabM Unit := do
  let byPhysical := metrics.qsort fun left right => left.physicalBody > right.physicalBody
  for item in byPhysical[:40] do
    logInfo m!"LARGEST_PHYSICAL_BODY\tlabel={label}\tname={item.name}\tphysicalType={item.physicalType}\tstructuralType={item.structuralType}\tphysicalBody={item.physicalBody}\tstructuralBody={item.structuralBody}"
  let byStructural := metrics.qsort fun left right => left.structuralBody > right.structuralBody
  for item in byStructural[:40] do
    logInfo m!"LARGEST_STRUCTURAL_BODY\tlabel={label}\tname={item.name}\tphysicalType={item.physicalType}\tstructuralType={item.structuralType}\tphysicalBody={item.physicalBody}\tstructuralBody={item.structuralBody}"

run_cmd do
  let env ← getEnv
  let first := ``FailureOfComposition.Palomar.obstruction_four_properties
  let productive := ``FailureOfComposition.Palomar.no_quotient_composition_productive
  let godel := ``FailureOfComposition.Palomar.no_quotient_composition_godel
  let reBridge := ``FailureOfComposition.Palomar.Arithmetic.reAxiomCodes_toFoundation_iff
  let craig := ``FailureOfComposition.CraigPresentation.exists_craig_presentation
  let indexGodel := ``FailureOfComposition.ConcreteIndices.index_noncongruence_via_godel
  let graphGodel := ``FailureOfComposition.graph_noncongruence_via_godel
  let arithmetization := ``FailureOfComposition.ConcreteEvaluator.arithmetization
  let realization := ``FailureOfComposition.SigmaOneRealization.realize_graph
  let two ← getClosure env [first, productive]
  let godelOnly ← getClosure env [godel]
  let three ← getClosure env [first, productive, godel]
  let marginal := difference three two
  let reClosure ← getClosure env [reBridge]
  let craigClosure ← getClosure env [craig]
  let indexClosure ← getClosure env [indexGodel]
  let graphClosure ← getClosure env [graphGodel]
  let arithClosure ← getClosure env [arithmetization]
  let realizationClosure ← getClosure env [realization]

  logInfo m!"SET_RELATIONS\ttwo={two.size}\tgodel={godelOnly.size}\tthree={three.size}\tmarginal={marginal.size}\ttwo_godel_overlap={intersectionSize two godelOnly}"
  logInfo m!"BOUNDARY_RELATIONS\treBridge={reClosure.size}\tcraig={craigClosure.size}\tindexGodel={indexClosure.size}\tgraphGodel={graphClosure.size}\tarithmetization={arithClosure.size}\trealization={realizationClosure.size}\tcraig_index_overlap={intersectionSize craigClosure indexClosure}\tgraph_index_overlap={intersectionSize graphClosure indexClosure}\tarith_index_overlap={intersectionSize arithClosure indexClosure}\trealization_arith_overlap={intersectionSize realizationClosure arithClosure}"

  discard <| profileSet env "first-two-union" two
  discard <| profileSet env "godel-only" godelOnly
  discard <| profileSet env "all-three-union" three
  let marginalMetrics ← profileSet env "three-minus-two-marginal" marginal
  printLargest "three-minus-two-marginal" marginalMetrics
  discard <| profileSet env "reAxiomCodes-toFoundation" reClosure
  discard <| profileSet env "Craig-exists-presentation" craigClosure
  discard <| profileSet env "index-noncongruence-via-godel" indexClosure
  discard <| profileSet env "graph-noncongruence-via-godel" graphClosure
  discard <| profileSet env "concrete-arithmetization" arithClosure
  discard <| profileSet env "sigma-one-realization" realizationClosure

  let pathTargets := #[reBridge, craig, indexGodel, graphGodel, arithmetization, realization]
  for target in pathTargets do
    match findPath env godel target with
    | some path => logInfo m!"DEPENDENCY_PATH\ttarget={target}\tpath={pathString path}"
    | none => logInfo m!"DEPENDENCY_PATH_MISSING\ttarget={target}"
  let largest := marginalMetrics.qsort fun left right => left.physicalBody > right.physicalBody
  for item in largest[:20] do
    match findPath env godel item.name with
    | some path => logInfo m!"HOTSPOT_PATH\ttarget={item.name}\tpath={pathString path}"
    | none => logInfo m!"HOTSPOT_PATH_MISSING\ttarget={item.name}"

end FailureOfComposition.Palomar.GodelBottleneckProfile
