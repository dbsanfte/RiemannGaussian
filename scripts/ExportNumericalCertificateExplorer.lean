import NumericalCertificate
import Lean.Util.CollectAxioms
import Lean.Util.FoldConsts

/-!
# Optional compiled proof graph for the literal 67.31 percent certificate

Run only after the separate NumericalCertificate target has been verified.
This reads its cached compiled environment; it is not part of ordinary CI.
Authored proof dependencies, statements, exact source ranges and transitive
axioms come from Lean. Generated data declarations are explicitly marked
as proof boundaries, with their full transitive axioms still checked.
The complete certificate audit remains the authority for every generated
range, anchor and cover group. Presentation checks validate the frozen
snapshot against the unchanged optional proof-input fingerprint.
-/

open Lean Elab Command

private def moduleOf? (env : Environment) (n : Name) : Option Name := do
  let i ← env.getModuleIdxFor? n
  env.header.moduleNames[i.toNat]?

private def isProject (env : Environment) (n : Name) : Bool :=
  (moduleOf? env n).any (`RiemannGaussian).isPrefixOf

private def namesJson (names : Array Name) : Json :=
  toJson ((names.qsort Name.lt).map Name.toString)

private def kind (ci : ConstantInfo) : String :=
  match ci with
  | .thmInfo _ => "theorem"
  | .defnInfo _ => "definition"
  | .opaqueInfo _ => "opaque"
  | .axiomInfo _ => "axiom"
  | .inductInfo _ => "inductive"
  | .ctorInfo _ => "constructor"
  | .recInfo _ => "recursor"
  | .quotInfo _ => "quotient"

private def standardAxiom (n : Name) : Bool :=
  n == ``propext || n == ``Classical.choice || n == ``Quot.sound

run_cmd do
  let metadata ← IO.FS.readFile "docs/numerical-certificate-explorer/metadata.json"
  let metadata ← ofExcept (Json.parse metadata)
  let status := metadata
  let endpoints ← ofExcept (metadata.getObjValAs? (Array Json) "endpoints")
  let env ← getEnv
  -- Inlined private match equations may be emitted in a different module
  -- from the source definition. Resolve their original private declaration
  -- through Lean's names and ranges, never by guessing a line number.
  let mut sourceAliases : NameMap (Array Name) := {}
  for h : moduleIndex in [0:env.header.moduleNames.size] do
    unless (`RiemannGaussian).isPrefixOf env.header.moduleNames[moduleIndex] do continue
    for ci in env.header.moduleData[moduleIndex]!.constants do
      let key := privateToUserName ci.name
      sourceAliases := sourceAliases.insert key ((sourceAliases.find? key).getD #[] |>.push ci.name)
  let mut roots : Array Name := #[]
  let mut rootJson : Array Json := #[]
  for endpoint in endpoints do
    let id ← ofExcept (endpoint.getObjValAs? String "id")
    let paths ← ofExcept (endpoint.getObjValAs? (Array (Array String)) "statusPaths")
    let mut endpointNames : Array Name := #[]
    for path in paths do
      let mut entry := status
      for key in path do
        entry ← ofExcept (entry.getObjVal? key)
      let name := (← ofExcept entry.getStr?).toName
      let some ci := env.find? name | throwError "unknown graph endpoint: {name}"
      unless ci.isTheorem && isProject env name do
        throwError "graph endpoint is not a project theorem: {name}"
      roots := roots.push name
      endpointNames := endpointNames.push name
    rootJson := rootJson.push (Json.mkObj [("id", toJson id),
      ("theorems", namesJson endpointNames)])
  let mut pending := roots
  let mut seen : NameSet := {}
  let mut entries : Array (Name × Json) := #[]
  while !pending.isEmpty do
    let name := pending.back!
    pending := pending.pop
    if seen.contains name then continue
    seen := seen.insert name
    let some ci := env.find? name | throwError "missing dependency: {name}"
    let project := isProject env name
    let dataBoundary := (moduleOf? env name).any (`RiemannGaussian.CertificateData).isPrefixOf
    let proofRefs := if project && !dataBoundary then
      (ci.value? (allowOpaque := true)).map Expr.getUsedConstants |>.getD #[]
      else #[]
    let typeRefs := if project && !dataBoundary then ci.type.getUsedConstants else #[]
    let ctorRefs := if project && !dataBoundary then match ci with
      | .inductInfo v => v.ctors.toArray
      | _ => #[]
      else #[]
    pending := pending ++ proofRefs ++ typeRefs ++ ctorRefs
    let axioms ← Lean.collectAxioms name
    unless axioms.all standardAxiom do
      throwError "nonstandard transitive axioms in graph: {name}: {axioms}"
    if project && ci.isAxiom then throwError "project axiom in graph: {name}"
    let mut sourceName := name
    let mut ranges ← findDeclarationRanges? name
    if let some structInfo := getStructureInfo? env name.getPrefix then
      if structInfo.parentInfo.any (fun parent => parent.projFn == name) then
        if let some r ← findDeclarationRanges? name.getPrefix then
          sourceName := name.getPrefix
          ranges := some r
    -- Generated induction helpers and implicit structure constructors inherit
    -- the inductive declaration's range; report that enclosing source honestly.
    if let some (.inductInfo _) := env.find? name.getPrefix then
      if let some parentRange ← findDeclarationRanges? name.getPrefix then
        if ranges.any (fun r => r.selectionRange.pos.line == parentRange.selectionRange.pos.line &&
            r.selectionRange.pos.column == parentRange.selectionRange.pos.column) then
          sourceName := name.getPrefix
          ranges := some parentRange
    while ranges.isNone && !sourceName.isAnonymous do
      sourceName := sourceName.getPrefix
      ranges ← findDeclarationRanges? sourceName
    if ranges.isNone then
      sourceName := privateToUserName name
      ranges ← findDeclarationRanges? sourceName
      while ranges.isNone && !sourceName.isAnonymous do
        sourceName := sourceName.getPrefix
        ranges ← findDeclarationRanges? sourceName
    if ranges.isNone then
      let mut candidate := privateToUserName name
      while ranges.isNone && !candidate.isAnonymous do
        for sourceAlias in (sourceAliases.find? candidate).getD #[] do
          if let some r ← findDeclarationRanges? sourceAlias then
            ranges := some r
            sourceName := sourceAlias
            break
        candidate := candidate.getPrefix
    let location := match ranges with
      | some r => Json.mkObj [("line", toJson r.selectionRange.pos.line),
          ("column", toJson r.selectionRange.pos.column),
          ("endLine", toJson r.range.endPos.line),
          ("declaration", toJson sourceName.toString),
          ("module", toJson ((moduleOf? env sourceName).map Name.toString)),
          ("exact", toJson (sourceName == name))]
      | none => Json.null
    let typeText ← liftTermElabM do
      return (← Meta.ppExpr ci.type).pretty 110
    let doc ← findDocString? env name
    entries := entries.push (name, Json.mkObj [
      ("id", toJson name.toString),
      ("displayName", toJson (privateToUserName name).toString),
      ("module", toJson ((moduleOf? env name).map Name.toString)),
      ("kind", toJson (kind ci)), ("project", toJson project),
      ("verifiedDataBoundary", toJson dataBoundary),
      ("location", location), ("statement", toJson typeText),
      ("doc", toJson (doc.getD "")), ("axioms", namesJson axioms),
      ("bodyDependencies", namesJson proofRefs),
      ("typeDependencies", namesJson typeRefs),
      ("constructorDependencies", namesJson ctorRefs)])
  let output := Json.mkObj [
    ("schemaVersion", toJson (1 : Nat)), ("leanVersion", toJson Lean.versionString),
    ("generator", toJson "scripts/ExportNumericalCertificateExplorer.lean"),
    ("edgeMeaning", toJson "Constants referenced in elaborated bodies and types; not a claim of logical equivalence or minimal necessity."),
    ("externalBoundary", toJson "Authored project dependencies are followed transitively. Generated CertificateData declarations and external libraries are explicit boundary leaves; their COMPLETE transitive axioms are audited. The optional full certificate audit checks the entire generated proof closure."),
    ("endpoints", toJson rootJson),
    ("nodes", toJson ((entries.qsort (fun a b => Name.lt a.1 b.1)).map Prod.snd))]
  IO.FS.createDirAll ".lake/numerical-certificate-explorer"
  IO.FS.writeFile ".lake/numerical-certificate-explorer/lean-graph.json" (output.compress ++ "\n")
  logInfo m!"Exported {entries.size} declarations from {roots.size} endpoints."
