import RiemannGaussian.SemiprimeSparseBlockPeriodObstruction
import Lean.Util.CollectAxioms
import Mathlib.Tactic.Linter

/-! Focused native leaf lint and axiom audit by module provenance. -/

open Lean Elab Command

#lint+ in RiemannGaussian.SemiprimeSparseBlockPeriodObstruction

run_cmd do
  let env ← getEnv
  let mut imported : Array Name := #[]
  for h : i in [0:env.header.moduleNames.size] do
    unless env.header.moduleNames[i] ==
        `RiemannGaussian.SemiprimeSparseBlockPeriodObstruction do continue
    for ci in env.header.moduleData[i]!.constants do
      imported := imported.push ci.name
  unless imported.size > 0 do throwError "no sparse-block proof module found"
  let mut declarations : Nat := 0
  let mut theorems : Nat := 0
  let mut localHelpers : Nat := 0
  let mut reports : Array Json := #[]
  for (n,ci) in env.constants.toList do
    if env.isImportedConst n && !imported.contains n then continue
    declarations := declarations+1
    if !env.isImportedConst n then localHelpers := localHelpers+1
    if ci.isAxiom then throwError "project-defined axiom: {n}"
    if ci.isTheorem then theorems := theorems+1
    let axs ← Lean.collectAxioms n
    for ax in axs do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "unexpected transitive axiom in {n}: {ax}"
    reports := reports.push (Json.mkObj [("declaration",toJson n.toString),
      ("isTheorem",toJson ci.isTheorem),("axioms",toJson (axs.map Name.toString)),
      ("checkerLocal",toJson (!env.isImportedConst n))])
  unless theorems > 0 do throwError "no sparse-block obstruction theorem checked"
  logInfo m!"Checked {declarations} declarations, {theorems} theorems, {localHelpers} checker-local helpers; only standard axioms."
  IO.FS.createDirAll "/tmp/semiprime-openai-math-20261007"
  IO.FS.writeFile "/tmp/semiprime-openai-math-20261007/sparse-block-axioms.json"
    (Json.mkObj [("declarations",toJson declarations),
      ("theoremsIncludingGeneratedHelpers",toJson theorems),
      ("importedLeafDeclarations",toJson imported.size),
      ("checkerLocalHelpers",toJson localHelpers),
      ("moduleProvenanceSelection",toJson true),
      ("onlyStandardAxioms",toJson true),
      ("declarationAxioms",Json.arr reports)]).pretty
