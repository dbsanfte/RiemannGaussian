import RiemannGaussian
import RiemannGaussian.SemiprimeHermiteWidthPolynomial
import RiemannGaussian.SemiprimeHermiteReportStagePolynomial
import RiemannGaussian.SemiprimeHermiteReportEnvelope
import RiemannGaussian.SemiprimePublicHermiteCounterBudget
import RiemannGaussian.SemiprimePublicHermiteReportPolynomial
import RiemannGaussian.SemiprimePublicResourceRate
import RiemannGaussian.SemiprimeHermiteFullReportRate
import RiemannGaussian.SemiprimeSourceScorePrefixHeight
import Lean.Util.CollectAxioms
import Mathlib.Tactic.Linter
open Lean Elab Command
#lint+ in RiemannGaussian.SemiprimeHermiteWidthPolynomial
#lint+ in RiemannGaussian.SemiprimeHermiteReportStagePolynomial
#lint+ in RiemannGaussian.SemiprimeHermiteReportEnvelope
#lint+ in RiemannGaussian.SemiprimePublicHermiteCounterBudget
#lint+ in RiemannGaussian.SemiprimePublicHermiteReportPolynomial
#lint+ in RiemannGaussian.SemiprimePublicResourceRate
#lint+ in RiemannGaussian.SemiprimeHermiteFullReportRate
#lint+ in RiemannGaussian.SemiprimeSourceScorePrefixHeight
run_cmd do
  let env ← getEnv
  let expected : List Name := [`RiemannGaussian.SemiprimeHermiteWidthPolynomial, `RiemannGaussian.SemiprimeHermiteReportStagePolynomial, `RiemannGaussian.SemiprimeHermiteReportEnvelope, `RiemannGaussian.SemiprimePublicHermiteCounterBudget, `RiemannGaussian.SemiprimePublicHermiteReportPolynomial, `RiemannGaussian.SemiprimePublicResourceRate, `RiemannGaussian.SemiprimeHermiteFullReportRate, `RiemannGaussian.SemiprimeSourceScorePrefixHeight]
  let mut checked : Nat := 0
  let mut totalDeclarations : Nat := 0
  let mut totalTheorems : Nat := 0
  for h : i in [0:env.header.moduleNames.size] do
    let moduleName := env.header.moduleNames[i]
    unless moduleName ∈ expected do continue
    let mut declarations : Nat := 0
    let mut theorems : Nat := 0
    for ci in env.header.moduleData[i]!.constants do
      declarations := declarations+1
      if ci.isAxiom then throwError "project-defined axiom: {ci.name}"
      if ci.isTheorem then theorems := theorems+1
      for ax in (← Lean.collectAxioms ci.name) do
        unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
          throwError "unexpected transitive axiom in {ci.name}: {ax}"
    checked := checked+1
    totalDeclarations := totalDeclarations+declarations
    totalTheorems := totalTheorems+theorems
    logInfo m!"AUDIT {moduleName}: declarations={declarations}, theorems={theorems}, standard_axioms_only=true"
  unless checked == expected.length do throwError "missing module: {checked}/{expected.length}"
  logInfo m!"TOTAL modules={checked}, declarations={totalDeclarations}, theorems={totalTheorems}, standard_axioms_only=true"
  liftIO <| IO.FS.writeFile "/tmp/semiprime-hermite-report-rate-20261027/compiler-imports.json" (Lean.Json.arr (env.header.moduleNames.map (fun n => Lean.Json.str n.toString))).pretty
