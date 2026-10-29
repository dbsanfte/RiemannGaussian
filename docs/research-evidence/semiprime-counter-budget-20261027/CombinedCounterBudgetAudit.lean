import RiemannGaussian
import RiemannGaussian.SemiprimeFullSetupBudget
import RiemannGaussian.SemiprimeNativeCounterBudget
import RiemannGaussian.SemiprimeIndexedDesignResources
import RiemannGaussian.SemiprimePublicBudgetDimensions
import RiemannGaussian.SemiprimeFullCounterBudget
import RiemannGaussian.SemiprimePublicCounterBudget
import RiemannGaussian.SemiprimeSetupPolynomialEnvelope
import RiemannGaussian.SemiprimePublicReportPolynomial
import RiemannGaussian.SemiprimePublicCounterResources
import RiemannGaussian.SemiprimeReportPolynomialGrowth
import RiemannGaussian.SemiprimeScheduledScalarBudget
import RiemannGaussian.SemiprimePublicReportGrowth
import RiemannGaussian.SemiprimeFullReportRate
import Lean.Util.CollectAxioms
import Mathlib.Tactic.Linter
open Lean Elab Command
#lint+ in RiemannGaussian.SemiprimeFullSetupBudget
#lint+ in RiemannGaussian.SemiprimeNativeCounterBudget
#lint+ in RiemannGaussian.SemiprimeIndexedDesignResources
#lint+ in RiemannGaussian.SemiprimePublicBudgetDimensions
#lint+ in RiemannGaussian.SemiprimeFullCounterBudget
#lint+ in RiemannGaussian.SemiprimePublicCounterBudget
#lint+ in RiemannGaussian.SemiprimeSetupPolynomialEnvelope
#lint+ in RiemannGaussian.SemiprimePublicReportPolynomial
#lint+ in RiemannGaussian.SemiprimePublicCounterResources
#lint+ in RiemannGaussian.SemiprimeReportPolynomialGrowth
#lint+ in RiemannGaussian.SemiprimeScheduledScalarBudget
#lint+ in RiemannGaussian.SemiprimePublicReportGrowth
#lint+ in RiemannGaussian.SemiprimeFullReportRate
run_cmd do
  let env ← getEnv
  let expected : List Name := [`RiemannGaussian.SemiprimeFullSetupBudget, `RiemannGaussian.SemiprimeNativeCounterBudget, `RiemannGaussian.SemiprimeIndexedDesignResources, `RiemannGaussian.SemiprimePublicBudgetDimensions, `RiemannGaussian.SemiprimeFullCounterBudget, `RiemannGaussian.SemiprimePublicCounterBudget, `RiemannGaussian.SemiprimeSetupPolynomialEnvelope, `RiemannGaussian.SemiprimePublicReportPolynomial, `RiemannGaussian.SemiprimePublicCounterResources, `RiemannGaussian.SemiprimeReportPolynomialGrowth, `RiemannGaussian.SemiprimeScheduledScalarBudget, `RiemannGaussian.SemiprimePublicReportGrowth, `RiemannGaussian.SemiprimeFullReportRate]
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
  liftIO <| IO.FS.writeFile "/tmp/semiprime-counter-budget-20261027/compiler-imports.json" (Lean.Json.arr (env.header.moduleNames.map (fun n => Lean.Json.str n.toString))).pretty
