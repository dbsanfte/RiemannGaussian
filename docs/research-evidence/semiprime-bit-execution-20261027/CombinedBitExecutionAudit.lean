import RiemannGaussian
import RiemannGaussian.SemiprimeJetBits
import RiemannGaussian.SemiprimePolynomialCodeBits
import RiemannGaussian.SemiprimeLocalBits
import RiemannGaussian.SemiprimeLocalBitsCorrectness
import RiemannGaussian.SemiprimeLocalBitsBounds
import RiemannGaussian.SemiprimeMeasurementBits
import RiemannGaussian.SemiprimeSupportRate
import RiemannGaussian.SemiprimeScheduledSupportRate
import RiemannGaussian.SemiprimeAcquiredPrefixSearch
import RiemannGaussian.SemiprimePublicAcquiredExecution
import RiemannGaussian.SemiprimeScheduledFactorExecution
import Lean.Util.CollectAxioms
import Mathlib.Tactic.Linter
open Lean Elab Command
#lint+ in RiemannGaussian.SemiprimeJetBits
#lint+ in RiemannGaussian.SemiprimePolynomialCodeBits
#lint+ in RiemannGaussian.SemiprimeLocalBits
#lint+ in RiemannGaussian.SemiprimeLocalBitsCorrectness
#lint+ in RiemannGaussian.SemiprimeLocalBitsBounds
#lint+ in RiemannGaussian.SemiprimeMeasurementBits
#lint+ in RiemannGaussian.SemiprimeSupportRate
#lint+ in RiemannGaussian.SemiprimeScheduledSupportRate
#lint+ in RiemannGaussian.SemiprimeAcquiredPrefixSearch
#lint+ in RiemannGaussian.SemiprimePublicAcquiredExecution
#lint+ in RiemannGaussian.SemiprimeScheduledFactorExecution
run_cmd do
  let env ← getEnv
  let expected : List Name := [`RiemannGaussian.SemiprimeJetBits, `RiemannGaussian.SemiprimePolynomialCodeBits, `RiemannGaussian.SemiprimeLocalBits, `RiemannGaussian.SemiprimeLocalBitsCorrectness, `RiemannGaussian.SemiprimeLocalBitsBounds, `RiemannGaussian.SemiprimeMeasurementBits, `RiemannGaussian.SemiprimeSupportRate, `RiemannGaussian.SemiprimeScheduledSupportRate, `RiemannGaussian.SemiprimeAcquiredPrefixSearch, `RiemannGaussian.SemiprimePublicAcquiredExecution, `RiemannGaussian.SemiprimeScheduledFactorExecution]
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
