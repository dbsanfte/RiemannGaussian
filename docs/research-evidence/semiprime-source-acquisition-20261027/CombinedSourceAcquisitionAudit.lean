import RiemannGaussian
import RiemannGaussian.SemiprimeBinomialExecution
import RiemannGaussian.SemiprimeBinomialExecutionBounds
import RiemannGaussian.SemiprimeBinomialExecutionTracked
import RiemannGaussian.SemiprimeBlockArrayExecution
import RiemannGaussian.SemiprimeLocalExecutionHeight
import RiemannGaussian.SemiprimeLocalExecutionBitBounds
import RiemannGaussian.SemiprimePaddedBlockExecution
import RiemannGaussian.SemiprimePaddedBlockCoverage
import RiemannGaussian.SemiprimePaddedConstraintSpan
import RiemannGaussian.SemiprimeRuntimeDesignAcquisition
import RiemannGaussian.SemiprimeSourceCodeArrays
import RiemannGaussian.SemiprimeUniversalNumeratorExecution
import RiemannGaussian.SemiprimeSourceInterpolationExecution
import RiemannGaussian.SemiprimeUniversalSourceExecution
import RiemannGaussian.SemiprimeUniversalConstraintPadding
import RiemannGaussian.SemiprimeSourceArrayAcquisition
import RiemannGaussian.SemiprimeSourceExpressionBound
import RiemannGaussian.SemiprimeSourceConstraintAcquisition
import RiemannGaussian.SemiprimeSourceRuntimeDesignBridge
import RiemannGaussian.SemiprimeAcquiredSourceCounter
import Lean.Util.CollectAxioms
import Mathlib.Tactic.Linter
open Lean Elab Command
#lint+ in RiemannGaussian.SemiprimeBinomialExecution
#lint+ in RiemannGaussian.SemiprimeBinomialExecutionBounds
#lint+ in RiemannGaussian.SemiprimeBinomialExecutionTracked
#lint+ in RiemannGaussian.SemiprimeBlockArrayExecution
#lint+ in RiemannGaussian.SemiprimeLocalExecutionHeight
#lint+ in RiemannGaussian.SemiprimeLocalExecutionBitBounds
#lint+ in RiemannGaussian.SemiprimePaddedBlockExecution
#lint+ in RiemannGaussian.SemiprimePaddedBlockCoverage
#lint+ in RiemannGaussian.SemiprimePaddedConstraintSpan
#lint+ in RiemannGaussian.SemiprimeRuntimeDesignAcquisition
#lint+ in RiemannGaussian.SemiprimeSourceCodeArrays
#lint+ in RiemannGaussian.SemiprimeUniversalNumeratorExecution
#lint+ in RiemannGaussian.SemiprimeSourceInterpolationExecution
#lint+ in RiemannGaussian.SemiprimeUniversalSourceExecution
#lint+ in RiemannGaussian.SemiprimeUniversalConstraintPadding
#lint+ in RiemannGaussian.SemiprimeSourceArrayAcquisition
#lint+ in RiemannGaussian.SemiprimeSourceExpressionBound
#lint+ in RiemannGaussian.SemiprimeSourceConstraintAcquisition
#lint+ in RiemannGaussian.SemiprimeSourceRuntimeDesignBridge
#lint+ in RiemannGaussian.SemiprimeAcquiredSourceCounter
run_cmd do
  let env ← getEnv
  let expected : List Name := [`RiemannGaussian.SemiprimeBinomialExecution, `RiemannGaussian.SemiprimeBinomialExecutionBounds, `RiemannGaussian.SemiprimeBinomialExecutionTracked, `RiemannGaussian.SemiprimeBlockArrayExecution, `RiemannGaussian.SemiprimeLocalExecutionHeight, `RiemannGaussian.SemiprimeLocalExecutionBitBounds, `RiemannGaussian.SemiprimePaddedBlockExecution, `RiemannGaussian.SemiprimePaddedBlockCoverage, `RiemannGaussian.SemiprimePaddedConstraintSpan, `RiemannGaussian.SemiprimeRuntimeDesignAcquisition, `RiemannGaussian.SemiprimeSourceCodeArrays, `RiemannGaussian.SemiprimeUniversalNumeratorExecution, `RiemannGaussian.SemiprimeSourceInterpolationExecution, `RiemannGaussian.SemiprimeUniversalSourceExecution, `RiemannGaussian.SemiprimeUniversalConstraintPadding, `RiemannGaussian.SemiprimeSourceArrayAcquisition, `RiemannGaussian.SemiprimeSourceExpressionBound, `RiemannGaussian.SemiprimeSourceConstraintAcquisition, `RiemannGaussian.SemiprimeSourceRuntimeDesignBridge, `RiemannGaussian.SemiprimeAcquiredSourceCounter]
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
