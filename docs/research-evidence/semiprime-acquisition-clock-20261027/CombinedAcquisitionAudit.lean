import RiemannGaussian
import RiemannGaussian.SemiprimePaidConstraintCache
import RiemannGaussian.SemiprimePaidConstraintRows
import RiemannGaussian.SemiprimePaidPackingSnapshot
import RiemannGaussian.SemiprimePaidConstraintAcquisition
import RiemannGaussian.SemiprimePaidOriginalConstraints
import RiemannGaussian.SemiprimePaidFiniteEnumerationLists
import RiemannGaussian.SemiprimePaidFiniteEnumerations
import RiemannGaussian.SemiprimePaidEnumeratedSource
import RiemannGaussian.SemiprimePaidEnumeratedConstraints
import RiemannGaussian.SemiprimeRowSelectionBitArithmetic
import RiemannGaussian.SemiprimeRowSelectionBits
import RiemannGaussian.SemiprimePaidPrefixController
import RiemannGaussian.SemiprimePaidFactorDecoder
import RiemannGaussian.SemiprimePaidPublicController
import RiemannGaussian.SemiprimePaidScheduledController
import Lean.Util.CollectAxioms
import Mathlib.Tactic.Linter
open Lean Elab Command
#lint+ in RiemannGaussian.SemiprimePaidConstraintCache
#lint+ in RiemannGaussian.SemiprimePaidConstraintRows
#lint+ in RiemannGaussian.SemiprimePaidPackingSnapshot
#lint+ in RiemannGaussian.SemiprimePaidConstraintAcquisition
#lint+ in RiemannGaussian.SemiprimePaidOriginalConstraints
#lint+ in RiemannGaussian.SemiprimePaidFiniteEnumerationLists
#lint+ in RiemannGaussian.SemiprimePaidFiniteEnumerations
#lint+ in RiemannGaussian.SemiprimePaidEnumeratedSource
#lint+ in RiemannGaussian.SemiprimePaidEnumeratedConstraints
#lint+ in RiemannGaussian.SemiprimeRowSelectionBitArithmetic
#lint+ in RiemannGaussian.SemiprimeRowSelectionBits
#lint+ in RiemannGaussian.SemiprimePaidPrefixController
#lint+ in RiemannGaussian.SemiprimePaidFactorDecoder
#lint+ in RiemannGaussian.SemiprimePaidPublicController
#lint+ in RiemannGaussian.SemiprimePaidScheduledController
run_cmd do
  let env ← getEnv
  let expected : List Name := [`RiemannGaussian.SemiprimePaidConstraintCache, `RiemannGaussian.SemiprimePaidConstraintRows, `RiemannGaussian.SemiprimePaidPackingSnapshot, `RiemannGaussian.SemiprimePaidConstraintAcquisition, `RiemannGaussian.SemiprimePaidOriginalConstraints, `RiemannGaussian.SemiprimePaidFiniteEnumerationLists, `RiemannGaussian.SemiprimePaidFiniteEnumerations, `RiemannGaussian.SemiprimePaidEnumeratedSource, `RiemannGaussian.SemiprimePaidEnumeratedConstraints, `RiemannGaussian.SemiprimeRowSelectionBitArithmetic, `RiemannGaussian.SemiprimeRowSelectionBits, `RiemannGaussian.SemiprimePaidPrefixController, `RiemannGaussian.SemiprimePaidFactorDecoder, `RiemannGaussian.SemiprimePaidPublicController, `RiemannGaussian.SemiprimePaidScheduledController]
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
  liftIO <| IO.FS.writeFile "/tmp/semiprime-acquisition-clock-20261027/compiler-imports.json" (Lean.Json.arr (env.header.moduleNames.map (fun n => Lean.Json.str n.toString))).pretty
