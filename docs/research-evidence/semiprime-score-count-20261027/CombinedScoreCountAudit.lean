import RiemannGaussian
import RiemannGaussian.SemiprimeSourceScoreCounts
import RiemannGaussian.SemiprimeSourceScoreCountsPadding
import RiemannGaussian.SemiprimeSourceScoreCountsObjective
import RiemannGaussian.SemiprimeSourceScoreCountsBounds
import RiemannGaussian.SemiprimeSourceScoreCancellation
import RiemannGaussian.SemiprimeSourceChoiceOrder
import RiemannGaussian.SemiprimeSourceScoreChoice
import RiemannGaussian.SemiprimeSourceScoreCountOrder
import RiemannGaussian.SemiprimeSourceScoreWeightBits
import RiemannGaussian.SemiprimeSourceScoreWeightAcquisition
import RiemannGaussian.SemiprimeSourceScorePredicateBits
import RiemannGaussian.SemiprimeSourceScorePredicateBitsBounds
import RiemannGaussian.SemiprimeSourceScoreCountBitsCore
import RiemannGaussian.SemiprimeSourceScoreCountBits
import RiemannGaussian.SemiprimeSourceScoreCountBitsBudget
import RiemannGaussian.SemiprimeSourceScoreCountBitsBounds
import RiemannGaussian.SemiprimeSourceScorePhysicalSearch
import RiemannGaussian.SemiprimeSourceScorePhysicalCaller
import RiemannGaussian.SemiprimeSourceScorePhysicalBudget
import RiemannGaussian.SemiprimeSourceScorePhysicalResources
import Lean.Util.CollectAxioms
import Mathlib.Tactic.Linter
open Lean Elab Command
#lint+ in RiemannGaussian.SemiprimeSourceScoreCounts
#lint+ in RiemannGaussian.SemiprimeSourceScoreCountsPadding
#lint+ in RiemannGaussian.SemiprimeSourceScoreCountsObjective
#lint+ in RiemannGaussian.SemiprimeSourceScoreCountsBounds
#lint+ in RiemannGaussian.SemiprimeSourceScoreCancellation
#lint+ in RiemannGaussian.SemiprimeSourceChoiceOrder
#lint+ in RiemannGaussian.SemiprimeSourceScoreChoice
#lint+ in RiemannGaussian.SemiprimeSourceScoreCountOrder
#lint+ in RiemannGaussian.SemiprimeSourceScoreWeightBits
#lint+ in RiemannGaussian.SemiprimeSourceScoreWeightAcquisition
#lint+ in RiemannGaussian.SemiprimeSourceScorePredicateBits
#lint+ in RiemannGaussian.SemiprimeSourceScorePredicateBitsBounds
#lint+ in RiemannGaussian.SemiprimeSourceScoreCountBitsCore
#lint+ in RiemannGaussian.SemiprimeSourceScoreCountBits
#lint+ in RiemannGaussian.SemiprimeSourceScoreCountBitsBudget
#lint+ in RiemannGaussian.SemiprimeSourceScoreCountBitsBounds
#lint+ in RiemannGaussian.SemiprimeSourceScorePhysicalSearch
#lint+ in RiemannGaussian.SemiprimeSourceScorePhysicalCaller
#lint+ in RiemannGaussian.SemiprimeSourceScorePhysicalBudget
#lint+ in RiemannGaussian.SemiprimeSourceScorePhysicalResources
run_cmd do
  let env ← getEnv
  let expected : List Name := [`RiemannGaussian.SemiprimeSourceScoreCounts, `RiemannGaussian.SemiprimeSourceScoreCountsPadding, `RiemannGaussian.SemiprimeSourceScoreCountsObjective, `RiemannGaussian.SemiprimeSourceScoreCountsBounds, `RiemannGaussian.SemiprimeSourceScoreCancellation, `RiemannGaussian.SemiprimeSourceChoiceOrder, `RiemannGaussian.SemiprimeSourceScoreChoice, `RiemannGaussian.SemiprimeSourceScoreCountOrder, `RiemannGaussian.SemiprimeSourceScoreWeightBits, `RiemannGaussian.SemiprimeSourceScoreWeightAcquisition, `RiemannGaussian.SemiprimeSourceScorePredicateBits, `RiemannGaussian.SemiprimeSourceScorePredicateBitsBounds, `RiemannGaussian.SemiprimeSourceScoreCountBitsCore, `RiemannGaussian.SemiprimeSourceScoreCountBits, `RiemannGaussian.SemiprimeSourceScoreCountBitsBudget, `RiemannGaussian.SemiprimeSourceScoreCountBitsBounds, `RiemannGaussian.SemiprimeSourceScorePhysicalSearch, `RiemannGaussian.SemiprimeSourceScorePhysicalCaller, `RiemannGaussian.SemiprimeSourceScorePhysicalBudget, `RiemannGaussian.SemiprimeSourceScorePhysicalResources]
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
  liftIO <| IO.FS.writeFile "/tmp/semiprime-score-count-20261027/compiler-imports.json" (Lean.Json.arr (env.header.moduleNames.map (fun n => Lean.Json.str n.toString))).pretty
