import RiemannGaussian
import RiemannGaussian.SemiprimeAffineJetBits
import RiemannGaussian.SemiprimeNormalizedInverseBits
import RiemannGaussian.SemiprimeNormalizedInverseBitsBounds
import RiemannGaussian.SemiprimeHermiteEvaluationBits
import RiemannGaussian.SemiprimeHermiteEvaluationBitsBounds
import RiemannGaussian.SemiprimeCardinalInputBits
import RiemannGaussian.SemiprimeScalarWordSum
import RiemannGaussian.SemiprimeHermiteWordWidth
import RiemannGaussian.SemiprimeHermiteNodeBits
import RiemannGaussian.SemiprimeHermiteNodeBitsCorrectness
import RiemannGaussian.SemiprimeHermiteNodeBitsBounds
import RiemannGaussian.SemiprimeAcquiredHermiteBits
import RiemannGaussian.SemiprimeWordPacketHermiteInput
import RiemannGaussian.SemiprimeHermiteBitsCounter
import RiemannGaussian.SemiprimeHermiteBitsCounterBudget
import RiemannGaussian.SemiprimeHermiteBitsSetupCounter
import RiemannGaussian.SemiprimeHermiteBitsSetupBudget
import RiemannGaussian.SemiprimeHermiteBitsPublicController
import RiemannGaussian.SemiprimeHermiteBitsScheduledController
import Lean.Util.CollectAxioms
import Mathlib.Tactic.Linter
open Lean Elab Command
#lint+ in RiemannGaussian.SemiprimeAffineJetBits
#lint+ in RiemannGaussian.SemiprimeNormalizedInverseBits
#lint+ in RiemannGaussian.SemiprimeNormalizedInverseBitsBounds
#lint+ in RiemannGaussian.SemiprimeHermiteEvaluationBits
#lint+ in RiemannGaussian.SemiprimeHermiteEvaluationBitsBounds
#lint+ in RiemannGaussian.SemiprimeCardinalInputBits
#lint+ in RiemannGaussian.SemiprimeScalarWordSum
#lint+ in RiemannGaussian.SemiprimeHermiteWordWidth
#lint+ in RiemannGaussian.SemiprimeHermiteNodeBits
#lint+ in RiemannGaussian.SemiprimeHermiteNodeBitsCorrectness
#lint+ in RiemannGaussian.SemiprimeHermiteNodeBitsBounds
#lint+ in RiemannGaussian.SemiprimeAcquiredHermiteBits
#lint+ in RiemannGaussian.SemiprimeWordPacketHermiteInput
#lint+ in RiemannGaussian.SemiprimeHermiteBitsCounter
#lint+ in RiemannGaussian.SemiprimeHermiteBitsCounterBudget
#lint+ in RiemannGaussian.SemiprimeHermiteBitsSetupCounter
#lint+ in RiemannGaussian.SemiprimeHermiteBitsSetupBudget
#lint+ in RiemannGaussian.SemiprimeHermiteBitsPublicController
#lint+ in RiemannGaussian.SemiprimeHermiteBitsScheduledController
run_cmd do
  let env ← getEnv
  let expected : List Name := [`RiemannGaussian.SemiprimeAffineJetBits, `RiemannGaussian.SemiprimeNormalizedInverseBits, `RiemannGaussian.SemiprimeNormalizedInverseBitsBounds, `RiemannGaussian.SemiprimeHermiteEvaluationBits, `RiemannGaussian.SemiprimeHermiteEvaluationBitsBounds, `RiemannGaussian.SemiprimeCardinalInputBits, `RiemannGaussian.SemiprimeScalarWordSum, `RiemannGaussian.SemiprimeHermiteWordWidth, `RiemannGaussian.SemiprimeHermiteNodeBits, `RiemannGaussian.SemiprimeHermiteNodeBitsCorrectness, `RiemannGaussian.SemiprimeHermiteNodeBitsBounds, `RiemannGaussian.SemiprimeAcquiredHermiteBits, `RiemannGaussian.SemiprimeWordPacketHermiteInput, `RiemannGaussian.SemiprimeHermiteBitsCounter, `RiemannGaussian.SemiprimeHermiteBitsCounterBudget, `RiemannGaussian.SemiprimeHermiteBitsSetupCounter, `RiemannGaussian.SemiprimeHermiteBitsSetupBudget, `RiemannGaussian.SemiprimeHermiteBitsPublicController, `RiemannGaussian.SemiprimeHermiteBitsScheduledController]
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
  liftIO <| IO.FS.writeFile "/tmp/semiprime-hermite-words-20261027/compiler-imports.json" (Lean.Json.arr (env.header.moduleNames.map (fun n => Lean.Json.str n.toString))).pretty
