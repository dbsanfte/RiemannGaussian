import RiemannGaussian
import RiemannGaussian.SemiprimeNativeGroupBitsHeight
import RiemannGaussian.SemiprimeWordPacketWidth
import RiemannGaussian.SemiprimeWordPacketWidthBudget
import RiemannGaussian.SemiprimeWordFoldArithmetic
import RiemannGaussian.SemiprimeWordFoldBounds
import RiemannGaussian.SemiprimeMaterializedWordFibre
import RiemannGaussian.SemiprimeMaterializedWordFibreBounds
import RiemannGaussian.SemiprimeWordPacketCounter
import RiemannGaussian.SemiprimeWordPacketCounterBudget
import RiemannGaussian.SemiprimeWordPacketSetupCounter
import RiemannGaussian.SemiprimeWordPacketSetupBudget
import RiemannGaussian.SemiprimeWordPacketPublicController
import RiemannGaussian.SemiprimeWordPacketScheduledController
import Lean.Util.CollectAxioms
import Mathlib.Tactic.Linter
open Lean Elab Command
#lint+ in RiemannGaussian.SemiprimeNativeGroupBitsHeight
#lint+ in RiemannGaussian.SemiprimeWordPacketWidth
#lint+ in RiemannGaussian.SemiprimeWordPacketWidthBudget
#lint+ in RiemannGaussian.SemiprimeWordFoldArithmetic
#lint+ in RiemannGaussian.SemiprimeWordFoldBounds
#lint+ in RiemannGaussian.SemiprimeMaterializedWordFibre
#lint+ in RiemannGaussian.SemiprimeMaterializedWordFibreBounds
#lint+ in RiemannGaussian.SemiprimeWordPacketCounter
#lint+ in RiemannGaussian.SemiprimeWordPacketCounterBudget
#lint+ in RiemannGaussian.SemiprimeWordPacketSetupCounter
#lint+ in RiemannGaussian.SemiprimeWordPacketSetupBudget
#lint+ in RiemannGaussian.SemiprimeWordPacketPublicController
#lint+ in RiemannGaussian.SemiprimeWordPacketScheduledController
run_cmd do
  let env ← getEnv
  let expected : List Name := [`RiemannGaussian.SemiprimeNativeGroupBitsHeight, `RiemannGaussian.SemiprimeWordPacketWidth, `RiemannGaussian.SemiprimeWordPacketWidthBudget, `RiemannGaussian.SemiprimeWordFoldArithmetic, `RiemannGaussian.SemiprimeWordFoldBounds, `RiemannGaussian.SemiprimeMaterializedWordFibre, `RiemannGaussian.SemiprimeMaterializedWordFibreBounds, `RiemannGaussian.SemiprimeWordPacketCounter, `RiemannGaussian.SemiprimeWordPacketCounterBudget, `RiemannGaussian.SemiprimeWordPacketSetupCounter, `RiemannGaussian.SemiprimeWordPacketSetupBudget, `RiemannGaussian.SemiprimeWordPacketPublicController, `RiemannGaussian.SemiprimeWordPacketScheduledController]
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
  liftIO <| IO.FS.writeFile "/tmp/semiprime-word-folds-20261027/compiler-imports.json" (Lean.Json.arr (env.header.moduleNames.map (fun n => Lean.Json.str n.toString))).pretty
