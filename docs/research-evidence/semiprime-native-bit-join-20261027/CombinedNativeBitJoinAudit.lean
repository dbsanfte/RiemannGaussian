import RiemannGaussian
import RiemannGaussian.SemiprimeRationalWordAcquisition
import RiemannGaussian.SemiprimeSourceWordAcquisition
import RiemannGaussian.SemiprimeNativeInputBits
import RiemannGaussian.SemiprimeCorrectedPortBits
import RiemannGaussian.SemiprimeCorrectedPortBitsBounds
import RiemannGaussian.SemiprimeNativeLocalBits
import RiemannGaussian.SemiprimeNativeGroupBits
import RiemannGaussian.SemiprimeNativeGroupBitsBudget
import RiemannGaussian.SemiprimeMaterializedGroupAdapter
import RiemannGaussian.SemiprimePrefixEntryWords
import RiemannGaussian.SemiprimeNativeBitsCounter
import RiemannGaussian.SemiprimeNativeBitsCounterBudget
import RiemannGaussian.SemiprimeNativeBitsSetupCounter
import RiemannGaussian.SemiprimeNativeBitsSetupBudget
import RiemannGaussian.SemiprimeNativeBitsPublicController
import RiemannGaussian.SemiprimeNativeBitsScheduledController
import Lean.Util.CollectAxioms
import Mathlib.Tactic.Linter
open Lean Elab Command
#lint+ in RiemannGaussian.SemiprimeRationalWordAcquisition
#lint+ in RiemannGaussian.SemiprimeSourceWordAcquisition
#lint+ in RiemannGaussian.SemiprimeNativeInputBits
#lint+ in RiemannGaussian.SemiprimeCorrectedPortBits
#lint+ in RiemannGaussian.SemiprimeCorrectedPortBitsBounds
#lint+ in RiemannGaussian.SemiprimeNativeLocalBits
#lint+ in RiemannGaussian.SemiprimeNativeGroupBits
#lint+ in RiemannGaussian.SemiprimeNativeGroupBitsBudget
#lint+ in RiemannGaussian.SemiprimeMaterializedGroupAdapter
#lint+ in RiemannGaussian.SemiprimePrefixEntryWords
#lint+ in RiemannGaussian.SemiprimeNativeBitsCounter
#lint+ in RiemannGaussian.SemiprimeNativeBitsCounterBudget
#lint+ in RiemannGaussian.SemiprimeNativeBitsSetupCounter
#lint+ in RiemannGaussian.SemiprimeNativeBitsSetupBudget
#lint+ in RiemannGaussian.SemiprimeNativeBitsPublicController
#lint+ in RiemannGaussian.SemiprimeNativeBitsScheduledController
run_cmd do
  let env ← getEnv
  let expected : List Name := [`RiemannGaussian.SemiprimeRationalWordAcquisition, `RiemannGaussian.SemiprimeSourceWordAcquisition, `RiemannGaussian.SemiprimeNativeInputBits, `RiemannGaussian.SemiprimeCorrectedPortBits, `RiemannGaussian.SemiprimeCorrectedPortBitsBounds, `RiemannGaussian.SemiprimeNativeLocalBits, `RiemannGaussian.SemiprimeNativeGroupBits, `RiemannGaussian.SemiprimeNativeGroupBitsBudget, `RiemannGaussian.SemiprimeMaterializedGroupAdapter, `RiemannGaussian.SemiprimePrefixEntryWords, `RiemannGaussian.SemiprimeNativeBitsCounter, `RiemannGaussian.SemiprimeNativeBitsCounterBudget, `RiemannGaussian.SemiprimeNativeBitsSetupCounter, `RiemannGaussian.SemiprimeNativeBitsSetupBudget, `RiemannGaussian.SemiprimeNativeBitsPublicController, `RiemannGaussian.SemiprimeNativeBitsScheduledController]
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
  liftIO <| IO.FS.writeFile "/tmp/semiprime-native-bit-join-20261027/compiler-imports.json" (Lean.Json.arr (env.header.moduleNames.map (fun n => Lean.Json.str n.toString))).pretty
