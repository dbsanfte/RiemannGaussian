import RiemannGaussian
import RiemannGaussian.SemiprimeCachedRawConstraints
import RiemannGaussian.SemiprimePaidSourceMetadata
import RiemannGaussian.SemiprimePaidRawAcquisition
import RiemannGaussian.SemiprimeEncodedRowSelection
import RiemannGaussian.SemiprimePaidMeasurementBound
import RiemannGaussian.SemiprimeRuntimeDesignCache
import RiemannGaussian.SemiprimePaidRuntimeDesign
import RiemannGaussian.SemiprimeFullSetupCounter
import RiemannGaussian.SemiprimeFullSetupPublicController
import RiemannGaussian.SemiprimeFullSetupScheduledController
import Lean.Util.CollectAxioms
import Mathlib.Tactic.Linter
open Lean Elab Command
#lint+ in RiemannGaussian.SemiprimeCachedRawConstraints
#lint+ in RiemannGaussian.SemiprimePaidSourceMetadata
#lint+ in RiemannGaussian.SemiprimePaidRawAcquisition
#lint+ in RiemannGaussian.SemiprimeEncodedRowSelection
#lint+ in RiemannGaussian.SemiprimePaidMeasurementBound
#lint+ in RiemannGaussian.SemiprimeRuntimeDesignCache
#lint+ in RiemannGaussian.SemiprimePaidRuntimeDesign
#lint+ in RiemannGaussian.SemiprimeFullSetupCounter
#lint+ in RiemannGaussian.SemiprimeFullSetupPublicController
#lint+ in RiemannGaussian.SemiprimeFullSetupScheduledController
run_cmd do
  let env ← getEnv
  let expected : List Name := [`RiemannGaussian.SemiprimeCachedRawConstraints, `RiemannGaussian.SemiprimePaidSourceMetadata, `RiemannGaussian.SemiprimePaidRawAcquisition, `RiemannGaussian.SemiprimeEncodedRowSelection, `RiemannGaussian.SemiprimePaidMeasurementBound, `RiemannGaussian.SemiprimeRuntimeDesignCache, `RiemannGaussian.SemiprimePaidRuntimeDesign, `RiemannGaussian.SemiprimeFullSetupCounter, `RiemannGaussian.SemiprimeFullSetupPublicController, `RiemannGaussian.SemiprimeFullSetupScheduledController]
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
  liftIO <| IO.FS.writeFile "/tmp/semiprime-design-clock-20261027/compiler-imports.json" (Lean.Json.arr (env.header.moduleNames.map (fun n => Lean.Json.str n.toString))).pretty
