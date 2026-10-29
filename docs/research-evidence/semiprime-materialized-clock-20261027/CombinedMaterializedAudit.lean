import RiemannGaussian
import RiemannGaussian.SemiprimeMaterializedAcquiredCounter
import RiemannGaussian.SemiprimeMaterializedFibre
import RiemannGaussian.SemiprimeMaterializedFibreNative
import RiemannGaussian.SemiprimeMaterializedFibrePacket
import RiemannGaussian.SemiprimeMaterializedOriginalSource
import RiemannGaussian.SemiprimeMaterializedPacking
import RiemannGaussian.SemiprimeMaterializedPublicExecution
import RiemannGaussian.SemiprimeMaterializedRate
import RiemannGaussian.SemiprimeMaterializedScheduledExecution
import RiemannGaussian.SemiprimeMaterializedScoreEnvironment
import RiemannGaussian.SemiprimeMaterializedScoreSearch
import RiemannGaussian.SemiprimeMaterializedSelectionHeight
import RiemannGaussian.SemiprimeMaterializedSelectionTemporaries
import RiemannGaussian.SemiprimeMaterializedSourceAcquisition
import RiemannGaussian.SemiprimeMaterializedSourceCache
import RiemannGaussian.SemiprimeMaterializedSourcePullback
import RiemannGaussian.SemiprimeMaterializedSourceRows
import RiemannGaussian.SemiprimeMaterializedSourceUniversal
import RiemannGaussian.SemiprimeMaterializedSourceWords
import RiemannGaussian.SemiprimeMaterializedWordSearch
import RiemannGaussian.SemiprimeMaterializedWords
import RiemannGaussian.SemiprimeCachedSourceCounter
import RiemannGaussian.SemiprimeCachedSourcePublicExecution
import RiemannGaussian.SemiprimeCachedSourceScheduledExecution
import Lean.Util.CollectAxioms
import Mathlib.Tactic.Linter
open Lean Elab Command
#lint+ in RiemannGaussian.SemiprimeMaterializedAcquiredCounter
#lint+ in RiemannGaussian.SemiprimeMaterializedFibre
#lint+ in RiemannGaussian.SemiprimeMaterializedFibreNative
#lint+ in RiemannGaussian.SemiprimeMaterializedFibrePacket
#lint+ in RiemannGaussian.SemiprimeMaterializedOriginalSource
#lint+ in RiemannGaussian.SemiprimeMaterializedPacking
#lint+ in RiemannGaussian.SemiprimeMaterializedPublicExecution
#lint+ in RiemannGaussian.SemiprimeMaterializedRate
#lint+ in RiemannGaussian.SemiprimeMaterializedScheduledExecution
#lint+ in RiemannGaussian.SemiprimeMaterializedScoreEnvironment
#lint+ in RiemannGaussian.SemiprimeMaterializedScoreSearch
#lint+ in RiemannGaussian.SemiprimeMaterializedSelectionHeight
#lint+ in RiemannGaussian.SemiprimeMaterializedSelectionTemporaries
#lint+ in RiemannGaussian.SemiprimeMaterializedSourceAcquisition
#lint+ in RiemannGaussian.SemiprimeMaterializedSourceCache
#lint+ in RiemannGaussian.SemiprimeMaterializedSourcePullback
#lint+ in RiemannGaussian.SemiprimeMaterializedSourceRows
#lint+ in RiemannGaussian.SemiprimeMaterializedSourceUniversal
#lint+ in RiemannGaussian.SemiprimeMaterializedSourceWords
#lint+ in RiemannGaussian.SemiprimeMaterializedWordSearch
#lint+ in RiemannGaussian.SemiprimeMaterializedWords
#lint+ in RiemannGaussian.SemiprimeCachedSourceCounter
#lint+ in RiemannGaussian.SemiprimeCachedSourcePublicExecution
#lint+ in RiemannGaussian.SemiprimeCachedSourceScheduledExecution
run_cmd do
  let env ← getEnv
  let expected : List Name := [`RiemannGaussian.SemiprimeMaterializedAcquiredCounter, `RiemannGaussian.SemiprimeMaterializedFibre, `RiemannGaussian.SemiprimeMaterializedFibreNative, `RiemannGaussian.SemiprimeMaterializedFibrePacket, `RiemannGaussian.SemiprimeMaterializedOriginalSource, `RiemannGaussian.SemiprimeMaterializedPacking, `RiemannGaussian.SemiprimeMaterializedPublicExecution, `RiemannGaussian.SemiprimeMaterializedRate, `RiemannGaussian.SemiprimeMaterializedScheduledExecution, `RiemannGaussian.SemiprimeMaterializedScoreEnvironment, `RiemannGaussian.SemiprimeMaterializedScoreSearch, `RiemannGaussian.SemiprimeMaterializedSelectionHeight, `RiemannGaussian.SemiprimeMaterializedSelectionTemporaries, `RiemannGaussian.SemiprimeMaterializedSourceAcquisition, `RiemannGaussian.SemiprimeMaterializedSourceCache, `RiemannGaussian.SemiprimeMaterializedSourcePullback, `RiemannGaussian.SemiprimeMaterializedSourceRows, `RiemannGaussian.SemiprimeMaterializedSourceUniversal, `RiemannGaussian.SemiprimeMaterializedSourceWords, `RiemannGaussian.SemiprimeMaterializedWordSearch, `RiemannGaussian.SemiprimeMaterializedWords, `RiemannGaussian.SemiprimeCachedSourceCounter, `RiemannGaussian.SemiprimeCachedSourcePublicExecution, `RiemannGaussian.SemiprimeCachedSourceScheduledExecution]
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
  liftIO <| IO.FS.writeFile "/tmp/semiprime-materialized-clock-20261027/compiler-imports.json" (Lean.Json.arr (env.header.moduleNames.map (fun n => Lean.Json.str n.toString))).pretty
