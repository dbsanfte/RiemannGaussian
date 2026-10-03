import RiemannGaussian.SemiprimeRHCancellation
import RiemannGaussian.ZetaRieszPrimeFourier
import RiemannGaussian.ZetaRieszSignedFrequency
import RiemannGaussian.ZetaRieszShortDivisorCancellation
import RiemannGaussian.EtaMoebiusQuotientAbel
import RiemannGaussian.ZetaRieszPairMatching
import RiemannGaussian.ZetaRieszComplexNullFloor
import RiemannGaussian.ZetaRieszQuantitativeNullStep
import Lean.Util.CollectAxioms
import Mathlib.Tactic.Linter

/-! Optional focused side-project proof check; outside ordinary CI. -/

open Lean Elab Command

#lint+ in RiemannGaussian.SemiprimeRHCancellation

run_cmd do
  let env ← getEnv
  let mut declarations : Nat := 0
  let mut theorems : Nat := 0
  for h : i in [0:env.header.moduleNames.size] do
    unless env.header.moduleNames[i] == `RiemannGaussian.SemiprimeRHCancellation do continue
    for ci in env.header.moduleData[i]!.constants do
      declarations := declarations + 1
      if ci.isAxiom then throwError "project-defined axiom: {ci.name}"
      if ci.isTheorem then theorems := theorems + 1
      for axiomName in (← Lean.collectAxioms ci.name) do
        unless axiomName == ``propext || axiomName == ``Classical.choice ||
            axiomName == ``Quot.sound do
          throwError "unexpected transitive axiom in {ci.name}: {axiomName}"
  unless theorems > 0 do throwError "no RH cancellation transfer proofs checked"
  logInfo m!"Checked {declarations} declarations, {theorems} theorems; only standard axioms."
  let references : List Name := [
    `RiemannGaussian.ZetaRieszPrimeFourier.divisorCharacter_eq_primeProduct,
    `RiemannGaussian.ZetaRieszSignedFrequency.primePair_eq_centered,
    `RiemannGaussian.ZetaRieszShortDivisorCancellation.signed_block_eq_zero,
    `RiemannGaussian.pairedEtaCompletedMoebiusCompleteQuotientAggregate_eq_abel,
    `RiemannGaussian.ZetaRieszPairMatching.sum_eq_pairs_add_remainder,
    `RiemannGaussian.ZetaRieszComplexNullFloor.increment_coherent_zero,
    `RiemannGaussian.ZetaRieszQuantitativeNullStep.cubicIncrement_coherent_zero]
  for name in references do
    let some ci := env.find? name | throwError "missing RH reference: {name}"
    unless ci.isTheorem do throwError "RH reference is not a theorem: {name}"
    for axiomName in (← Lean.collectAxioms name) do
      unless axiomName == ``propext || axiomName == ``Classical.choice ||
          axiomName == ``Quot.sound do
        throwError "unexpected transitive axiom in RH reference {name}: {axiomName}"
  logInfo m!"Verified {references.length} compiled RH cancellation references; only standard axioms."
