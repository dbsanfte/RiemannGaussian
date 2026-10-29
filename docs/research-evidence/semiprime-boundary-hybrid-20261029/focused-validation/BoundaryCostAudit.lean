import RiemannGaussian.SemiprimeD1BoundaryLeafPolynomial
import Mathlib.Tactic.Linter
import Lean.Util.CollectAxioms

open Lean Elab Command
#lint- in RiemannGaussian.SemiprimeD1BoundaryRecordsCanonical
#lint- in RiemannGaussian.SemiprimeD1BoundaryLeafCanonical
#lint- in RiemannGaussian.SemiprimeD1BoundaryRecordsGroupBounds
#lint- in RiemannGaussian.SemiprimeD1BoundaryRecordsContractBounds
#lint- in RiemannGaussian.SemiprimeD1BoundaryRecordsAttachBounds
#lint- in RiemannGaussian.SemiprimeD1BoundaryRecordsSeedBounds
#lint- in RiemannGaussian.SemiprimeD1BoundaryRecordsTableBounds
#lint- in RiemannGaussian.SemiprimeD1BoundaryLeafBounds
#lint- in RiemannGaussian.SemiprimeD1BoundaryLeafReport
#lint- in RiemannGaussian.SemiprimeD1BoundaryLeafLoad

#lint- in RiemannGaussian.SemiprimeD1BoundaryBudgetEnvelope
#lint- in RiemannGaussian.SemiprimeD1BoundaryPlanBudget
#lint- in RiemannGaussian.SemiprimeD1BoundaryLeafPolynomial

run_cmd do
  let env ← getEnv
  let owned : Array String := #["RiemannGaussian.SemiprimeD1BoundaryRecordsCanonical","RiemannGaussian.SemiprimeD1BoundaryLeafCanonical","RiemannGaussian.SemiprimeD1BoundaryRecordsGroupBounds","RiemannGaussian.SemiprimeD1BoundaryRecordsContractBounds","RiemannGaussian.SemiprimeD1BoundaryRecordsAttachBounds","RiemannGaussian.SemiprimeD1BoundaryRecordsSeedBounds","RiemannGaussian.SemiprimeD1BoundaryRecordsTableBounds","RiemannGaussian.SemiprimeD1BoundaryLeafBounds","RiemannGaussian.SemiprimeD1BoundaryLeafReport","RiemannGaussian.SemiprimeD1BoundaryLeafLoad","RiemannGaussian.SemiprimeD1BoundaryBudgetEnvelope","RiemannGaussian.SemiprimeD1BoundaryPlanBudget","RiemannGaussian.SemiprimeD1BoundaryLeafPolynomial"]
  let mut declarations : Nat := 0
  let mut theorems : Nat := 0
  for h : idx in [0:env.header.moduleNames.size] do
    unless owned.contains env.header.moduleNames[idx].toString do continue
    for ci in env.header.moduleData[idx]!.constants do
      declarations := declarations+1
      if ci.isTheorem then theorems := theorems+1
      if ci.isAxiom then throwError "owned project axiom: {ci.name}"
      let axs ← Lean.collectAxioms ci.name
      unless axs.all (fun a => a == ``propext || a == ``Classical.choice || a == ``Quot.sound) do
        throwError "nonstandard axiom dependency: {ci.name}: {axs}"
  logInfo m!"BOUNDARY_COST_ALL_GENERATED_STD3_PASS declarations={declarations} theorems={theorems} modules={owned.size}"
