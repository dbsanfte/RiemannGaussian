import RiemannGaussian.SemiprimeD1BoundaryLeafValue
import Lean.Util.CollectAxioms
import Mathlib.Tactic.Linter
open Lean Elab Command
#lint+ in RiemannGaussian.SemiprimeD1BoundaryLeafCorrectness
#lint+ in RiemannGaussian.SemiprimeD1BoundaryAddresses
#lint+ in RiemannGaussian.SemiprimeD1BoundaryRecordsShape
#lint+ in RiemannGaussian.SemiprimeD1BoundaryFiber
#lint+ in RiemannGaussian.SemiprimeD1BoundaryCatalogue
#lint+ in RiemannGaussian.SemiprimeD1BoundaryBucketValue
#lint+ in RiemannGaussian.SemiprimeD1BoundaryTensorRep
#lint+ in RiemannGaussian.SemiprimeD1BoundaryLeaf
run_cmd do
  let env ← getEnv
  let modules : Array Name := #[`RiemannGaussian.SemiprimeD1BoundaryLeafCorrectness,`RiemannGaussian.SemiprimeD1BoundaryAddresses,`RiemannGaussian.SemiprimeD1BoundaryRecordsShape,`RiemannGaussian.SemiprimeD1BoundaryFiber,`RiemannGaussian.SemiprimeD1BoundaryCatalogue,`RiemannGaussian.SemiprimeD1BoundaryBucketValue,`RiemannGaussian.SemiprimeD1BoundaryTensorRep,`RiemannGaussian.SemiprimeD1BoundaryLeafValue]
  let mut declarations : Nat := 0
  let mut theorems : Nat := 0
  for h : i in [0:env.header.moduleNames.size] do
    unless modules.contains env.header.moduleNames[i] do continue
    for ci in env.header.moduleData[i]!.constants do
      declarations := declarations + 1
      if ci.isAxiom then throwError "project-defined axiom: {ci.name}"
      if ci.isTheorem then theorems := theorems + 1
      for axiomName in (← Lean.collectAxioms ci.name) do
        unless axiomName == ``propext || axiomName == ``Classical.choice || axiomName == ``Quot.sound do
          throwError "unexpected transitive axiom in {ci.name}: {axiomName}"
  unless theorems > 0 do throwError "no leaf correctness theorem audited"
  logInfo m!"Checked {declarations} declarations, {theorems} theorems; only standard axioms."
