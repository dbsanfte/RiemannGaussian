import RiemannGaussian
import RiemannGaussian.SemiprimeD1HybridPublicReport
import RiemannGaussian.SemiprimeD1BoundaryWidth
import RiemannGaussian.SemiprimeD1BoundaryColourWords
import Mathlib.Tactic.Linter
import Lean.Util.CollectAxioms

open Lean Elab Command
#lint- in RiemannGaussian.SemiprimeD1BoundaryChoice
#lint- in RiemannGaussian.SemiprimeD1BoundaryPotential
#lint- in RiemannGaussian.SemiprimeD1BoundaryColourWords
#lint- in RiemannGaussian.SemiprimeD1BoundaryLeafPorts
#lint- in RiemannGaussian.SemiprimeD1BoundaryMergeMean
#lint- in RiemannGaussian.SemiprimeD1BoundaryWidth
#lint- in RiemannGaussian.SemiprimeD1HybridRecursiveKernel
#lint- in RiemannGaussian.SemiprimeD1HybridRecursiveCounter
#lint- in RiemannGaussian.SemiprimeD1HybridPublicExecution

run_cmd do
  let env ← getEnv
  let owned : Array String := #[
    "RiemannGaussian.SemiprimeD1BoundaryChoice",
    "RiemannGaussian.SemiprimeD1BoundaryPotential",
    "RiemannGaussian.SemiprimeD1BoundaryColourWords",
    "RiemannGaussian.SemiprimeD1BoundaryLeafPorts",
    "RiemannGaussian.SemiprimeD1BoundaryMergeMean",
    "RiemannGaussian.SemiprimeD1BoundaryWidth",
    "RiemannGaussian.SemiprimeD1HybridRecursiveKernel",
    "RiemannGaussian.SemiprimeD1HybridRecursiveCounter",
    "RiemannGaussian.SemiprimeD1HybridPublicExecution",
    "RiemannGaussian.SemiprimeD1HybridCorrectness",
    "RiemannGaussian.SemiprimeD1HybridPublicReport"]
  let mut declarations : Nat := 0
  let mut theorems : Nat := 0
  for h : idx in [0:env.header.moduleNames.size] do
    unless owned.contains env.header.moduleNames[idx].toString do continue
    for ci in env.header.moduleData[idx]!.constants do
      declarations := declarations + 1
      if ci.isTheorem then theorems := theorems + 1
      if ci.isAxiom then throwError "new project axiom: {ci.name}"
      let axs ← Lean.collectAxioms ci.name
      unless axs.all (fun a => a == ``propext || a == ``Classical.choice || a == ``Quot.sound) do
        throwError "nonstandard axiom dependency: {ci.name}: {axs}"
  logInfo m!"HYBRID_PARENT_ALL_GENERATED_STD3_PASS declarations={declarations} theorems={theorems} modules={owned.size}"
