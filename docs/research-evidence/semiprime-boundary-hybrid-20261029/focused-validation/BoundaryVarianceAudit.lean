import RiemannGaussian.SemiprimeD1BoundaryVariance
import Mathlib.Tactic.Linter
import Lean.Util.CollectAxioms

open Lean Elab Command
#lint- in RiemannGaussian.SemiprimeD1BoundaryInitialVariance
#lint- in RiemannGaussian.SemiprimeD1BoundaryOverlap
#lint- in RiemannGaussian.SemiprimeD1BoundaryVariance

run_cmd do
  let env ← getEnv
  let owned : Array String := #["RiemannGaussian.SemiprimeD1BoundaryInitialVariance","RiemannGaussian.SemiprimeD1BoundaryOverlap","RiemannGaussian.SemiprimeD1BoundaryVariance"]
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
  logInfo m!"VARIANCE_ALL_GENERATED_STD3_PASS declarations={declarations} theorems={theorems} modules={owned.size}"
