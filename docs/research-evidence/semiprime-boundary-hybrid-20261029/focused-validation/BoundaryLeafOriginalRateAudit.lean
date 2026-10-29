import RiemannGaussian.SemiprimeD1BoundaryLeafOriginalReachRate
import Mathlib.Tactic.Linter
import Lean.Util.CollectAxioms

open Lean Elab Command
#lint- in RiemannGaussian.SemiprimeD1BoundaryLeafOriginalRate
#lint- in RiemannGaussian.SemiprimeD1BoundaryCheckedPolynomial
#lint- in RiemannGaussian.SemiprimeD1BoundaryCheckedOriginalRate
#lint- in RiemannGaussian.SemiprimeD1BoundaryLeafOriginalReachRate

run_cmd do
  let env ← getEnv
  let owned : Array String := #["RiemannGaussian.SemiprimeD1BoundaryLeafOriginalRate","RiemannGaussian.SemiprimeD1BoundaryCheckedPolynomial","RiemannGaussian.SemiprimeD1BoundaryCheckedOriginalRate","RiemannGaussian.SemiprimeD1BoundaryLeafOriginalReachRate"]
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
  logInfo m!"BOUNDARY_LEAF_ORIGINAL_RATE_STD3_PASS declarations={declarations} theorems={theorems} modules={owned.size}"
