import RiemannGaussian.SemiprimeD1HybridCallReport
import Mathlib.Tactic.Linter
import Lean.Util.CollectAxioms

open Lean Elab Command
#lint- in RiemannGaussian.SemiprimeD1HybridPathDecay
#lint- in RiemannGaussian.SemiprimeD1HybridPathRate
#lint- in RiemannGaussian.SemiprimeD1HybridCallEnvelope
#lint- in RiemannGaussian.SemiprimeD1HybridCallBranch
#lint- in RiemannGaussian.SemiprimeD1HybridCallTree
#lint- in RiemannGaussian.SemiprimeD1HybridCallOriginal
#lint- in RiemannGaussian.SemiprimeD1HybridCallReport

run_cmd do
  let env ← getEnv
  let owned : Array String := #["RiemannGaussian.SemiprimeD1HybridPathDecay","RiemannGaussian.SemiprimeD1HybridPathRate","RiemannGaussian.SemiprimeD1HybridCallEnvelope","RiemannGaussian.SemiprimeD1HybridCallBranch","RiemannGaussian.SemiprimeD1HybridCallTree","RiemannGaussian.SemiprimeD1HybridCallOriginal","RiemannGaussian.SemiprimeD1HybridCallReport"]
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
  logInfo m!"HYBRID_ALL_GENERATED_STD3_PASS declarations={declarations} theorems={theorems} modules={owned.size}"
