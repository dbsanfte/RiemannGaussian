import RiemannGaussian
import RiemannGaussian.SemiprimeKernelResidual
import Lean.Util.CollectAxioms
import Mathlib.Tactic.Linter

/-! Optional audit of cached small-prime stripping and residual transport. -/

open Lean Elab Command

#lint+ in RiemannGaussian.SemiprimeKernelResidual

run_cmd do
  let env ← getEnv
  let moduleName := `RiemannGaussian.SemiprimeKernelResidual
  let mut declarations : Nat := 0
  let mut theorems : Nat := 0
  for h : i in [0:env.header.moduleNames.size] do
    unless env.header.moduleNames[i] == moduleName do continue
    for ci in env.header.moduleData[i]!.constants do
      declarations := declarations + 1
      if ci.isAxiom then throwError "project-defined axiom: {ci.name}"
      if ci.isTheorem then theorems := theorems + 1
      for axiomName in (← Lean.collectAxioms ci.name) do
        unless axiomName == ``propext || axiomName == ``Classical.choice ||
            axiomName == ``Quot.sound do
          throwError "unexpected transitive axiom in {ci.name}: {axiomName}"
  unless theorems > 0 do throwError "no {moduleName} proofs checked"
  logInfo m!"{moduleName}: checked {declarations} declarations, {theorems} theorems; only standard axioms."
