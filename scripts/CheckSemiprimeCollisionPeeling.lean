import RiemannGaussian
import RiemannGaussian.SemiprimeCollisionPeeling
import Lean.Util.CollectAxioms
import Mathlib.Tactic.Linter

/-! Optional audit of the collision-distance stripping and factor branch. -/

open Lean Elab Command

#lint+ in RiemannGaussian.SemiprimeCollisionPeeling

run_cmd do
  let env ← getEnv
  let moduleName := `RiemannGaussian.SemiprimeCollisionPeeling
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
