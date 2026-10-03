import RiemannGaussian
import RiemannGaussian.SemiprimeReciprocalRows
import Lean.Util.CollectAxioms
import Mathlib.Tactic.Linter

/-! Ordinary-root lint and all-declaration axiom audit of reciprocal row correlations. -/

open Lean Elab Command

#lint+ in RiemannGaussian.SemiprimeReciprocalRows

run_cmd do
  let env ← getEnv
  let moduleName := `RiemannGaussian.SemiprimeReciprocalRows
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
