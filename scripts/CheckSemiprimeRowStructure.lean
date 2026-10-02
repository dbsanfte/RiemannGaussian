import RiemannGaussian.SemiprimeRowStructure
import Lean.Util.CollectAxioms
import Mathlib.Tactic.Linter

/-! Optional scoped side-project proof audit; outside ordinary CI. -/

open Lean Elab Command

#lint+ in RiemannGaussian.SemiprimeRowStructure

run_cmd do
  let env ← getEnv
  let mut declarations : Nat := 0
  let mut theorems : Nat := 0
  for h : i in [0:env.header.moduleNames.size] do
    unless env.header.moduleNames[i] == `RiemannGaussian.SemiprimeRowStructure do continue
    for ci in env.header.moduleData[i]!.constants do
      declarations := declarations + 1
      if ci.isAxiom then throwError "project-defined axiom: {ci.name}"
      if ci.isTheorem then theorems := theorems + 1
      for axiomName in (← Lean.collectAxioms ci.name) do
        unless axiomName == ``propext || axiomName == ``Classical.choice ||
            axiomName == ``Quot.sound do
          throwError "unexpected transitive axiom in {ci.name}: {axiomName}"
  unless theorems > 0 do throwError "no row-structure proofs checked"
  logInfo m!"Checked {declarations} declarations, {theorems} theorems; only standard axioms."
