import RiemannGaussian
import RiemannGaussian.SemiprimeMacroEntryBitPrimitives
import Lean.Util.CollectAxioms
import Mathlib.Tactic.Linter

open Lean Elab Command

#lint+ in RiemannGaussian.SemiprimeMacroEntryBitPrimitives

run_cmd do
  let env ← getEnv
  let targets := #[`RiemannGaussian.SemiprimeMacroEntryBitPrimitives]
  let mut declarations : Nat := 0
  let mut theorems : Nat := 0
  for h : i in [0:env.header.moduleNames.size] do
    unless targets.contains env.header.moduleNames[i] do continue
    for ci in env.header.moduleData[i]!.constants do
      declarations := declarations+1
      if ci.isAxiom then throwError "project-defined axiom: {ci.name}"
      if ci.isTheorem then theorems := theorems+1
      for ax in (← Lean.collectAxioms ci.name) do
        unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
          throwError "unexpected transitive axiom in {ci.name}: {ax}"
  unless theorems > 0 do throwError "no graph semantic theorem checked"
  logInfo m!"Checked {declarations} declarations, {theorems} theorems; only standard axioms."
