import RiemannGaussian
import RiemannGaussian.SemiprimeBooleanDiagonal
import RiemannGaussian.SemiprimeCounterFiltration
import RiemannGaussian.SemiprimeCountRecovery
import RiemannGaussian.SemiprimeHermiteRecovery
import RiemannGaussian.SemiprimeSharedSummary
import RiemannGaussian.SemiprimeCounterRate
import RiemannGaussian.SemiprimeMacroFermatNetwork
import Lean.Util.CollectAxioms
import Mathlib.Tactic.Linter

open Lean Elab Command

#lint- in RiemannGaussian.SemiprimeBooleanDiagonal
#lint- in RiemannGaussian.SemiprimeCounterFiltration
#lint- in RiemannGaussian.SemiprimeCountRecovery
#lint- in RiemannGaussian.SemiprimeHermiteRecovery
#lint- in RiemannGaussian.SemiprimeSharedSummary
#lint- in RiemannGaussian.SemiprimeCounterRate
#lint- in RiemannGaussian.SemiprimeMacroFermatNetwork

run_cmd do
  let env ← getEnv
  let expected : List Name := [`RiemannGaussian.SemiprimeBooleanDiagonal, `RiemannGaussian.SemiprimeCounterFiltration, `RiemannGaussian.SemiprimeCountRecovery, `RiemannGaussian.SemiprimeHermiteRecovery, `RiemannGaussian.SemiprimeSharedSummary, `RiemannGaussian.SemiprimeCounterRate, `RiemannGaussian.SemiprimeMacroFermatNetwork]
  let mut audited : Nat := 0
  for h : i in [0:env.header.moduleNames.size] do
    let moduleName := env.header.moduleNames[i]
    unless moduleName ∈ expected do continue
    let mut declarations : Nat := 0
    let mut theorems : Nat := 0
    for ci in env.header.moduleData[i]!.constants do
      declarations := declarations + 1
      if ci.isAxiom then throwError "project-defined axiom: {ci.name}"
      if ci.isTheorem then theorems := theorems + 1
      for axiomName in (← Lean.collectAxioms ci.name) do
        unless axiomName == ``propext || axiomName == ``Classical.choice ||
            axiomName == ``Quot.sound do
          throwError "unexpected transitive axiom in {ci.name}: {axiomName}"
    unless theorems > 0 do throwError "no theorem audited in {moduleName}"
    logInfo m!"AUDIT {moduleName}: declarations={declarations}, theorems={theorems}, standard_axioms_only=true"
    audited := audited + 1
  unless audited == expected.length do throwError "missing modules: audited {audited}"
