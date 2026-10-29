import RiemannGaussian
import RiemannGaussian.SemiprimeCounterNative
import RiemannGaussian.SemiprimeCounterSeparation
import RiemannGaussian.SemiprimeCounterCompose
import RiemannGaussian.SemiprimeCounterTail
import RiemannGaussian.SemiprimeJetRecurrence
import RiemannGaussian.SemiprimeBooleanNetwork
import RiemannGaussian.SemiprimeCounterSearch
import RiemannGaussian.SemiprimeMacroBitNetwork
import Lean.Util.CollectAxioms
import Mathlib.Tactic.Linter

open Lean Elab Command

#lint- in RiemannGaussian.SemiprimeCounterNative
#lint- in RiemannGaussian.SemiprimeCounterSeparation
#lint- in RiemannGaussian.SemiprimeCounterCompose
#lint- in RiemannGaussian.SemiprimeCounterTail
#lint- in RiemannGaussian.SemiprimeJetRecurrence
#lint- in RiemannGaussian.SemiprimeBooleanNetwork
#lint- in RiemannGaussian.SemiprimeCounterSearch
#lint- in RiemannGaussian.SemiprimeMacroBitNetwork

run_cmd do
  let env ← getEnv
  let expected : List Name := [`RiemannGaussian.SemiprimeCounterNative, `RiemannGaussian.SemiprimeCounterSeparation, `RiemannGaussian.SemiprimeCounterCompose, `RiemannGaussian.SemiprimeCounterTail, `RiemannGaussian.SemiprimeJetRecurrence, `RiemannGaussian.SemiprimeBooleanNetwork, `RiemannGaussian.SemiprimeCounterSearch, `RiemannGaussian.SemiprimeMacroBitNetwork]
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
