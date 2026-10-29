import RiemannGaussian
import RiemannGaussian.SemiprimeMacroFlagExtension
import RiemannGaussian.SemiprimeMacroGraphSemantics
import RiemannGaussian.SemiprimeMacroGraphUnique
import RiemannGaussian.SemiprimeMacroGraphExtension
import RiemannGaussian.SemiprimeMacroParameters
import RiemannGaussian.SemiprimePublicFactorCount
import RiemannGaussian.SemiprimeScheduledCounter
import RiemannGaussian.SemiprimeJetArray
import RiemannGaussian.SemiprimeJetArrayHeight
import RiemannGaussian.SemiprimeCounterEnumeration
import RiemannGaussian.SemiprimeSourceRowHeight
import RiemannGaussian.SemiprimeTaylorHeight
import RiemannGaussian.SemiprimeCardinalHeight
import Lean.Util.CollectAxioms
import Mathlib.Tactic.Linter

open Lean Elab Command
#lint+ in RiemannGaussian.SemiprimeMacroFlagExtension
#lint+ in RiemannGaussian.SemiprimeMacroGraphSemantics
#lint+ in RiemannGaussian.SemiprimeMacroGraphUnique
#lint+ in RiemannGaussian.SemiprimeMacroGraphExtension
#lint+ in RiemannGaussian.SemiprimeMacroParameters
#lint+ in RiemannGaussian.SemiprimePublicFactorCount
#lint+ in RiemannGaussian.SemiprimeScheduledCounter
#lint+ in RiemannGaussian.SemiprimeJetArray
#lint+ in RiemannGaussian.SemiprimeJetArrayHeight
#lint+ in RiemannGaussian.SemiprimeCounterEnumeration
#lint+ in RiemannGaussian.SemiprimeSourceRowHeight
#lint+ in RiemannGaussian.SemiprimeTaylorHeight
#lint+ in RiemannGaussian.SemiprimeCardinalHeight

run_cmd do
  let env ← getEnv
  let expected : List Name := [`RiemannGaussian.SemiprimeMacroFlagExtension, `RiemannGaussian.SemiprimeMacroGraphSemantics, `RiemannGaussian.SemiprimeMacroGraphUnique, `RiemannGaussian.SemiprimeMacroGraphExtension, `RiemannGaussian.SemiprimeMacroParameters, `RiemannGaussian.SemiprimePublicFactorCount, `RiemannGaussian.SemiprimeScheduledCounter, `RiemannGaussian.SemiprimeJetArray, `RiemannGaussian.SemiprimeJetArrayHeight, `RiemannGaussian.SemiprimeCounterEnumeration, `RiemannGaussian.SemiprimeSourceRowHeight, `RiemannGaussian.SemiprimeTaylorHeight, `RiemannGaussian.SemiprimeCardinalHeight]
  let mut checked : Nat := 0
  for h : i in [0:env.header.moduleNames.size] do
    let moduleName := env.header.moduleNames[i]
    unless moduleName ∈ expected do continue
    let mut declarations : Nat := 0
    let mut theorems : Nat := 0
    for ci in env.header.moduleData[i]!.constants do
      declarations := declarations + 1
      if ci.isAxiom then throwError "project axiom: {ci.name}"
      if ci.isTheorem then theorems := theorems + 1
      for ax in (← Lean.collectAxioms ci.name) do
        unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
          throwError "unexpected transitive axiom in {ci.name}: {ax}"
    checked := checked + 1
    logInfo m!"AUDIT {moduleName}: declarations={declarations}, theorems={theorems}, standard_axioms_only=true"
  unless checked == expected.length do throwError "missing module: {checked}/{expected.length}"
