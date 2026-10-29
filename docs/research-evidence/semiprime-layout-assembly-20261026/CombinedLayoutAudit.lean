import RiemannGaussian
import RiemannGaussian.SemiprimeSourceLayout
import RiemannGaussian.SemiprimeSourceLayoutHeight
import RiemannGaussian.SemiprimeSourceLayoutRate
import RiemannGaussian.SemiprimeLayoutCertificates
import RiemannGaussian.SemiprimeLayoutSelection
import RiemannGaussian.SemiprimeMacroGraph
import RiemannGaussian.SemiprimeConstructedCounter
import Lean.Util.CollectAxioms
import Mathlib.Tactic.Linter

open Lean Elab Command
#lint+ in RiemannGaussian.SemiprimeSourceLayout
#lint+ in RiemannGaussian.SemiprimeSourceLayoutHeight
#lint+ in RiemannGaussian.SemiprimeSourceLayoutRate
#lint+ in RiemannGaussian.SemiprimeLayoutCertificates
#lint+ in RiemannGaussian.SemiprimeLayoutSelection
#lint+ in RiemannGaussian.SemiprimeMacroGraph
#lint+ in RiemannGaussian.SemiprimeConstructedCounter

run_cmd do
  let env ← getEnv
  let expected : List Name := [`RiemannGaussian.SemiprimeSourceLayout, `RiemannGaussian.SemiprimeSourceLayoutHeight, `RiemannGaussian.SemiprimeSourceLayoutRate, `RiemannGaussian.SemiprimeLayoutCertificates, `RiemannGaussian.SemiprimeLayoutSelection, `RiemannGaussian.SemiprimeMacroGraph, `RiemannGaussian.SemiprimeConstructedCounter]
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
