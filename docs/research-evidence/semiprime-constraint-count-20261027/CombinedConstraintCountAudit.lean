import RiemannGaussian
import RiemannGaussian.SemiprimeSourceCountPowers
import RiemannGaussian.SemiprimeSourceHeadFibres
import RiemannGaussian.SemiprimeSourceHeadCountFormula
import RiemannGaussian.SemiprimeSourceIncidenceNamespaces
import RiemannGaussian.SemiprimeSourceIncidencePairAverage
import RiemannGaussian.SemiprimeSourceIncidenceCountFormula
import RiemannGaussian.SemiprimeSourceHeadCountBits
import RiemannGaussian.SemiprimeSourceHeadCountBitsBounds
import RiemannGaussian.SemiprimeSourceIncidenceCountBits
import RiemannGaussian.SemiprimeSourceIncidenceCountBitsBounds
import RiemannGaussian.SemiprimeSourceClassifiedWeights
import RiemannGaussian.SemiprimeSourceClassifiedCounts
import RiemannGaussian.SemiprimeSourceClassifiedCountsClock
import RiemannGaussian.SemiprimeSourceClassifiedSearch
import RiemannGaussian.SemiprimeSourceClassifiedCaller
import RiemannGaussian.SemiprimeSourceClassifiedSearchBudget
import RiemannGaussian.SemiprimeSourceClassifiedResources
import Lean.Util.CollectAxioms
import Mathlib.Tactic.Linter
open Lean Elab Command
#lint+ in RiemannGaussian.SemiprimeSourceCountPowers
#lint+ in RiemannGaussian.SemiprimeSourceHeadFibres
#lint+ in RiemannGaussian.SemiprimeSourceHeadCountFormula
#lint+ in RiemannGaussian.SemiprimeSourceIncidenceNamespaces
#lint+ in RiemannGaussian.SemiprimeSourceIncidencePairAverage
#lint+ in RiemannGaussian.SemiprimeSourceIncidenceCountFormula
#lint+ in RiemannGaussian.SemiprimeSourceHeadCountBits
#lint+ in RiemannGaussian.SemiprimeSourceHeadCountBitsBounds
#lint+ in RiemannGaussian.SemiprimeSourceIncidenceCountBits
#lint+ in RiemannGaussian.SemiprimeSourceIncidenceCountBitsBounds
#lint+ in RiemannGaussian.SemiprimeSourceClassifiedWeights
#lint+ in RiemannGaussian.SemiprimeSourceClassifiedCounts
#lint+ in RiemannGaussian.SemiprimeSourceClassifiedCountsClock
#lint+ in RiemannGaussian.SemiprimeSourceClassifiedSearch
#lint+ in RiemannGaussian.SemiprimeSourceClassifiedCaller
#lint+ in RiemannGaussian.SemiprimeSourceClassifiedSearchBudget
#lint+ in RiemannGaussian.SemiprimeSourceClassifiedResources
run_cmd do
  let env ← getEnv
  let expected : List Name := [`RiemannGaussian.SemiprimeSourceCountPowers, `RiemannGaussian.SemiprimeSourceHeadFibres, `RiemannGaussian.SemiprimeSourceHeadCountFormula, `RiemannGaussian.SemiprimeSourceIncidenceNamespaces, `RiemannGaussian.SemiprimeSourceIncidencePairAverage, `RiemannGaussian.SemiprimeSourceIncidenceCountFormula, `RiemannGaussian.SemiprimeSourceHeadCountBits, `RiemannGaussian.SemiprimeSourceHeadCountBitsBounds, `RiemannGaussian.SemiprimeSourceIncidenceCountBits, `RiemannGaussian.SemiprimeSourceIncidenceCountBitsBounds, `RiemannGaussian.SemiprimeSourceClassifiedWeights, `RiemannGaussian.SemiprimeSourceClassifiedCounts, `RiemannGaussian.SemiprimeSourceClassifiedCountsClock, `RiemannGaussian.SemiprimeSourceClassifiedSearch, `RiemannGaussian.SemiprimeSourceClassifiedCaller, `RiemannGaussian.SemiprimeSourceClassifiedSearchBudget, `RiemannGaussian.SemiprimeSourceClassifiedResources]
  let mut checked : Nat := 0
  let mut totalDeclarations : Nat := 0
  let mut totalTheorems : Nat := 0
  for h : i in [0:env.header.moduleNames.size] do
    let moduleName := env.header.moduleNames[i]
    unless moduleName ∈ expected do continue
    let mut declarations : Nat := 0
    let mut theorems : Nat := 0
    for ci in env.header.moduleData[i]!.constants do
      declarations := declarations+1
      if ci.isAxiom then throwError "project-defined axiom: {ci.name}"
      if ci.isTheorem then theorems := theorems+1
      for ax in (← Lean.collectAxioms ci.name) do
        unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
          throwError "unexpected transitive axiom in {ci.name}: {ax}"
    checked := checked+1
    totalDeclarations := totalDeclarations+declarations
    totalTheorems := totalTheorems+theorems
    logInfo m!"AUDIT {moduleName}: declarations={declarations}, theorems={theorems}, standard_axioms_only=true"
  unless checked == expected.length do throwError "missing module: {checked}/{expected.length}"
  logInfo m!"TOTAL modules={checked}, declarations={totalDeclarations}, theorems={totalTheorems}, standard_axioms_only=true"
  liftIO <| IO.FS.writeFile "/tmp/semiprime-constraint-count-20261027/compiler-imports.json" (Lean.Json.arr (env.header.moduleNames.map (fun n => Lean.Json.str n.toString))).pretty
