import RiemannGaussian
import RiemannGaussian.SemiprimeSourceWordBankRows
import RiemannGaussian.SemiprimeSourceWordBank
import RiemannGaussian.SemiprimeSourceWordBankSemantics
import RiemannGaussian.SemiprimeSourceWordBankBounds
import RiemannGaussian.SemiprimeSourceWordBankAcquisitionBudget
import RiemannGaussian.SemiprimeSourceWordMenuOrder
import RiemannGaussian.SemiprimeSourceWordBankIndexed
import RiemannGaussian.SemiprimeSourceWordIdEnvironment
import RiemannGaussian.SemiprimeSourceWordIdEnvironmentBounds
import RiemannGaussian.SemiprimeSourceWordIdPredicate
import RiemannGaussian.SemiprimeSourceWordIdPredicateBounds
import RiemannGaussian.SemiprimeSourceWordIdCountsCore
import RiemannGaussian.SemiprimeSourceWordIdCountsBudget
import RiemannGaussian.SemiprimeSourceWordIdCounts
import RiemannGaussian.SemiprimeSourceWordIdCountsBounds
import RiemannGaussian.SemiprimeSourceWordIdCountsClock
import RiemannGaussian.SemiprimeSourceWordIdControl
import RiemannGaussian.SemiprimeSourceWordIdMetadata
import RiemannGaussian.SemiprimeSourceWordIdMenu
import RiemannGaussian.SemiprimeSourceWordIdSearch
import RiemannGaussian.SemiprimeSourceWordIdCaller
import RiemannGaussian.SemiprimeSourceWordIdSearchBudget
import RiemannGaussian.SemiprimeSourceWordIdResources
import Lean.Util.CollectAxioms
import Mathlib.Tactic.Linter
open Lean Elab Command
#lint+ in RiemannGaussian.SemiprimeSourceWordBankRows
#lint+ in RiemannGaussian.SemiprimeSourceWordBank
#lint+ in RiemannGaussian.SemiprimeSourceWordBankSemantics
#lint+ in RiemannGaussian.SemiprimeSourceWordBankBounds
#lint+ in RiemannGaussian.SemiprimeSourceWordBankAcquisitionBudget
#lint+ in RiemannGaussian.SemiprimeSourceWordMenuOrder
#lint+ in RiemannGaussian.SemiprimeSourceWordBankIndexed
#lint+ in RiemannGaussian.SemiprimeSourceWordIdEnvironment
#lint+ in RiemannGaussian.SemiprimeSourceWordIdEnvironmentBounds
#lint+ in RiemannGaussian.SemiprimeSourceWordIdPredicate
#lint+ in RiemannGaussian.SemiprimeSourceWordIdPredicateBounds
#lint+ in RiemannGaussian.SemiprimeSourceWordIdCountsCore
#lint+ in RiemannGaussian.SemiprimeSourceWordIdCountsBudget
#lint+ in RiemannGaussian.SemiprimeSourceWordIdCounts
#lint+ in RiemannGaussian.SemiprimeSourceWordIdCountsBounds
#lint+ in RiemannGaussian.SemiprimeSourceWordIdCountsClock
#lint+ in RiemannGaussian.SemiprimeSourceWordIdControl
#lint+ in RiemannGaussian.SemiprimeSourceWordIdMetadata
#lint+ in RiemannGaussian.SemiprimeSourceWordIdMenu
#lint+ in RiemannGaussian.SemiprimeSourceWordIdSearch
#lint+ in RiemannGaussian.SemiprimeSourceWordIdCaller
#lint+ in RiemannGaussian.SemiprimeSourceWordIdSearchBudget
#lint+ in RiemannGaussian.SemiprimeSourceWordIdResources
run_cmd do
  let env ← getEnv
  let expected : List Name := [`RiemannGaussian.SemiprimeSourceWordBankRows, `RiemannGaussian.SemiprimeSourceWordBank, `RiemannGaussian.SemiprimeSourceWordBankSemantics, `RiemannGaussian.SemiprimeSourceWordBankBounds, `RiemannGaussian.SemiprimeSourceWordBankAcquisitionBudget, `RiemannGaussian.SemiprimeSourceWordMenuOrder, `RiemannGaussian.SemiprimeSourceWordBankIndexed, `RiemannGaussian.SemiprimeSourceWordIdEnvironment, `RiemannGaussian.SemiprimeSourceWordIdEnvironmentBounds, `RiemannGaussian.SemiprimeSourceWordIdPredicate, `RiemannGaussian.SemiprimeSourceWordIdPredicateBounds, `RiemannGaussian.SemiprimeSourceWordIdCountsCore, `RiemannGaussian.SemiprimeSourceWordIdCountsBudget, `RiemannGaussian.SemiprimeSourceWordIdCounts, `RiemannGaussian.SemiprimeSourceWordIdCountsBounds, `RiemannGaussian.SemiprimeSourceWordIdCountsClock, `RiemannGaussian.SemiprimeSourceWordIdControl, `RiemannGaussian.SemiprimeSourceWordIdMetadata, `RiemannGaussian.SemiprimeSourceWordIdMenu, `RiemannGaussian.SemiprimeSourceWordIdSearch, `RiemannGaussian.SemiprimeSourceWordIdCaller, `RiemannGaussian.SemiprimeSourceWordIdSearchBudget, `RiemannGaussian.SemiprimeSourceWordIdResources]
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
  liftIO <| IO.FS.writeFile "/tmp/semiprime-word-bank-20261027/compiler-imports.json" (Lean.Json.arr (env.header.moduleNames.map (fun n => Lean.Json.str n.toString))).pretty
