import RiemannGaussian
import RiemannGaussian.SemiprimeSourcePackingState
import RiemannGaussian.SemiprimeSourceParityState
import RiemannGaussian.SemiprimeSourceEnumerationState
import RiemannGaussian.SemiprimeSourceMemoryBits
import RiemannGaussian.SemiprimeSourceProgramBits
import RiemannGaussian.SemiprimeSourceProgramStorage
import RiemannGaussian.SemiprimeSourceOffsetProgramBits
import RiemannGaussian.SemiprimeSourceOffsetProgramBudget
import Lean.Util.CollectAxioms
import Mathlib.Tactic.Linter
open Lean Elab Command
#lint+ in RiemannGaussian.SemiprimeSourcePackingState
#lint+ in RiemannGaussian.SemiprimeSourceParityState
#lint+ in RiemannGaussian.SemiprimeSourceEnumerationState
#lint+ in RiemannGaussian.SemiprimeSourceMemoryBits
#lint+ in RiemannGaussian.SemiprimeSourceProgramBits
#lint+ in RiemannGaussian.SemiprimeSourceProgramStorage
#lint+ in RiemannGaussian.SemiprimeSourceOffsetProgramBits
#lint+ in RiemannGaussian.SemiprimeSourceOffsetProgramBudget
run_cmd do
  let env ← getEnv
  let expected : List Name := [`RiemannGaussian.SemiprimeSourcePackingState, `RiemannGaussian.SemiprimeSourceParityState, `RiemannGaussian.SemiprimeSourceEnumerationState, `RiemannGaussian.SemiprimeSourceMemoryBits, `RiemannGaussian.SemiprimeSourceProgramBits, `RiemannGaussian.SemiprimeSourceProgramStorage, `RiemannGaussian.SemiprimeSourceOffsetProgramBits, `RiemannGaussian.SemiprimeSourceOffsetProgramBudget]
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
  liftIO <| IO.FS.writeFile "/tmp/semiprime-source-machine-20261027/compiler-imports.json" (Lean.Json.arr (env.header.moduleNames.map (fun n => Lean.Json.str n.toString))).pretty
