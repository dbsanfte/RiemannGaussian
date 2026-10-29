import RiemannGaussian
import RiemannGaussian.SemiprimeSourceMemoryTrace
import RiemannGaussian.SemiprimeSourceProgramErasure
import RiemannGaussian.SemiprimeSourceComparisonBits
import RiemannGaussian.SemiprimeSourceChoiceBits
import RiemannGaussian.SemiprimeSourceChoiceRefinement
import RiemannGaussian.SemiprimeSourceArrayProgramIR
import RiemannGaussian.SemiprimeSourceArrayProgramBlocks
import RiemannGaussian.SemiprimeSourceArrayProgramCompiler
import RiemannGaussian.SemiprimeSourceArrayProgramLowering
import RiemannGaussian.SemiprimeSourceArrayProgramSafe
import RiemannGaussian.SemiprimeSourceArrayCompilerSafe
import RiemannGaussian.SemiprimeSourceArrayProgramGeneration
import RiemannGaussian.SemiprimeSourceArrayProgramAcquisition
import RiemannGaussian.SemiprimeSourceArrayProgramBits
import RiemannGaussian.SemiprimeSourceInterpolationProgramBits
import RiemannGaussian.SemiprimeSourceArrayBackendBudget
import RiemannGaussian.SemiprimeSourceInterpolationProgramBudget
import RiemannGaussian.SemiprimeSourceArrayGeneratedBits
import RiemannGaussian.SemiprimeSourceInterpolationGeneratedBits
import RiemannGaussian.SemiprimeSourceInterpolationGeneratedBudget
import RiemannGaussian.SemiprimeSourceOffsetInputsCore
import RiemannGaussian.SemiprimeSourceOffsetInputsScales
import RiemannGaussian.SemiprimeSourceOffsetInputs
import RiemannGaussian.SemiprimeSourceOffsetInputsBounds
import Lean.Util.CollectAxioms
import Mathlib.Tactic.Linter
open Lean Elab Command
#lint+ in RiemannGaussian.SemiprimeSourceMemoryTrace
#lint+ in RiemannGaussian.SemiprimeSourceProgramErasure
#lint+ in RiemannGaussian.SemiprimeSourceComparisonBits
#lint+ in RiemannGaussian.SemiprimeSourceChoiceBits
#lint+ in RiemannGaussian.SemiprimeSourceChoiceRefinement
#lint+ in RiemannGaussian.SemiprimeSourceArrayProgramIR
#lint+ in RiemannGaussian.SemiprimeSourceArrayProgramBlocks
#lint+ in RiemannGaussian.SemiprimeSourceArrayProgramCompiler
#lint+ in RiemannGaussian.SemiprimeSourceArrayProgramLowering
#lint+ in RiemannGaussian.SemiprimeSourceArrayProgramSafe
#lint+ in RiemannGaussian.SemiprimeSourceArrayCompilerSafe
#lint+ in RiemannGaussian.SemiprimeSourceArrayProgramGeneration
#lint+ in RiemannGaussian.SemiprimeSourceArrayProgramAcquisition
#lint+ in RiemannGaussian.SemiprimeSourceArrayProgramBits
#lint+ in RiemannGaussian.SemiprimeSourceInterpolationProgramBits
#lint+ in RiemannGaussian.SemiprimeSourceArrayBackendBudget
#lint+ in RiemannGaussian.SemiprimeSourceInterpolationProgramBudget
#lint+ in RiemannGaussian.SemiprimeSourceArrayGeneratedBits
#lint+ in RiemannGaussian.SemiprimeSourceInterpolationGeneratedBits
#lint+ in RiemannGaussian.SemiprimeSourceInterpolationGeneratedBudget
#lint+ in RiemannGaussian.SemiprimeSourceOffsetInputsCore
#lint+ in RiemannGaussian.SemiprimeSourceOffsetInputsScales
#lint+ in RiemannGaussian.SemiprimeSourceOffsetInputs
#lint+ in RiemannGaussian.SemiprimeSourceOffsetInputsBounds
run_cmd do
  let env ← getEnv
  let expected : List Name := [`RiemannGaussian.SemiprimeSourceMemoryTrace, `RiemannGaussian.SemiprimeSourceProgramErasure, `RiemannGaussian.SemiprimeSourceComparisonBits, `RiemannGaussian.SemiprimeSourceChoiceBits, `RiemannGaussian.SemiprimeSourceChoiceRefinement, `RiemannGaussian.SemiprimeSourceArrayProgramIR, `RiemannGaussian.SemiprimeSourceArrayProgramBlocks, `RiemannGaussian.SemiprimeSourceArrayProgramCompiler, `RiemannGaussian.SemiprimeSourceArrayProgramLowering, `RiemannGaussian.SemiprimeSourceArrayProgramSafe, `RiemannGaussian.SemiprimeSourceArrayCompilerSafe, `RiemannGaussian.SemiprimeSourceArrayProgramGeneration, `RiemannGaussian.SemiprimeSourceArrayProgramAcquisition, `RiemannGaussian.SemiprimeSourceArrayProgramBits, `RiemannGaussian.SemiprimeSourceInterpolationProgramBits, `RiemannGaussian.SemiprimeSourceArrayBackendBudget, `RiemannGaussian.SemiprimeSourceInterpolationProgramBudget, `RiemannGaussian.SemiprimeSourceArrayGeneratedBits, `RiemannGaussian.SemiprimeSourceInterpolationGeneratedBits, `RiemannGaussian.SemiprimeSourceInterpolationGeneratedBudget, `RiemannGaussian.SemiprimeSourceOffsetInputsCore, `RiemannGaussian.SemiprimeSourceOffsetInputsScales, `RiemannGaussian.SemiprimeSourceOffsetInputs, `RiemannGaussian.SemiprimeSourceOffsetInputsBounds]
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
  liftIO <| IO.FS.writeFile "/tmp/semiprime-source-lowering-20261027/compiler-imports.json" (Lean.Json.arr (env.header.moduleNames.map (fun n => Lean.Json.str n.toString))).pretty
