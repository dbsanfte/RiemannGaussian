import RiemannGaussian
import RiemannGaussian.SemiprimeRationalBits
import RiemannGaussian.SemiprimeDotBits
import RiemannGaussian.SemiprimeCounterPacketHeight
import RiemannGaussian.SemiprimeFibreAccumulatorHeight
import RiemannGaussian.SemiprimeLocalPrefixHeight
import RiemannGaussian.SemiprimeHermiteArrayHeight
import RiemannGaussian.SemiprimeMacroEntryExecution
import RiemannGaussian.SemiprimeMacroEntryBitPrimitives
import RiemannGaussian.SemiprimeMacroEntryBitCheck
import RiemannGaussian.SemiprimeSubdividedEntry
import RiemannGaussian.SemiprimePublicConstructedCount
import Lean.Util.CollectAxioms
import Mathlib.Tactic.Linter

open Lean Elab Command

#lint+ in RiemannGaussian.SemiprimeRationalBits
#lint+ in RiemannGaussian.SemiprimeDotBits
#lint+ in RiemannGaussian.SemiprimeCounterPacketHeight
#lint+ in RiemannGaussian.SemiprimeFibreAccumulatorHeight
#lint+ in RiemannGaussian.SemiprimeLocalPrefixHeight
#lint+ in RiemannGaussian.SemiprimeHermiteArrayHeight
#lint+ in RiemannGaussian.SemiprimeMacroEntryExecution
#lint+ in RiemannGaussian.SemiprimeMacroEntryBitPrimitives
#lint+ in RiemannGaussian.SemiprimeMacroEntryBitCheck
#lint+ in RiemannGaussian.SemiprimeSubdividedEntry
#lint+ in RiemannGaussian.SemiprimePublicConstructedCount

run_cmd do
  let env ← getEnv
  let expected : List Name := [`RiemannGaussian.SemiprimeRationalBits, `RiemannGaussian.SemiprimeDotBits, `RiemannGaussian.SemiprimeCounterPacketHeight, `RiemannGaussian.SemiprimeFibreAccumulatorHeight, `RiemannGaussian.SemiprimeLocalPrefixHeight, `RiemannGaussian.SemiprimeHermiteArrayHeight, `RiemannGaussian.SemiprimeMacroEntryExecution, `RiemannGaussian.SemiprimeMacroEntryBitPrimitives, `RiemannGaussian.SemiprimeMacroEntryBitCheck, `RiemannGaussian.SemiprimeSubdividedEntry, `RiemannGaussian.SemiprimePublicConstructedCount]
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
