import RiemannGaussian
import RiemannGaussian.SemiprimeFiniteEnumerations
import RiemannGaussian.SemiprimeEnumeratedCounter
import RiemannGaussian.SemiprimeMacroFiniteEnumerations
import RiemannGaussian.SemiprimeMixedRadix
import RiemannGaussian.SemiprimeArrayOps
import RiemannGaussian.SemiprimeLocalArrayFrontend
import RiemannGaussian.SemiprimeRepresentativeExecution
import RiemannGaussian.SemiprimeFibreArrayExecution
import RiemannGaussian.SemiprimeNativeGroupExecution
import RiemannGaussian.SemiprimePacketArrayExecution
import RiemannGaussian.SemiprimeRowSelectionExecution
import RiemannGaussian.SemiprimeRowSelectionTracked
import RiemannGaussian.SemiprimeIndexedNodeCertificate
import RiemannGaussian.SemiprimeIndexedFibrePacket
import RiemannGaussian.SemiprimeExecutedNodeDesign
import RiemannGaussian.SemiprimeAcquiredHermite
import RiemannGaussian.SemiprimeNodeArrayExecution
import Lean.Util.CollectAxioms
import Mathlib.Tactic.Linter
open Lean Elab Command
#lint+ in RiemannGaussian.SemiprimeFiniteEnumerations
#lint+ in RiemannGaussian.SemiprimeEnumeratedCounter
#lint+ in RiemannGaussian.SemiprimeMacroFiniteEnumerations
#lint+ in RiemannGaussian.SemiprimeMixedRadix
#lint+ in RiemannGaussian.SemiprimeArrayOps
#lint+ in RiemannGaussian.SemiprimeLocalArrayFrontend
#lint+ in RiemannGaussian.SemiprimeRepresentativeExecution
#lint+ in RiemannGaussian.SemiprimeFibreArrayExecution
#lint+ in RiemannGaussian.SemiprimeNativeGroupExecution
#lint+ in RiemannGaussian.SemiprimePacketArrayExecution
#lint+ in RiemannGaussian.SemiprimeRowSelectionExecution
#lint+ in RiemannGaussian.SemiprimeRowSelectionTracked
#lint+ in RiemannGaussian.SemiprimeIndexedNodeCertificate
#lint+ in RiemannGaussian.SemiprimeIndexedFibrePacket
#lint+ in RiemannGaussian.SemiprimeExecutedNodeDesign
#lint+ in RiemannGaussian.SemiprimeAcquiredHermite
#lint+ in RiemannGaussian.SemiprimeNodeArrayExecution
run_cmd do
  let env ← getEnv
  let expected : List Name := [`RiemannGaussian.SemiprimeFiniteEnumerations, `RiemannGaussian.SemiprimeEnumeratedCounter, `RiemannGaussian.SemiprimeMacroFiniteEnumerations, `RiemannGaussian.SemiprimeMixedRadix, `RiemannGaussian.SemiprimeArrayOps, `RiemannGaussian.SemiprimeLocalArrayFrontend, `RiemannGaussian.SemiprimeRepresentativeExecution, `RiemannGaussian.SemiprimeFibreArrayExecution, `RiemannGaussian.SemiprimeNativeGroupExecution, `RiemannGaussian.SemiprimePacketArrayExecution, `RiemannGaussian.SemiprimeRowSelectionExecution, `RiemannGaussian.SemiprimeRowSelectionTracked, `RiemannGaussian.SemiprimeIndexedNodeCertificate, `RiemannGaussian.SemiprimeIndexedFibrePacket, `RiemannGaussian.SemiprimeExecutedNodeDesign, `RiemannGaussian.SemiprimeAcquiredHermite, `RiemannGaussian.SemiprimeNodeArrayExecution]
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
