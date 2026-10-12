import RiemannGaussian.SuzukiCarryAllJetGate
import Mathlib.Tactic.Linter
import Lean.Util.CollectAxioms

/-! Focused local audit; no root or publication gate is run. -/
#lint+ in RiemannGaussian.SuzukiCarryMellinBranches
#lint+ in RiemannGaussian.SuzukiCarryExceptionalPhase
#lint+ in RiemannGaussian.SuzukiCarryPhaseScaleGate
#lint+ in RiemannGaussian.SuzukiCarrySmallCell
#lint+ in RiemannGaussian.SuzukiCarryCellCertificate
#lint+ in RiemannGaussian.SuzukiCarryRealJet
#lint+ in RiemannGaussian.SuzukiCarryExceptionalGate
#lint+ in RiemannGaussian.SuzukiCarryPhaseQuadrature
#lint+ in RiemannGaussian.SuzukiCarryPhaseEta
#lint+ in RiemannGaussian.SuzukiCarryPhaseHolomorphy
#lint+ in RiemannGaussian.SuzukiCarryPhaseLag
#lint+ in RiemannGaussian.SuzukiCarryPhaseSpectrum
#lint+ in RiemannGaussian.SuzukiCarryPhaseTransform
#lint+ in RiemannGaussian.SuzukiCarryPhaseContinuation
#lint+ in RiemannGaussian.SuzukiCarryPhaseInjectivity
#lint+ in RiemannGaussian.SuzukiCarryPhaseCosine
#lint+ in RiemannGaussian.SuzukiCarryPhaseDensity
#lint+ in RiemannGaussian.SuzukiCarryAllJetGate

open Lean Elab Command
set_option maxHeartbeats 0
run_cmd do
  let targets := #[`RiemannGaussian.SuzukiCarryMellinBranches,
    `RiemannGaussian.SuzukiCarryExceptionalPhase, `RiemannGaussian.SuzukiCarryPhaseScaleGate,
    `RiemannGaussian.SuzukiCarrySmallCell, `RiemannGaussian.SuzukiCarryCellCertificate,
    `RiemannGaussian.SuzukiCarryRealJet, `RiemannGaussian.SuzukiCarryExceptionalGate,
    `RiemannGaussian.SuzukiCarryPhaseQuadrature, `RiemannGaussian.SuzukiCarryPhaseEta,
    `RiemannGaussian.SuzukiCarryPhaseHolomorphy, `RiemannGaussian.SuzukiCarryPhaseLag,
    `RiemannGaussian.SuzukiCarryPhaseSpectrum, `RiemannGaussian.SuzukiCarryPhaseTransform,
    `RiemannGaussian.SuzukiCarryPhaseContinuation, `RiemannGaussian.SuzukiCarryPhaseInjectivity,
    `RiemannGaussian.SuzukiCarryPhaseCosine, `RiemannGaussian.SuzukiCarryPhaseDensity,
    `RiemannGaussian.SuzukiCarryAllJetGate]
  let env ← getEnv
  let mut modules : Array Json := #[]
  for target in targets do
    let mut seen := false
    let mut declarations : Nat := 0
    let mut theorems : Nat := 0
    let mut reports : Array Json := #[]
    for i in [:env.header.moduleNames.size] do
      unless env.header.moduleNames[i]! == target do continue
      seen := true
      for ci in env.header.moduleData[i]!.constants do
        declarations := declarations+1
        if ci.isAxiom then throwError "Project-defined axiom: {ci.name}"
        let dependencies ← Lean.collectAxioms ci.name
        for ax in dependencies do
          unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
            throwError "Unexpected axiom in {ci.name}: {ax}"
        if ci.isTheorem then
          theorems := theorems+1
          reports := reports.push (Json.mkObj [
            ("theorem",toJson ci.name.toString),
            ("axioms",toJson (dependencies.map Name.toString))])
    unless seen do throwError "Missing imported module: {target}"
    modules := modules.push (Json.mkObj [("module",toJson target.toString),
      ("onlyStandardAxioms",toJson true),("declarations",toJson declarations),
      ("theoremsIncludingPrivateHelpers",toJson theorems),
      ("namespaceLinters",toJson (14 : Nat)),("theoremAxioms",Json.arr reports),
      ("rootRegistered",toJson false)])
    logInfo m!"Checked {target}: {theorems} theorems; only standard axioms."
  IO.FS.createDirAll ".lake/suzuki-carry-determinant"
  IO.FS.writeFile ".lake/suzuki-carry-determinant/axioms.json"
    (Json.mkObj [("modules",Json.arr modules)]).pretty
