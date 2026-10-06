import RiemannGaussian
import Mathlib.Tactic.Linter
import Lean.Util.CollectAxioms

/-! Root-import publication audit of every new declaration, including helpers. -/
#lint+ in RiemannGaussian.ZetaTwistedChebyshev
#lint+ in RiemannGaussian.SuzukiIntegerCarry
#lint+ in RiemannGaussian.SuzukiIntegerCarryMellinAudit
#lint+ in RiemannGaussian.SuzukiJoinedExcursionAudit
#lint+ in RiemannGaussian.SuzukiCarryCorrelation
#lint+ in RiemannGaussian.SuzukiCarrySourceDetector
#lint+ in RiemannGaussian.SuzukiCarryGram
#lint+ in RiemannGaussian.SuzukiCarryGramSource
#lint+ in RiemannGaussian.SuzukiCarryFejer
#lint+ in RiemannGaussian.SuzukiCarryPoleCenter
#lint+ in RiemannGaussian.SuzukiCarryPhaseCode
#lint+ in RiemannGaussian.SuzukiCarryMellinLimit
#lint+ in RiemannGaussian.SuzukiCarryMellinRate
#lint+ in RiemannGaussian.SuzukiCarryDeterminantGate
#lint+ in RiemannGaussian.SuzukiCarryPeriodicDiscrepancy
#lint+ in RiemannGaussian.SuzukiCarryPeriodicBudgetAudit
#lint+ in RiemannGaussian.SuzukiCarryMellinJet
#lint+ in RiemannGaussian.SuzukiCarryMellinBranches
#lint+ in RiemannGaussian.SuzukiCarryCollapseAudit

open Lean Elab Command
set_option maxHeartbeats 0
run_cmd do
  let targets := #[
    `RiemannGaussian.ZetaTwistedChebyshev,
    `RiemannGaussian.SuzukiIntegerCarry,
    `RiemannGaussian.SuzukiIntegerCarryMellinAudit,
    `RiemannGaussian.SuzukiJoinedExcursionAudit,
    `RiemannGaussian.SuzukiCarryCorrelation,
    `RiemannGaussian.SuzukiCarrySourceDetector,
    `RiemannGaussian.SuzukiCarryGram,
    `RiemannGaussian.SuzukiCarryGramSource,
    `RiemannGaussian.SuzukiCarryFejer,
    `RiemannGaussian.SuzukiCarryPoleCenter,
    `RiemannGaussian.SuzukiCarryPhaseCode,
    `RiemannGaussian.SuzukiCarryMellinLimit,
    `RiemannGaussian.SuzukiCarryMellinRate,
    `RiemannGaussian.SuzukiCarryDeterminantGate,
    `RiemannGaussian.SuzukiCarryPeriodicDiscrepancy,
    `RiemannGaussian.SuzukiCarryPeriodicBudgetAudit,
    `RiemannGaussian.SuzukiCarryMellinJet,
    `RiemannGaussian.SuzukiCarryMellinBranches,
    `RiemannGaussian.SuzukiCarryCollapseAudit]
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
      ("rootRegistered",toJson true)])
    logInfo m!"Checked {target}: {theorems} theorems; only standard axioms."
  IO.FS.createDirAll ".lake/suzuki-carry-publication"
  IO.FS.writeFile ".lake/suzuki-carry-publication/axioms.json"
    (Json.mkObj [("modules",Json.arr modules)]).pretty
