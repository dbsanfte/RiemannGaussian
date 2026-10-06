import RiemannGaussian.SuzukiCarryPeriodicBudgetAudit
import Mathlib.Tactic.Linter
import Lean.Util.CollectAxioms

/-! Focused local audit, including every generated/private declaration. -/
#lint+ in RiemannGaussian.SuzukiCarryPeriodicDiscrepancy
#lint+ in RiemannGaussian.SuzukiCarryPeriodicBudgetAudit

open Lean Elab Command
set_option maxHeartbeats 0
run_cmd do
  let targets := #[`RiemannGaussian.SuzukiCarryPeriodicDiscrepancy,
    `RiemannGaussian.SuzukiCarryPeriodicBudgetAudit]
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
  IO.FS.createDirAll ".lake/suzuki-carry-periodic-discrepancy"
  IO.FS.writeFile ".lake/suzuki-carry-periodic-discrepancy/axioms.json"
    (Json.mkObj [("modules",Json.arr modules)]).pretty
