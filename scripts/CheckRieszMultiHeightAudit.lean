import RiemannGaussian.ZetaRieszMultiHeightAudit
import Mathlib.Tactic.Linter
import Lean.Util.CollectAxioms

/-! Scoped mathematical gate; optional numerical controls are not dependencies. -/
#lint+ in RiemannGaussian.ZetaRieszMultiHeightAudit

open Lean Elab Command
set_option maxHeartbeats 0
run_cmd do
  let target := `RiemannGaussian.ZetaRieszMultiHeightAudit
  let env ← getEnv
  let mut seen := false
  let mut declarations : Nat := 0
  let mut theorems : Nat := 0
  let mut report : Array Json := #[]
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
        report := report.push (Json.mkObj [("theorem",toJson ci.name.toString),
          ("axioms",toJson (dependencies.map Name.toString))])
  unless seen do throwError "The target module was not imported"
  logInfo m!"Checked {target}: {theorems} theorems; only standard axioms."
  IO.FS.createDirAll ".lake/riesz-multi-height"
  IO.FS.writeFile ".lake/riesz-multi-height/axioms.json"
    (Json.mkObj [("module",toJson target.toString),
      ("declarations",toJson declarations),("theoremsIncludingPrivateHelpers",toJson theorems),
      ("namespaceLinters",toJson (14 : Nat)),("onlyStandardAxioms",toJson true),
      ("theoremAxioms",Json.arr report)]).pretty
