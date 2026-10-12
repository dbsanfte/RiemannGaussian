import RiemannGaussian.ZetaQuasiRHProbeCalibration
import Mathlib.Tactic.Linter
import Lean.Util.CollectAxioms

/-! Focused exponent preflight. This does not certify or import the
upstream arithmetic estimates. Every private/generated declaration is audited. -/
#lint+ in RiemannGaussian.ZetaQuasiRHProbeCalibration

open Lean Elab Command
set_option maxHeartbeats 0
run_cmd do
  let target := `RiemannGaussian.ZetaQuasiRHProbeCalibration
  let env ← getEnv
  let mut seen := false
  let mut declarations : Nat := 0
  let mut theorems : Nat := 0
  let mut reports : Array Json := #[]
  for i in [:env.header.moduleNames.size] do
    unless env.header.moduleNames[i]! == target do continue
    seen := true
    for ci in env.header.moduleData[i]!.constants do
      declarations := declarations + 1
      if ci.isAxiom then throwError "Project-defined axiom: {ci.name}"
      let dependencies ← Lean.collectAxioms ci.name
      for ax in dependencies do
        unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
          throwError "Unexpected axiom in {ci.name}: {ax}"
      if ci.isTheorem then theorems := theorems + 1
      reports := reports.push (Json.mkObj [
        ("declaration", toJson ci.name.toString),
        ("isTheorem", toJson ci.isTheorem),
        ("axioms", toJson (dependencies.map Name.toString))])
  unless seen do throwError "Missing imported module: {target}"
  logInfo m!"Checked {target}: {declarations} declarations, {theorems} theorems; only standard axioms."
  IO.FS.createDirAll ".lake/riesz-quasi-rh-discharge"
  IO.FS.writeFile ".lake/riesz-quasi-rh-discharge/calibration-axioms.json"
    (Json.mkObj [("module", toJson target.toString),
      ("scope", toJson "retained low formula and nonnegative fully rescaled lengths only"),
      ("upstreamArithmeticEstimatesImported", toJson false),
      ("onlyStandardAxioms", toJson true),
      ("namespaceLinters", toJson (14 : Nat)),
      ("declarations", toJson declarations),
      ("theoremsIncludingGeneratedHelpers", toJson theorems),
      ("declarationAxioms", Json.arr reports)]).pretty
