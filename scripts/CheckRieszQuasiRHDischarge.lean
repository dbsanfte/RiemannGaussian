import RiemannGaussian.ZetaRieszQuasiRHDischarge
import Mathlib.Tactic.Linter
import Lean.Util.CollectAxioms

/-! Focused local transfer audit, including generated and private declarations.
The external input remains a parameter here; upstream verification is separate. -/
#lint+ in RiemannGaussian.ZetaRieszQuasiRHDischarge

open Lean Elab Command
set_option maxHeartbeats 0
run_cmd do
  let target := `RiemannGaussian.ZetaRieszQuasiRHDischarge
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
  IO.FS.writeFile ".lake/riesz-quasi-rh-discharge/local-axioms.json"
    (Json.mkObj [("module", toJson target.toString),
      ("externalInputIsParameter", toJson true),
      ("onlyStandardAxioms", toJson true),
      ("namespaceLinters", toJson (14 : Nat)),
      ("declarations", toJson declarations),
      ("theoremsIncludingGeneratedHelpers", toJson theorems),
      ("declarationAxioms", Json.arr reports)]).pretty
