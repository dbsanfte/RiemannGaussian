import RiemannGaussian.ZetaRieszPairPhaseRecurrence
import Mathlib.Tactic.Linter
import Lean.Util.CollectAxioms

/-! Optional focused audit; no root registration or wider gates. -/

#lint+ in RiemannGaussian.ZetaRieszPairPhaseRecurrence

open Lean Elab Command
set_option maxHeartbeats 0
run_cmd do
  let target := `RiemannGaussian.ZetaRieszPairPhaseRecurrence
  let env ← getEnv
  let mut seen := false
  let mut declarations : Nat := 0
  let mut theorems : Nat := 0
  let mut axioms : Array Json := #[]
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
        axioms := axioms.push (Json.mkObj [("theorem",toJson ci.name.toString),
          ("axioms",toJson (dependencies.map Name.toString))])
  unless seen do throwError "The target module was not imported"
  logInfo m!"Checked {theorems} theorems; only standard axioms."
  IO.FS.writeFile ".lake/riesz-pair-phase-recurrence/axioms.json"
    (Json.mkObj [("module",toJson target.toString),
      ("declarations",toJson declarations),("theoremsIncludingPrivateHelpers",toJson theorems),
      ("onlyStandardAxioms",toJson true),("theoremAxioms",Json.arr axioms)]).pretty
