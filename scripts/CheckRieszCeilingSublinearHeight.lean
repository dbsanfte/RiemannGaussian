import RiemannGaussian.ZetaRieszCeilingSublinearHeight
import Mathlib.Tactic.Linter
import Lean.Util.CollectAxioms

/-! Optional scoped local check; no root registration or wider gate. -/
#lint+ in RiemannGaussian.ZetaRieszCeilingSublinearHeight

open Lean Elab Command
set_option maxHeartbeats 0
run_cmd do
  let target := `RiemannGaussian.ZetaRieszCeilingSublinearHeight
  let env ← getEnv
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
      let axioms ← Lean.collectAxioms ci.name
      for ax in axioms do
        unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
          throwError "Unexpected axiom in {ci.name}: {ax}"
      if ci.isTheorem then
        theorems := theorems+1
        reports := reports.push (Json.mkObj [("theorem",toJson ci.name.toString),
          ("axioms",toJson (axioms.map Name.toString))])
  unless seen do throwError "The target module was not imported"
  logInfo m!"Checked {target}: {theorems} theorems; only standard axioms."
  IO.FS.createDirAll ".lake/riesz-ceiling-sublinear-height"
  IO.FS.writeFile ".lake/riesz-ceiling-sublinear-height/axioms.json"
    (Json.mkObj [("module",toJson target.toString),("declarations",toJson declarations),
      ("theoremsIncludingGeneratedEquations",toJson theorems),
      ("onlyStandardAxioms",toJson true),("theoremAxioms",Json.arr reports)]).pretty
