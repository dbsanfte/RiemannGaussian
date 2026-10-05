import RiemannGaussian.ZetaPrimeMomentNoncoherenceStrip
import Mathlib.Tactic.Linter
import Lean.Util.CollectAxioms

/-! Local structural non-coherence gate, including private proof helpers. -/
#lint+ in RiemannGaussian.ZetaPrimeMomentNoncoherence
#lint+ in RiemannGaussian.ZetaPrimeMomentNoncoherenceStrip

open Lean Elab Command
set_option maxHeartbeats 0
run_cmd do
  let targets := #[`RiemannGaussian.ZetaPrimeMomentNoncoherence,
    `RiemannGaussian.ZetaPrimeMomentNoncoherenceStrip]
  let env ← getEnv
  let mut reports : Array Json := #[]
  for target in targets do
    let mut seen := false
    let mut declarations : Nat := 0
    let mut theorems : Nat := 0
    let mut dependenciesReport : Array Json := #[]
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
          dependenciesReport := dependenciesReport.push (Json.mkObj [
            ("theorem",toJson ci.name.toString),
            ("axioms",toJson (dependencies.map Name.toString))])
    unless seen do throwError "Missing imported module: {target}"
    logInfo m!"Checked {target}: {theorems} theorems; only standard axioms."
    reports := reports.push (Json.mkObj [("module",toJson target.toString),
      ("declarations",toJson declarations),("theoremsIncludingPrivateHelpers",toJson theorems),
      ("theoremAxioms",Json.arr dependenciesReport)])
  IO.FS.createDirAll ".lake/prime-moment-noncoherence"
  IO.FS.writeFile ".lake/prime-moment-noncoherence/axioms.json"
    (Json.mkObj [("onlyStandardAxioms",toJson true),
      ("namespaceLintersPerNamespace",toJson (14 : Nat)),("modules",Json.arr reports)]).pretty
