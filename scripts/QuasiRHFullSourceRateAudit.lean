/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import OAI.NumberTheory.DirichletL.Detector.CentralExponent
import Mathlib.Tactic.Linter
import Lean.Util.CollectAxioms

/-!
# Actual native floor-envelope transfer boundary

This is the exponent in actual_normalized_floor_cube, not a lower bound
on any actual signed covariance. Its existing uniform envelope cannot
remove the floor population throughout the proposed83/96 source band.
Retaining that population in the exact full transport remains possible.
-/
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 800000
noncomputable section
namespace OpenAIReview.FullSourceRate
open OAI.SevenEighths.ProbeCentralExponent

/-- The native floor exponent attains the currently stated endpoint exactly. -/
theorem native_floor_endpoint :
    sourceExponent (51/100) (13/16) 1 (1/100)=(109/600:ℝ) := by
  norm_num [sourceExponent]

/-- The7/1200 gap in the native floor bound has no unused numerical slack. -/
theorem native_floor_margin_exact :
    (3/16:ℝ)-sourceExponent (51/100) (13/16) 1 (1/100)=7/1200 := by
  rw [native_floor_endpoint]
  norm_num

/-- Exact necessary and sufficient budget for this envelope to meet the source. -/
theorem native_floor_source_budget (beta loss saving : ℝ) :
    sourceExponent (51/100) (13/16) 1 (1/100)+loss≤beta-11/16-saving ↔
      (1043/1200:ℝ)+loss+saving≤beta := by
  rw [native_floor_endpoint]
  constructor <;> intro h <;> linarith

/-- Any positive saving with this envelope requires beta strictly beyond1043/1200. -/
theorem native_floor_requires_larger_beta {beta loss saving : ℝ}
    (hloss : 0≤loss) (hsaving : 0<saving)
    (h : sourceExponent (51/100) (13/16) 1 (1/100)+loss≤beta-11/16-saving) :
    (1043/1200:ℝ)<beta := by
  have hh:=(native_floor_source_budget beta loss saving).mp h
  linarith

/-- Existing floor deletion leaves a nonempty portion of the proposed source band. -/
theorem native_floor_lower_band_obstruction {beta loss saving : ℝ}
    (hbeta : beta≤1043/1200) (hloss : 0≤loss) (hsaving : 0<saving) :
    ¬sourceExponent (51/100) (13/16) 1 (1/100)+loss≤beta-11/16-saving := by
  intro h
  exact (not_lt_of_ge hbeta) (native_floor_requires_larger_beta hloss hsaving h)

/-- At the continuous threshold the actual native floor envelope exceeds source. -/
theorem native_floor_continuous_gap :
    sourceExponent (51/100) (13/16) 1 (1/100)-((83/96:ℝ)-11/16)=11/2400 := by
  rw [native_floor_endpoint]
  norm_num

/-- The same gap is the difference between the two source thresholds. -/
theorem source_threshold_gap : (1043/1200:ℝ)-83/96=11/2400 := by norm_num

/-- Correct sub7/8 budget for the already proved floor exponent. -/
theorem corrected_floor_budget (beta loss saving : ℝ) :
    loss+saving+(7/8-beta)≤7/1200 ↔
      sourceExponent (51/100) (13/16) 1 (1/100)+loss≤beta-11/16-saving := by
  rw [native_floor_source_budget]
  constructor <;> intro h <;> linarith

end OpenAIReview.FullSourceRate
#lint+ in OpenAIReview.FullSourceRate

open Lean Elab Command
run_cmd do
  let env ← getEnv
  let mut declarations : Nat := 0
  let mut theorems : Nat := 0
  let mut details : Array Json := #[]
  for (n,ci) in env.constants.toList do
    if env.isImportedConst n then continue
    declarations := declarations+1
    if ci.isAxiom then throwError "Project-defined axiom: {n}"
    let axs ← Lean.collectAxioms n
    for ax in axs do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "Unexpected axiom in {n}: {ax}"
    if ci.isTheorem then theorems := theorems+1
    details := details.push (Json.mkObj [("declaration",toJson n.toString),
      ("isTheorem",toJson ci.isTheorem),("axioms",toJson (axs.map Name.toString))])
  unless declarations>0 do throwError "Empty full-source-rate audit."
  logInfo m!"Full-source-rate audit: {declarations} declarations, {theorems} theorems; only standard axioms."
  IO.FS.createDirAll ".lake/arithmetic-operator-full-source-transfer-gate"
  IO.FS.writeFile ".lake/arithmetic-operator-full-source-transfer-gate/axioms.json"
    (Json.mkObj [("scope",toJson "exact native sourceExponent floor envelope and necessary amended source budget; not an actual signed lower bound or whole-route impossibility"),
      ("onlyStandardAxioms",toJson true),("namespaceLinters",toJson (15:Nat)),
      ("allLocalModuleProvenance",toJson true),("declarations",toJson declarations),
      ("theoremsIncludingHelpers",toJson theorems),("details",Json.arr details)]).pretty
