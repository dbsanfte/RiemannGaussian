/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import OAI.NumberTheory.DirichletL.Detector.CentralMixedMargins
import Mathlib.Tactic.Linter
import Lean.Util.CollectAxioms

/-!
# The actual native central-rate frontier

A stronger rational certificate for the existing balanced row-count envelope.
It supplies no new moment estimate, physical/theta bound or zero exclusion.
All exponents below use the literal native sourceExponent.
-/
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1200000
noncomputable section
namespace OpenAIReview.CentralRateFrontier
open OAI.SevenEighths OAI.SevenEighths.ProbeCentralExponent

/-- Exact positive-quadratic certificate for the native balanced endpoint. -/
theorem balanced_quadratic_identity (δ y : ℝ)
    (hJ : Endpoint.balanceDenominator δ y ≠ 0) :
    3240000*Endpoint.balanceDenominator δ y*(-Endpoint.balancedExponent δ y-1/5000)=
      (480000*y^3+1410000*y^2+1965000*y+765000)*δ^2+
      (-65576*y^2-942572*y-591672)*δ+(105230*y+114515) := by
  unfold Endpoint.balancedExponent Endpoint.balancedRowCount Endpoint.balancedCutoff
  field_simp
  simp only [Endpoint.balanceDenominator,Endpoint.denominator,Endpoint.primeWeight] at *
  nlinarith [hJ]

/-- The completed-square discriminant is strictly positive for every y>=0. -/
theorem balanced_discriminant_identity (y : ℝ) :
    4*(480000*y^3+1410000*y^2+1965000*y+765000)*(105230*y+114515)-
      (-65576*y^2-942572*y-591672)^2=
      16*(12358836764*y^4+43109112316*y^3+31683216167*y^2+
        6669048702*y+21259026) := by ring

/-- A stronger uniform margin for the unchanged native balanced envelope. -/
theorem balanced_native_margin {δ y : ℝ} (hδ : 0≤δ) (hδ1 : δ≤5/6)
    (hy : 0≤y) (hy1 : y≤1/2) :
    (1/5000:ℝ)≤-Endpoint.balancedExponent δ y := by
  have hJ := (Endpoint.balanceDenominator_bounds hδ hδ1 hy hy1).1
  have hJp : 0<Endpoint.balanceDenominator δ y := by linarith
  have hi := balanced_quadratic_identity δ y hJp.ne'
  have hd := balanced_discriminant_identity y
  have hA : 0<480000*y^3+1410000*y^2+1965000*y+765000 := by positivity
  have hP : 0≤16*(12358836764*y^4+43109112316*y^3+31683216167*y^2+
      6669048702*y+21259026) := by positivity
  have hs := sq_nonneg (2*(480000*y^3+1410000*y^2+1965000*y+765000)*δ+
      (-65576*y^2-942572*y-591672))
  have ht : 0≤(480000*y^3+1410000*y^2+1965000*y+765000)*δ^2+
      (-65576*y^2-942572*y-591672)*δ+(105230*y+114515) := by
    nlinarith only [hd,hP,hs,hA]
  nlinarith only [hi,ht,hJp]

/-- The native mixed row exponent with all positive auxiliary costs visible. -/
theorem native_mixed_margin (δ x Δ loss ζ μ v d : ℝ)
    (hδ : 0≤δ) (hδ1 : δ≤5/6) (hx : 0≤x) (hx1 : x≤1/2)
    (hΔ : 0≤Δ) (hΔ1 : Δ≤1/8) (hloss : 0≤loss) (hloss1 : loss≤1/32)
    (hζ : 0≤ζ) (hv : v≤13/16+ζ) (hμ : 0≤μ) (hd : d-v≤μ) :
    ProbeHighRowFamily.mixedSourceExponent ((1+δ)/2) v d
      (Endpoint.balancedRowCount δ (1/2-x)+Δ/4+loss) (δ*x) ≤
      3/16-1/5000+(13/64)*Δ+(13/16)*loss+2*ζ+(3/2)*μ := by
  let R := Endpoint.balancedRowCount δ (1/2-x)+Δ/4+loss
  have hb := balanced_native_margin hδ hδ1 (show 0≤1/2-x by linarith)
    (show 1/2-x≤1/2 by linarith)
  have hr := ProbeHighRowFamily.balanced_count_range δ x Δ loss
    hδ hδ1 hx hx1 hΔ hΔ1 hloss hloss1
  have he := relative_extend δ v R (δ*x) ζ hζ hv
    (show 0≤R+δ/2-17/50 by dsimp [R]; linarith [hr.1])
    (show R+δ/2-17/50≤2 by dsimp [R]; linarith [hr.2])
  have hs := ProbeHighRowFamily.mixed_source_slack ((1+δ)/2) v d R (δ*x) μ (3/2)
    (by dsimp [R];linarith [hr.1]) hr.2 hμ hd
  rw [original_exponent_identity] at hs
  have hid : 2*((1+δ)/2)-1=δ := by ring
  rw [hid] at hs
  unfold Endpoint.balancedExponent at hb
  unfold relativeExponent at he hs
  dsimp [R] at he hs
  linarith

/-- A sufficient source-small rate budget for the unchanged central envelope. -/
theorem central_source_budget (beta cost saving : ℝ) :
    (3/16:ℝ)-1/5000+cost≤beta-11/16-saving ↔
      (2187/2500:ℝ)+cost+saving≤beta := by constructor <;> intro h <;> linarith

/-- An admissible native bin witnessing a genuine deficit below the upper band. -/
theorem native_balanced_witness :
    Endpoint.balancedRowCount (2/5) 0=(2129/3245:ℝ) ∧
    Endpoint.balancedExponent (2/5) 0=-(41/155760:ℝ) ∧
    sourceExponent (7/10) (13/16) (Endpoint.balancedRowCount (2/5) 0) (1/5)=
      (7291/38940:ℝ) := by
  norm_num [Endpoint.balancedRowCount,Endpoint.balancedCutoff,
    Endpoint.balanceDenominator,Endpoint.denominator,Endpoint.primeWeight,
    Endpoint.balancedExponent,sourceExponent]

/-- This witness is an obstruction to that norm envelope, not a signed lower bound. -/
theorem native_witness_budget (beta loss saving : ℝ) :
    sourceExponent (7/10) (13/16) (Endpoint.balancedRowCount (2/5) 0) (1/5)+loss≤
      beta-11/16-saving ↔ (136249/155760:ℝ)+loss+saving≤beta := by
  rw [native_balanced_witness.2.2]
  constructor <;> intro h <;> linarith

end OpenAIReview.CentralRateFrontier
#lint+ in OpenAIReview.CentralRateFrontier

open Lean Elab Command
run_cmd do
  let env ← getEnv
  let mut declarations : Nat := 0
  let mut theorems : Nat := 0
  let mut reports : Array Json := #[]
  for (n,ci) in env.constants.toList do
    if env.isImportedConst n then continue
    declarations := declarations+1
    if ci.isAxiom then throwError "Project-defined axiom: {n}"
    let axs ← Lean.collectAxioms n
    for ax in axs do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "Unexpected axiom in {n}: {ax}"
    if ci.isTheorem then theorems := theorems+1
    reports := reports.push (Json.mkObj [("declaration",toJson n.toString),
      ("isTheorem",toJson ci.isTheorem),("axioms",toJson (axs.map Name.toString))])
  unless declarations>0 do throwError "Empty central-rate audit."
  logInfo m!"Central-rate audit: {declarations} declarations, {theorems} theorems; only standard axioms."
  IO.FS.createDirAll ".lake/arithmetic-operator-central-rate-frontier-gate"
  IO.FS.writeFile ".lake/arithmetic-operator-central-rate-frontier-gate/axioms.json"
    (Json.mkObj [("scope",toJson "native balanced/sourceExponent rate certificate; not a new moment estimate, signed lower bound or zero exclusion"),
      ("declarations",toJson declarations),("theoremsIncludingHelpers",toJson theorems),
      ("namespaceLinters",toJson (15:Nat)),("allLocalModuleProvenance",toJson true),
      ("onlyStandardAxioms",toJson true),("details",Json.arr reports)]).pretty
