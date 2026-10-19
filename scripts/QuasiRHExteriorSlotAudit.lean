/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import OAI.NumberTheory.DirichletL.PrincipalSignalComparison
import OAI.NumberTheory.DirichletL.Detector.FiniteProductBounds
import scripts.QuasiRHExteriorRegionAudit
import Mathlib.Tactic.Linter
import Lean.Util.CollectAxioms

/-!
# Literal compensated Euler slots in the exterior source band

The SAME native regionSlot tends to -1 with error1440*Q^-a for
4/5<=a<=7/8, Re x>=a, Re w>=19/20, Re z>=33/200. The exact native
unit-character cancellation is retained. No contour/source transfer or
signed theta estimate is claimed.
-/
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 800000
noncomputable section
namespace OpenAIReview.ExteriorSlot
open OAI OAI.SevenEighths OAI.SevenEighths.ProbeEuler
open OAI.SevenEighths.ProbeLocal OAI.SevenEighths.PrincipalSlotEstimate
open Complex

/-- Native correction remains within one half of one throughout the band. -/
theorem band_correction_defect {a Q : ℝ} {A eta s w z : ℂ}
    (hQ : 480 ≤ Q) (hA : ‖A‖ ≤ 1) (heta : ‖eta‖ ≤ 1)
    (hs : a ≤ s.re) (ha : 4/5 ≤ a)
    (hw : 19/20 ≤ w.re) (hz : 33/200 ≤ z.re) :
    ‖unramifiedClosed Q A eta 1 s w z-1‖ ≤ 1/2 := by
  have hQ0 : 0<Q := by linarith
  have hQ1 : 1≤Q := by linarith
  calc
    _ ≤ 240*Q^(-(149/100:ℝ)) := ExteriorRegion.exterior_bound Q A eta 1 s w z
      (by linarith) hA heta (by simp) (by linarith) hw hz
    _ ≤ 240*Q^(-1:ℝ) := mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_le hQ1 (by norm_num)) (by norm_num)
    _ ≤ 1/2 := by
      rw [Real.rpow_neg_one,←div_eq_mul_inv]
      exact (div_le_iff₀ hQ0).mpr (by linarith)

/-- Actual local correction denominator is nonzero; no supplied model denominator. -/
theorem band_correction_ne_zero {a Q : ℝ} {A eta s w z : ℂ}
    (hQ : 480 ≤ Q) (hA : ‖A‖ ≤ 1) (heta : ‖eta‖ ≤ 1)
    (hs : a ≤ s.re) (ha : 4/5 ≤ a)
    (hw : 19/20 ≤ w.re) (hz : 33/200 ≤ z.re) :
    unramifiedClosed Q A eta 1 s w z≠0 := by
  have h:=band_correction_defect hQ hA heta hs ha hw hz
  intro hn
  norm_num [hn] at h

/-- The unchanged correction denominator has inverse norm at most two. -/
theorem band_correction_inverse_bound {a Q : ℝ} {A eta s w z : ℂ}
    (hQ : 480 ≤ Q) (hA : ‖A‖ ≤ 1) (heta : ‖eta‖ ≤ 1)
    (hs : a ≤ s.re) (ha : 4/5 ≤ a)
    (hw : 19/20 ≤ w.re) (hz : 33/200 ≤ z.re) :
    ‖(unramifiedClosed Q A eta 1 s w z)⁻¹‖ ≤ 2 := by
  have h:=band_correction_defect hQ hA heta hs ha hw hz
  have hn:=norm_sub_norm_le (1:ℂ) (unramifiedClosed Q A eta 1 s w z)
  rw [norm_one,norm_sub_rev] at hn
  have hl : 1/2≤‖unramifiedClosed Q A eta 1 s w z‖ := by linarith
  rw [norm_inv,inv_eq_one_div]
  exact (div_le_iff₀ (by linarith : 0<‖unramifiedClosed Q A eta 1 s w z‖)).mpr (by linarith)

theorem band_geometric_bounds {a Q : ℝ} {η s w z : ℂ}
    (hQ : 480 ≤ Q) (hη : ‖η‖ ≤ 1) (hs : a ≤ s.re)
    (haLo : 4/5 ≤ a)
    (hw : 19 / 20 ≤ w.re) (hz : 33 / 200 ≤ z.re) :
    ‖coordV Q z‖ ≤ 1 / 2 ∧ ‖coordW Q 1 w‖ ≤ 1 / 2 ∧ ‖coordD Q η 1 s‖ ≤ 1 / 2 := by
  have hQ0 : 0 < Q := by linarith
  have hQ4 : 4 ≤ Q := by linarith
  refine ⟨?_, ?_, ?_⟩
  · rw [coordV_norm Q hQ0]; exact rpow_le_half Q _ hQ4 (by linarith)
  · exact (coordW_norm_le Q hQ0 1 w (by simp)).trans (rpow_le_half Q _ hQ4 (by linarith))
  · exact (coordD_norm_le Q hQ0 η 1 s hη (by simp)).trans (rpow_le_half Q _ hQ4 (by linarith))

theorem band_marked_error_bounds {a Q : ℝ} {A η s w z : ℂ}
    (hQ : 480 ≤ Q) (hA : ‖A‖ ≤ 1) (hη : ‖η‖ = 1) (hs : a ≤ s.re)
    (haLo : 4/5 ≤ a) (haHi : a ≤ 7/8)
    (hw : 19 / 20 ≤ w.re) (hz : 33 / 200 ≤ z.re) :
    ‖regionMarked Q A η s w z + coordD Q η 1 s‖ ≤ 28 * Q ^ (-(a : ℝ)) ∧
    ‖star η * (Q : ℂ) ^ s‖ * ‖regionMarked Q A η s w z + coordD Q η 1 s‖ ≤
      28 * Q ^ (-(a : ℝ)) := by
  have hQ0 : 0 < Q := by linarith
  have hQ1 : 1 ≤ Q := by linarith
  have hQ4 : 4 ≤ Q := by linarith
  have hpow (x y : ℝ) (h : x ≤ y) : Q ^ x ≤ Q ^ y :=
    Real.rpow_le_rpow_of_exponent_le hQ1 h
  have hV := coordV_norm Q hQ0 z
  have hR := coordR_norm_le Q hQ0 A s z hA
  have hK := coordK_norm_le Q hQ1 η s w hη.le
  have hB := principal_B_norm hQ0 η s hη
  have hg := band_geometric_bounds hQ hη.le hs haLo hw hz
  have hRhalf : ‖coordR Q A s z‖ ≤ 1 / 2 :=
    hR.trans (rpow_le_half Q _ hQ4 (by linarith))
  have hW : ‖coordW Q 1 w‖ ≤ 1 := by linarith [hg.2.1]
  have hq : ‖(Q : ℂ)⁻¹‖ ≤ 1 := by
    rw [norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hQ0]
    exact inv_le_one_of_one_le₀ hQ1
  have hE := unramified_marked_error_bound (coordR Q A s z) (coordV Q z)
    (Q : ℂ)⁻¹ (coordK Q η s w) (coordW Q 1 w) (coordD Q η 1 s)
    hRhalf hg.1 hq hg.2.2
  change ‖regionMarked Q A η s w z + coordD Q η 1 s‖ ≤ _ at hE
  have hRT : ‖coordR Q A s z‖ ≤ Q ^ (-(a : ℝ)) := hR.trans (hpow _ _ (by linarith))
  have hKV : ‖coordK Q η s w‖ * ‖coordV Q z‖ ≤ Q ^ (-(a : ℝ)) := by
    calc
      _ ≤ Q ^ (1 - s.re - w.re) * Q ^ (-6 * z.re) := by rw [hV]; gcongr
      _ = Q ^ (1 - s.re - w.re - 6 * z.re) := by rw [← Real.rpow_add hQ0]; congr 1; ring
      _ ≤ _ := hpow _ _ (by linarith)
  have hBR : ‖star η * (Q : ℂ) ^ s‖ * ‖coordR Q A s z‖ ≤ Q ^ (-(a : ℝ)) := by
    calc
      _ ≤ Q ^ s.re * Q ^ (4 - 6 * s.re - 6 * z.re) := by rw [hB]; gcongr
      _ = Q ^ (4 - 5 * s.re - 6 * z.re) := by rw [← Real.rpow_add hQ0]; congr 1; ring
      _ ≤ _ := hpow _ _ (by linarith)
  have hBKV : ‖star η * (Q : ℂ) ^ s‖ * (‖coordK Q η s w‖ * ‖coordV Q z‖) ≤
      Q ^ (-(a : ℝ)) := by
    calc
      _ ≤ Q ^ s.re * (Q ^ (1 - s.re - w.re) * Q ^ (-6 * z.re)) := by rw [hB, hV]; gcongr
      _ = Q ^ (1 - w.re - 6 * z.re) := by
        rw [← Real.rpow_add hQ0, ← Real.rpow_add hQ0]; congr 1; ring
      _ ≤ _ := hpow _ _ (by linarith)
  have hE' : ‖regionMarked Q A η s w z + coordD Q η 1 s‖ ≤
      24 * ‖coordR Q A s z‖ + 4 * (‖coordK Q η s w‖ * ‖coordV Q z‖) := by
    apply hE.trans
    nlinarith [mul_le_mul_of_nonneg_left hW (norm_nonneg (coordR Q A s z))]
  constructor
  · linarith
  · have h := mul_le_mul_of_nonneg_left hE' (norm_nonneg (star η * (Q : ℂ) ^ s))
    nlinarith

theorem band_replacement_error {a Q : ℝ} {A η s w z : ℂ}
    (hQ : 480 ≤ Q) (hA : ‖A‖ ≤ 1) (hη : ‖η‖ = 1) (hs : a ≤ s.re)
    (haLo : 4/5 ≤ a) (haHi : a ≤ 7/8)
    (hw : 19 / 20 ≤ w.re) (hz : 33 / 200 ≤ z.re) :
    ‖regionReplacement Q A η s w z + unramifiedClosed Q A η 1 s w z‖ ≤
      720 * Q ^ (-(a : ℝ)) := by
  have hQ0 : 0 < Q := by linarith
  have hQ1 : 1 ≤ Q := by linarith
  have hg := band_geometric_bounds hQ hη.le hs haLo hw hz
  have hWq : coordW Q 1 w = (Q : ℂ) ^ (-w) := by simp [coordW]
  have hq : ‖(Q : ℂ) ^ (-w)‖ ≤ 1 := by rw [← hWq]; linarith [hg.2.1]
  have hW : ‖coordW Q 1 w‖ ≤ 1 := by linarith [hg.2.1]
  have hVT : ‖coordV Q z‖ ≤ Q ^ (-(a : ℝ)) := by
    rw [coordV_norm Q hQ0]; exact Real.rpow_le_rpow_of_exponent_le hQ1 (by linarith)
  have hDT : ‖coordD Q η 1 s‖ ≤ Q ^ (-(a : ℝ)) :=
    (coordD_norm_le Q hQ0 η 1 s hη.le (by simp)).trans
      (Real.rpow_le_rpow_of_exponent_le hQ1 (by linarith))
  have hE := band_marked_error_bounds hQ hA hη hs haLo haHi hw hz
  exact compensated_unit_error_bound _ _ _ _ _ _ _ (Real.rpow_nonneg hQ0.le _)
    hg.1 hW hg.2.2 hq hVT hDT hE.1 hE.2
    (principal_coord_cancellation hQ0 η s hη) hWq

theorem band_slot_error {a Q : ℝ} {A η s w z : ℂ}
    (hQ : 480 ≤ Q) (hA : ‖A‖ ≤ 1) (hη : ‖η‖ = 1) (hs : a ≤ s.re)
    (haLo : 4/5 ≤ a) (haHi : a ≤ 7/8)
    (hw : 19 / 20 ≤ w.re) (hz : 33 / 200 ≤ z.re) :
    ‖regionSlot Q A η s w z + 1‖ ≤ 1440 * Q ^ (-(a : ℝ)) := by
  have hn := band_correction_ne_zero hQ hA hη.le hs haLo hw hz
  have he := band_replacement_error hQ hA hη hs haLo haHi hw hz
  have hi := band_correction_inverse_bound hQ hA hη.le hs haLo hw hz
  have hid : regionSlot Q A η s w z + 1 =
      (regionReplacement Q A η s w z + unramifiedClosed Q A η 1 s w z) *
        (unramifiedClosed Q A η 1 s w z)⁻¹ := by
    unfold regionSlot
    field_simp
  rw [hid, norm_mul]
  calc
    _ ≤ (720 * Q ^ (-(a : ℝ))) * 2 := mul_le_mul he hi (norm_nonneg _) (by positivity)
    _ = _ := by ring


/-- Specialization is the literal original source slot, with no coefficient reset. -/
theorem source_slot_error {a Q : ℝ} {A eta s : ℂ}
    (hQ : 480 ≤ Q) (hA : ‖A‖ ≤ 1) (heta : ‖eta‖ = 1)
    (hs : a ≤ s.re) (haLo : 4/5 ≤ a) (haHi : a ≤ 7/8) :
    ‖principalSlot Q A eta s+1‖ ≤ 1440*Q^(-a) := by
  exact band_slot_error hQ hA heta hs haLo haHi (by norm_num) (by norm_num)

/-- Original region slot has the corresponding uniform norm bound. -/
theorem band_slot_norm {a Q : ℝ} {A eta s w z : ℂ}
    (hQ : 480 ≤ Q) (hA : ‖A‖ ≤ 1) (heta : ‖eta‖ = 1)
    (hs : a ≤ s.re) (haLo : 4/5 ≤ a) (haHi : a ≤ 7/8)
    (hw : 19/20 ≤ w.re) (hz : 33/200 ≤ z.re) :
    ‖regionSlot Q A eta s w z‖ ≤ 1+1440*Q^(-a) := by
  have h:=band_slot_error hQ hA heta hs haLo haHi hw hz
  have hn:=norm_sub_le (regionSlot Q A eta s w z+1) (1:ℂ)
  rw [add_sub_cancel_right,norm_one] at hn
  linarith


/-- Prime-ideal specialization retains the actual angular and target characters. -/
theorem actual_region_slot_error (eta : OAI.SevenEighths.HeckeFamily.Character)
    (P : OAI.SevenEighths.ProbePhysical.PrimeIdeal) {a : ℝ} {s w z : ℂ}
    (hQ : 480 ≤ (Ideal.absNorm P.val : ℝ))
    (hcop : IsCoprime P.val eta.modulus) (hs : a ≤ s.re)
    (haLo : 4/5 ≤ a) (haHi : a ≤ 7/8)
    (hw : 19/20 ≤ w.re) (hz : 33/200 ≤ z.re) :
    ‖regionSlot (Ideal.absNorm P.val)
      (actualAPhase eta (OAI.CompletedGauss.primaryGenerator P.val))
      (OAI.SevenEighths.HeckeFamily.idealCoeff eta P.val) s w z+1‖ ≤
      1440*(Ideal.absNorm P.val : ℝ)^(-a) := by
  exact band_slot_error hQ (actualAPhase_norm_le_one eta _)
    (PrincipalSignalComparison.idealCoeff_norm_one_of_coprime eta P.val P.property.ne_zero hcop)
    hs haLo haHi hw hz

/-- Literal marked Euler multiplier error, including its actual norm power. -/
theorem actual_multiplier_error (eta : OAI.SevenEighths.HeckeFamily.Character)
    (P : OAI.SevenEighths.ProbePhysical.PrimeIdeal) {a : ℝ} {s w z : ℂ}
    (hQ : 480 ≤ (Ideal.absNorm P.val : ℝ))
    (hcop : IsCoprime P.val eta.modulus) (hs : a ≤ s.re)
    (haLo : 4/5 ≤ a) (haHi : a ≤ 7/8)
    (hw : 19/20 ≤ w.re) (hz : 33/200 ≤ z.re) :
    ‖ProbeFiniteProductBounds.localMultiplier eta P s w z+
        (Ideal.absNorm P.val : ℂ)^(z-1)‖ ≤
      (Ideal.absNorm P.val : ℝ)^(z.re-1)*
        (1440*(Ideal.absNorm P.val : ℝ)^(-a)) := by
  have hpos : 0<(Ideal.absNorm P.val : ℝ) := by linarith
  rw [ProbeFiniteProductBounds.local_eq_regionSlot]
  rw [show (Ideal.absNorm P.val : ℂ)^(z-1)*
        regionSlot (Ideal.absNorm P.val)
          (actualAPhase eta (OAI.CompletedGauss.primaryGenerator P.val))
          (OAI.SevenEighths.HeckeFamily.idealCoeff eta P.val) s w z+
          (Ideal.absNorm P.val : ℂ)^(z-1)=
        (Ideal.absNorm P.val : ℂ)^(z-1)*
          (regionSlot (Ideal.absNorm P.val)
            (actualAPhase eta (OAI.CompletedGauss.primaryGenerator P.val))
            (OAI.SevenEighths.HeckeFamily.idealCoeff eta P.val) s w z+1) by ring]
  rw [norm_mul]
  have hc : (Ideal.absNorm P.val : ℂ)=((Ideal.absNorm P.val : ℝ):ℂ) := by simp
  rw [hc,Complex.norm_cpow_eq_rpow_re_of_pos hpos]
  simp only [sub_re,one_re]
  exact mul_le_mul_of_nonneg_left
    (actual_region_slot_error eta P hQ hcop hs haLo haHi hw hz) (Real.rpow_nonneg hpos.le _)

end OpenAIReview.ExteriorSlot
#lint+ in OpenAIReview.ExteriorSlot

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
  unless declarations>0 do throwError "Empty exterior-slot audit."
  logInfo m!"Exterior-slot audit: {declarations} declarations, {theorems} theorems; only standard axioms."
  IO.FS.createDirAll ".lake/arithmetic-operator-exterior-source-transfer-review"
  IO.FS.writeFile ".lake/arithmetic-operator-exterior-source-transfer-review/axioms.json"
    (Json.mkObj [("scope",toJson "literal native regionSlot and principalSlot error1440Q^-a for4/5<=a<=7/8; no full contour/source transfer or theta estimate"),
      ("onlyStandardAxioms",toJson true),("namespaceLinters",toJson (15:Nat)),
      ("allLocalModuleProvenance",toJson true),("declarations",toJson declarations),
      ("theoremsIncludingHelpers",toJson theorems),("details",Json.arr details)]).pretty
