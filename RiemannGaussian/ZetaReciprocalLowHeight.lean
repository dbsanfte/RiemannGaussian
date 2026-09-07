import RiemannGaussian.ZetaReciprocalGeometry

/-!
# The genuine reciprocal at the filled pole and bounded heights

The reciprocal extends through zeta's pole at one by the exact quotient
`(s - 1) / riemannZeta₁ s`. A positive compact minimum on the line of real
part one, together with the proved eta derivative bound, supplies a
nonvanishing neighbourhood for the entire low-height contour segment.
-/

open Complex Set
open scoped Classical

namespace RiemannGaussian

noncomputable section

/-- The meromorphic reciprocal with its genuine removable value zero at the pole of zeta. -/
def zetaReciprocalExtension (s : ℂ) : ℂ := (s - 1) / riemannZeta₁ s

/-- Away from the pole the extension is exactly the reciprocal of the original zeta function. -/
theorem zetaReciprocalExtension_eq_inv {s : ℂ} (hs : s ≠ 1) :
    zetaReciprocalExtension s = (riemannZeta s)⁻¹ := by
  rw [zetaReciprocalExtension, riemannZeta_eq_inv_sub_mul hs, mul_inv_rev, inv_inv]
  rw [div_eq_mul_inv, mul_comm]

/-- The extension fills zeta's pole with the reciprocal's actual removable value. -/
theorem zetaReciprocalExtension_one : zetaReciprocalExtension 1 = 0 := by
  simp [zetaReciprocalExtension]

/-- The reciprocal is analytic wherever the actual pole-removed zeta function is nonzero, including one. -/
theorem analyticAt_zetaReciprocalExtension {s : ℂ} (hs : riemannZeta₁ s ≠ 0) :
    AnalyticAt ℂ zetaReciprocalExtension s :=
  (analyticAt_id.sub analyticAt_const).div (differentiable_riemannZeta₁.analyticAt s) hs

/-- The nonvanishing line at real part one has a proved positive compact norm floor at bounded heights. -/
theorem exists_zetaReciprocalLowHeightFloor : ∃ c : ℝ, 0 < c ∧
    ∀ y : ℝ, |y| ≤ 2 → c ≤ ‖riemannZeta₁ (1 + I * y)‖ := by
  have hc : Continuous (fun y : ℝ ↦ ‖riemannZeta₁ (1 + I * y)‖) :=
    (differentiable_riemannZeta₁.continuous.comp (by fun_prop)).norm
  obtain ⟨c, hcpos, hc⟩ := (isCompact_Icc : IsCompact (Icc (-2 : ℝ) 2)).exists_forall_le'
    hc.continuousOn (a := 0) (fun y _ ↦ norm_pos_iff.mpr
      (riemannZeta₁_ne_zero_of_one_le_re (by simp)))
  exact ⟨c, hcpos, fun y hy ↦ hc y (abs_le.mp hy)⟩

/-- A fixed positive floor obtained from the actual compact line segment. -/
def zetaReciprocalLowHeightFloor : ℝ := Classical.choose exists_zetaReciprocalLowHeightFloor

/-- The selected compact floor is strictly positive. -/
theorem zetaReciprocalLowHeightFloor_pos : 0 < zetaReciprocalLowHeightFloor :=
  (Classical.choose_spec exists_zetaReciprocalLowHeightFloor).1

/-- The selected floor bounds every actual point of the low-height line segment. -/
theorem zetaReciprocalLowHeightFloor_le (y : ℝ) (hy : |y| ≤ 2) :
    zetaReciprocalLowHeightFloor ≤ ‖riemannZeta₁ (1 + I * y)‖ :=
  (Classical.choose_spec exists_zetaReciprocalLowHeightFloor).2 y hy

/-- The eta derivative estimate turns the compact floor into a fixed horizontal allowance. -/
def zetaReciprocalLowHeightWidth : ℝ := min (1 / 8) (zetaReciprocalLowHeightFloor / 33856)

/-- The low-height contour allowance is strictly positive. -/
theorem zetaReciprocalLowHeightWidth_pos : 0 < zetaReciprocalLowHeightWidth :=
  lt_min (by norm_num) (div_pos zetaReciprocalLowHeightFloor_pos (by norm_num))

/-- Half of the compact floor persists throughout the actual low-height strip. -/
theorem half_floor_le_norm_riemannZeta₁_lowHeight (sigma y : ℝ) (hy : |y| ≤ 2)
    (hsigma : |sigma - 1| ≤ zetaReciprocalLowHeightWidth) :
    zetaReciprocalLowHeightFloor / 2 ≤ ‖riemannZeta₁ ((sigma : ℂ) + I * y)‖ := by
  have hw : zetaReciprocalLowHeightWidth ≤ 1 / 8 := min_le_left _ _
  have hc : zetaReciprocalLowHeightWidth ≤ zetaReciprocalLowHeightFloor / 33856 := min_le_right _ _
  have hs := abs_le.mp (hsigma.trans hw)
  have hdiff := norm_riemannZeta₁_sub_le_etaStrip_horizontal y (u := 1) (v := sigma)
    (by constructor <;> norm_num) ⟨by linarith [hs.1], by linarith [hs.2]⟩
  have hcoef : 32 * (|y| + 21) ^ 2 ≤ (16928 : ℝ) := by
    calc
      _ ≤ 32 * (2 + 21 : ℝ) ^ 2 := by gcongr
      _ = _ := by norm_num
  have hdiff' : ‖riemannZeta₁ ((sigma : ℂ) + I * y) - riemannZeta₁ (1 + I * y)‖ ≤
      zetaReciprocalLowHeightFloor / 2 := by
    apply hdiff.trans
    have h := mul_le_mul_of_nonneg_right hcoef (abs_nonneg (sigma - 1))
    have h' := mul_le_mul_of_nonneg_left (hsigma.trans hc) (by norm_num : (0 : ℝ) ≤ 16928)
    linarith
  have hn := norm_sub_norm_le (riemannZeta₁ (1 + I * y)) (riemannZeta₁ ((sigma : ℂ) + I * y))
  rw [norm_sub_rev] at hn
  linarith [zetaReciprocalLowHeightFloor_le y hy]

/-- The genuine reciprocal is uniformly bounded on the whole low-height shifted strip, including the filled pole. -/
theorem norm_zetaReciprocalExtension_le_lowHeight {s : ℂ} (hy : |s.im| ≤ 2)
    (hs : |s.re - 1| ≤ zetaReciprocalLowHeightWidth) :
    ‖zetaReciprocalExtension s‖ ≤ 6 / zetaReciprocalLowHeightFloor := by
  have he : ((s.re : ℝ) : ℂ) + I * s.im = s := by
    simpa only [mul_comm I] using Complex.re_add_im s
  have hfloor := half_floor_le_norm_riemannZeta₁_lowHeight s.re s.im hy hs
  rw [he] at hfloor
  have hc : 0 < zetaReciprocalLowHeightFloor := zetaReciprocalLowHeightFloor_pos
  have hn : ‖s - 1‖ ≤ 3 := by
    have h := Complex.norm_le_abs_re_add_abs_im (s - 1)
    simp only [Complex.sub_re, Complex.one_re, Complex.sub_im, Complex.one_im, sub_zero] at h
    have hw : zetaReciprocalLowHeightWidth ≤ 1 / 8 := min_le_left _ _
    linarith
  rw [zetaReciprocalExtension, norm_div]
  calc
    _ ≤ 3 / ‖riemannZeta₁ s‖ := div_le_div_of_nonneg_right hn (norm_nonneg _)
    _ ≤ 3 / (zetaReciprocalLowHeightFloor / 2) :=
      div_le_div_of_nonneg_left (by norm_num) (by positivity) hfloor
    _ = _ := by ring

end

end RiemannGaussian
