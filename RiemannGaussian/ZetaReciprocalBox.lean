import RiemannGaussian.ZetaLocalReciprocal
import RiemannGaussian.ZetaReciprocalLowHeight

/-!
# A nonvanishing rectangle and quantitative reciprocal bound

The complete canonical estimate controls every high ordinate. The compact
low-height floor closes the middle of the contour, including zeta's pole.
One proved positive width and one finite bound cover the entire rectangle
crossing the line of real part one.
-/

open Complex Set
open scoped Classical

namespace RiemannGaussian

noncomputable section

/-- The actual height-dependent reciprocal bound from the complete local factorization. -/
def zetaReciprocalHeightBound (y : ℝ) : ℝ :=
  16 * (|y| + 1) * Real.exp (40 * localZetaLogHeight y +
    32 * localZetaLogHeight y * Real.log (1000000 * localZetaLogHeight y))

/-- The reciprocal height bound is strictly positive. -/
theorem zetaReciprocalHeightBound_pos (y : ℝ) : 0 < zetaReciprocalHeightBound y := by
  unfold zetaReciprocalHeightBound
  positivity

/-- The logarithmic height increases with absolute ordinate. -/
theorem localZetaLogHeight_mono_abs {y t : ℝ} (h : |y| ≤ |t|) :
    localZetaLogHeight y ≤ localZetaLogHeight t :=
  Real.log_le_log (by positivity) (by linarith)

/-- The reciprocal strip allowance decreases with absolute ordinate. -/
theorem zetaReciprocalStripWidth_antitone_abs {y t : ℝ} (h : |y| ≤ |t|) :
    zetaReciprocalStripWidth t ≤ zetaReciprocalStripWidth y := by
  have hL : 0 < localZetaLogHeight y := by linarith [two_lt_localZetaLogHeight y]
  exact one_div_le_one_div_of_le (by positivity) (mul_le_mul_of_nonneg_left
    (localZetaLogHeight_mono_abs h) (by norm_num))

/-- The entire reciprocal envelope increases with absolute ordinate. -/
theorem zetaReciprocalHeightBound_mono_abs {y t : ℝ} (h : |y| ≤ |t|) :
    zetaReciprocalHeightBound y ≤ zetaReciprocalHeightBound t := by
  have hL := localZetaLogHeight_mono_abs h
  have hyL := two_lt_localZetaLogHeight y
  have htL := two_lt_localZetaLogHeight t
  have hylog : 0 ≤ Real.log (1000000 * localZetaLogHeight y) := Real.log_nonneg (by linarith)
  unfold zetaReciprocalHeightBound
  gcongr

/-- At every sufficiently high ordinate the actual reciprocal is bounded throughout the shifted horizontal segment. -/
theorem norm_zetaReciprocalExtension_le_height {s : ℂ} (hy : 2 ≤ |s.im|)
    (hslo : 1 - zetaReciprocalStripWidth s.im ≤ s.re) (hshi : s.re ≤ 3 / 2) :
    ‖zetaReciprocalExtension s‖ ≤ zetaReciprocalHeightBound s.im := by
  let z : ℂ := ((s.re - 3 / 2 : ℝ) : ℂ)
  have hzn : ‖z‖ ≤ 5 / 8 := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonpos (by linarith)]
    linarith [zetaReciprocalStripWidth_le_eighth s.im]
  have hzr : -(1 / 2 : ℝ) - zetaReciprocalStripWidth s.im ≤ z.re := by
    dsimp [z]
    linarith
  have he : 3 / 2 + I * (s.im : ℂ) + z = s := by
    apply Complex.ext <;> simp [z]
  have hf : localZetaPoleRemoved s.im z ≠ 0 := by
    rw [localZetaPoleRemoved, he]
    exact riemannZeta₁_ne_zero_in_reciprocalStrip (by linarith) hslo
  have hinv := norm_inv_localZetaPoleRemoved_le s.im hy hzn hzr hf
  rw [localZetaPoleRemoved, he] at hinv
  have hw : 2 / zetaReciprocalStripWidth s.im = 1000000 * localZetaLogHeight s.im := by
    simp only [zetaReciprocalStripWidth, div_eq_mul_inv, one_mul, inv_inv]
    ring
  rw [hw] at hinv
  have hn : ‖s - 1‖ ≤ |s.im| + 1 := by
    have h := Complex.norm_le_abs_re_add_abs_im (s - 1)
    simp only [Complex.sub_re, Complex.one_re, Complex.sub_im, Complex.one_im, sub_zero] at h
    have ha : |s.re - 1| ≤ 1 := abs_le.mpr ⟨by linarith [zetaReciprocalStripWidth_le_eighth s.im], by linarith⟩
    linarith
  rw [zetaReciprocalExtension, div_eq_mul_inv, norm_mul]
  apply (mul_le_mul hn hinv (norm_nonneg _) (by positivity)).trans_eq
  unfold zetaReciprocalHeightBound
  ring

/-- A common positive contour width that also covers the low-height segment. -/
def zetaReciprocalContourWidth (T : ℝ) : ℝ := min zetaReciprocalLowHeightWidth (zetaReciprocalStripWidth T)

/-- The entire contour has positive width at every height. -/
theorem zetaReciprocalContourWidth_pos (T : ℝ) : 0 < zetaReciprocalContourWidth T :=
  lt_min zetaReciprocalLowHeightWidth_pos (zetaReciprocalStripWidth_pos T)

/-- The contour width stays within the proved geometric neighbourhood. -/
theorem zetaReciprocalContourWidth_le_eighth (T : ℝ) : zetaReciprocalContourWidth T ≤ 1 / 8 :=
  (min_le_right _ _).trans (zetaReciprocalStripWidth_le_eighth T)

/-- Beyond a fixed proved threshold, the full contour has the explicit reciprocal-logarithm width. -/
theorem zetaReciprocalContourWidth_eq_stripWidth {T : ℝ} (hT : 2 ≤ T)
    (hlarge : Real.exp (1 / (500000 * zetaReciprocalLowHeightWidth)) ≤ T) :
    zetaReciprocalContourWidth T = zetaReciprocalStripWidth T := by
  have hL : 1 / (500000 * zetaReciprocalLowHeightWidth) ≤ localZetaLogHeight T := by
    have h := Real.log_le_log (Real.exp_pos _) (hlarge.trans (show T ≤ T + 22 by linarith))
    rw [Real.log_exp] at h
    simpa only [localZetaLogHeight, abs_of_nonneg (by linarith [hT] : 0 ≤ T)] using h
  have hw := zetaReciprocalLowHeightWidth_pos
  have hLT : 0 < localZetaLogHeight T := by linarith [two_lt_localZetaLogHeight T]
  have hprod := (div_le_iff₀ (by positivity : 0 < 500000 * zetaReciprocalLowHeightWidth)).mp hL
  apply min_eq_right
  unfold zetaReciprocalStripWidth
  rw [div_le_iff₀ (by positivity)]
  nlinarith

/-- The common finite reciprocal bound for both the compact middle and high ordinates. -/
def zetaReciprocalContourBound (T : ℝ) : ℝ :=
  max (6 / zetaReciprocalLowHeightFloor) (zetaReciprocalHeightBound T)

/-- The common reciprocal bound is positive. -/
theorem zetaReciprocalContourBound_pos (T : ℝ) : 0 < zetaReciprocalContourBound T :=
  (zetaReciprocalHeightBound_pos T).trans_le (le_max_right _ _)

/-- The actual pole-removed function is nonzero on the entire closed rectangle crossing real part one. -/
theorem riemannZeta₁_ne_zero_on_reciprocalBox {T : ℝ} {s : ℂ}
    (hre : |s.re - 1| ≤ zetaReciprocalContourWidth T) (him : |s.im| ≤ T) : riemannZeta₁ s ≠ 0 := by
  by_cases hy : |s.im| ≤ 2
  · have hs := hre.trans (min_le_left _ _)
    have hfloor := half_floor_le_norm_riemannZeta₁_lowHeight s.re s.im hy hs
    have he : ((s.re : ℝ) : ℂ) + I * s.im = s := by
      simpa only [mul_comm I] using Complex.re_add_im s
    rw [he] at hfloor
    exact norm_pos_iff.mp ((div_pos zetaReciprocalLowHeightFloor_pos (by norm_num)).trans_le hfloor)
  · have hw := zetaReciprocalStripWidth_antitone_abs (y := s.im) (t := T)
      (by simpa only [abs_of_nonneg ((abs_nonneg s.im).trans him)] using him)
    have hs := (abs_le.mp hre).1
    have hc : zetaReciprocalContourWidth T ≤ zetaReciprocalStripWidth T := min_le_right _ _
    exact riemannZeta₁_ne_zero_in_reciprocalStrip (by linarith) (by linarith)

/-- One finite proved constant bounds the genuine reciprocal throughout the whole shifted rectangle. -/
theorem norm_zetaReciprocalExtension_le_on_box {T : ℝ} {s : ℂ}
    (hre : |s.re - 1| ≤ zetaReciprocalContourWidth T) (him : |s.im| ≤ T) :
    ‖zetaReciprocalExtension s‖ ≤ zetaReciprocalContourBound T := by
  by_cases hy : |s.im| ≤ 2
  · exact (norm_zetaReciprocalExtension_le_lowHeight hy (hre.trans (min_le_left _ _))).trans (le_max_left _ _)
  · have ht : |s.im| ≤ |T| := by simpa only [abs_of_nonneg ((abs_nonneg s.im).trans him)] using him
    have hw := zetaReciprocalStripWidth_antitone_abs ht
    have hs := abs_le.mp hre
    have hc : zetaReciprocalContourWidth T ≤ zetaReciprocalStripWidth T := min_le_right _ _
    have hb := norm_zetaReciprocalExtension_le_height (s := s) (by linarith)
      (by linarith [hs.1]) (by linarith [hs.2, zetaReciprocalContourWidth_le_eighth T])
    exact hb.trans ((zetaReciprocalHeightBound_mono_abs ht).trans (le_max_right _ _))

/-- The reciprocal is analytic near every point of the whole closed contour rectangle, with zero avoidance discharged. -/
theorem analyticAt_zetaReciprocalExtension_on_box {T : ℝ} {s : ℂ}
    (hre : |s.re - 1| ≤ zetaReciprocalContourWidth T) (him : |s.im| ≤ T) :
    AnalyticAt ℂ zetaReciprocalExtension s :=
  analyticAt_zetaReciprocalExtension (riemannZeta₁_ne_zero_on_reciprocalBox hre him)

end

end RiemannGaussian
