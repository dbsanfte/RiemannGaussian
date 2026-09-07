import RiemannGaussian.GaussianMoebiusScaleConstants

/-!
# Unit heat time and logarithmic arithmetic height

Choose contour height equal to the logarithmic arithmetic parameter and
keep the heat time equal to one. The actual mass bound and all three
contour contributions then give a fixed squared-logarithm envelope above
the strictly smaller left-line exponent. All constants are independent
of the arithmetic scale.
-/

namespace RiemannGaussian

noncomputable section

/-- At unit heat time and height equal to the arithmetic logarithm, all contour errors fit the left-line scale. -/
theorem gaussianMoebiusSum_one_le_scale_prefactor {a : ℝ} (ha : 22 ≤ a)
    (hlarge : Real.exp (1 / (500000 * zetaReciprocalLowHeightWidth)) ≤ a) :
    |gaussianMoebiusSum a 1| ≤ gaussianMoebiusScalePrefactor * a *
      Real.exp (33000000 * localZetaLogHeight a ^ 2) *
        Real.exp (a * (1 - zetaReciprocalContourWidth a)) := by
  let w := zetaReciprocalContourWidth a
  let B := zetaReciprocalContourBound a
  let D := moebiusDirichletMass (1 + w)
  let M := Real.exp (33000000 * localZetaLogHeight a ^ 2)
  let C := gaussianMoebiusContourConstant
  let X := Real.exp (a * (1 - w) + 2)
  have hw : 0 < w := zetaReciprocalContourWidth_pos a
  have hwle : w ≤ 1 / 8 := zetaReciprocalContourWidth_le_eighth a
  have hB : 0 < B := zetaReciprocalContourBound_pos a
  have hD : 0 ≤ D := le_trans zero_le_one (one_le_moebiusDirichletMass (by linarith))
  have hM : 1 ≤ M := Real.one_le_exp (by positivity)
  have hC : 16 ≤ C := sixteen_le_gaussianMoebiusContourConstant
  have hBC : B ≤ C * M := zetaReciprocalContourBound_le_logSquare a
  have hCM : 1 ≤ C * M := by nlinarith
  have hL : localZetaLogHeight a ≤ 2 * a := by
    have h := Real.log_le_sub_one_of_pos (show 0 < |a| + 22 by positivity)
    rw [abs_of_nonneg (by linarith)] at h
    change Real.log (|a| + 22) ≤ 2 * a
    rw [abs_of_nonneg (by linarith)]
    linarith
  have hDle : D ≤ 4000000 * a :=
    (moebiusDirichletMass_contour_le_log (by linarith) hlarge).trans (by linarith)
  have hsqrt : 1 ≤ Real.sqrt Real.pi := by
    have h := Real.sqrt_le_sqrt (show 1 ≤ Real.pi by linarith [Real.pi_gt_three])
    simpa using h
  have hleft : Real.exp (a * (1 - w) + (1 - w) ^ 2) ≤ X := by
    apply Real.exp_le_exp.mpr
    nlinarith
  have htop : Real.exp (a * (1 + w) + (1 + w) ^ 2 - a ^ 2) ≤ X := by
    apply Real.exp_le_exp.mpr
    nlinarith [mul_nonneg (show 0 ≤ a by linarith) (show 0 ≤ 1 / 8 - w by linarith)]
  have htail : Real.exp (a * (1 + w) + (1 + w) ^ 2 - a ^ 2 / 2) ≤ X := by
    apply Real.exp_le_exp.mpr
    nlinarith [mul_nonneg (show 0 ≤ a by linarith) (show 0 ≤ 1 / 8 - w by linarith)]
  have hb := gaussianMoebiusSum_contour_bound (a := a) (tau := 1) (T := a)
    (by linarith) (by norm_num) (by linarith)
  simp only [one_mul, div_one] at hb
  have hb' := (le_div_iff₀ (show 0 < Real.sqrt Real.pi by linarith)).mp hb
  have hraw := (le_mul_of_one_le_right (abs_nonneg (gaussianMoebiusSum a 1)) hsqrt).trans hb'
  have h1 := mul_le_mul_of_nonneg_left hleft (show 0 ≤ 2 * a * B by positivity)
  have h2 := mul_le_mul_of_nonneg_left htop (show 0 ≤ 4 * w * B by positivity)
  have h3 := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left htail hD)
    (Real.sqrt_nonneg (2 * Real.pi))
  have hcoef : 2 * a * B + 4 * w * B + D * Real.sqrt (2 * Real.pi) ≤
      C * (3 + 4000000 * Real.sqrt (2 * Real.pi)) * a * M := by
    calc
      _ ≤ 3 * a * B + (4000000 * a * Real.sqrt (2 * Real.pi)) * (C * M) := by
        apply add_le_add
        · have h := mul_le_mul_of_nonneg_right (show 2 * a + 4 * w ≤ 3 * a by linarith) hB.le
          nlinarith
        · exact (mul_le_mul_of_nonneg_right hDle (Real.sqrt_nonneg _)).trans
            (le_mul_of_one_le_right (by positivity) hCM)
      _ ≤ 3 * a * (C * M) + (4000000 * a * Real.sqrt (2 * Real.pi)) * (C * M) := by gcongr
      _ = _ := by ring
  calc
    _ ≤ (2 * a * B + 4 * w * B + D * Real.sqrt (2 * Real.pi)) * X := by
      dsimp only [w, B, D] at h1 h2 h3
      nlinarith
    _ ≤ (C * (3 + 4000000 * Real.sqrt (2 * Real.pi)) * a * M) * X :=
      mul_le_mul_of_nonneg_right hcoef (Real.exp_pos _).le
    _ = _ := by
      dsimp [X, C, M, w, gaussianMoebiusScalePrefactor]
      rw [Real.exp_add]
      ring

/-- The actual unit-time Möbius sum has the left-line exponent plus a fixed squared-logarithm cost. -/
theorem gaussianMoebiusSum_one_le_logSquare_envelope {a : ℝ} (ha : 22 ≤ a)
    (hlarge : Real.exp (1 / (500000 * zetaReciprocalLowHeightWidth)) ≤ a) :
    |gaussianMoebiusSum a 1| ≤ Real.exp
      (a - a / (500000 * localZetaLogHeight a) + gaussianMoebiusScaleExponent * localZetaLogHeight a ^ 2) := by
  let L := localZetaLogHeight a
  have hL : 2 < L := two_lt_localZetaLogHeight a
  have hP := gaussianMoebiusScalePrefactor_pos
  have haexp : a ≤ Real.exp L := by
    rw [show Real.exp L = |a| + 22 by exact Real.exp_log (by positivity)]
    exact (le_abs_self a).trans (by linarith)
  have hexponent : Real.log gaussianMoebiusScalePrefactor + L + 33000000 * L ^ 2 ≤
      gaussianMoebiusScaleExponent * L ^ 2 := by
    have h := mul_le_mul_of_nonneg_left (show 1 ≤ L ^ 2 by nlinarith)
      (abs_nonneg (Real.log gaussianMoebiusScalePrefactor))
    unfold gaussianMoebiusScaleExponent
    nlinarith [le_abs_self (Real.log gaussianMoebiusScalePrefactor), sq_nonneg (L - 2)]
  have hpre : gaussianMoebiusScalePrefactor * a * Real.exp (33000000 * L ^ 2) ≤
      Real.exp (gaussianMoebiusScaleExponent * L ^ 2) := by
    calc
      _ ≤ gaussianMoebiusScalePrefactor * Real.exp L * Real.exp (33000000 * L ^ 2) := by gcongr
      _ = Real.exp (Real.log gaussianMoebiusScalePrefactor + L + 33000000 * L ^ 2) := by
        rw [Real.exp_add, Real.exp_add, Real.exp_log hP]
      _ ≤ _ := Real.exp_le_exp.mpr hexponent
  apply (gaussianMoebiusSum_one_le_scale_prefactor ha hlarge).trans
  apply (mul_le_mul_of_nonneg_right hpre (Real.exp_pos _).le).trans_eq
  rw [← Real.exp_add, zetaReciprocalContourWidth_eq_stripWidth (by linarith) hlarge, zetaReciprocalStripWidth]
  congr 1
  dsimp [L]
  ring

end

end RiemannGaussian
