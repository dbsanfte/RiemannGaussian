import RiemannGaussian.MoebiusExponentialContourScale

/-!
# Full contour cancellation on a moving arithmetic heat schedule

At the cubic logarithmic center, exponential contour height and reciprocal
heat time give an exponential gain in the scale parameter. The bound
includes the left line, horizontal terms, and the full right-line tails.
Every moving mass and Gaussian normalization is estimated explicitly.
-/

namespace RiemannGaussian

noncomputable section

/-- A fixed prefactor covering all three actual moving-contour contributions. -/
def moebiusFiniteContourPrefactor : ℝ :=
  3 * gaussianMoebiusContourConstant + 4000000 * Real.sqrt (2 * Real.pi)

/-- The full moving-contour prefactor is positive. -/
theorem moebiusFiniteContourPrefactor_pos : 0 < moebiusFiniteContourPrefactor := by
  have hC := sixteen_le_gaussianMoebiusContourConstant
  unfold moebiusFiniteContourPrefactor
  positivity

/-- The complete original contour envelope has an exponential scale gain on the coupled cubic-center, exponential-height, and shrinking-heat schedule. -/
theorem gaussianMoebiusContourMajorant_exponentialScale_le {h : ℝ} (hh : 22 ≤ h)
    (hlarge : 1 / (500000 * zetaReciprocalLowHeightWidth) ≤ h)
    (htail : 4 * moebiusFiniteContourCenter h ≤ Real.exp h) :
    gaussianMoebiusContourMajorant (moebiusFiniteContourCenter h) (Real.exp (-h)) (Real.exp h) ≤
      moebiusFiniteContourPrefactor * Real.exp (moebiusFiniteContourCenter h - h) := by
  let a := moebiusFiniteContourCenter h
  let tau := Real.exp (-h)
  let T := Real.exp h
  let w := zetaReciprocalContourWidth T
  let B := zetaReciprocalContourBound T
  let D := moebiusDirichletMass (1 + w)
  let Q := Real.sqrt (Real.pi / tau)
  let C := gaussianMoebiusContourConstant
  have htau : 0 < tau := Real.exp_pos _
  have htaule : tau ≤ 1 / 4 := by
    have hd := one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 4)
      (show 4 ≤ Real.exp h by linarith [Real.add_one_le_exp h])
    simpa only [tau, Real.exp_neg, one_div] using hd
  have hT : 0 < T := Real.exp_pos _
  have hw : 0 < w := zetaReciprocalContourWidth_pos T
  have hwle : w ≤ 1 / 8 := zetaReciprocalContourWidth_le_eighth T
  have hB : 0 < B := zetaReciprocalContourBound_pos T
  have hD : 0 ≤ D := by have hd := one_le_moebiusDirichletMass (show 1 < 1 + w by linarith); linarith
  have hC : 0 < C := by linarith [sixteen_le_gaussianMoebiusContourConstant]
  have hQ : 1 ≤ Q := by
    have hp : 1 ≤ Real.pi / tau := (le_div_iff₀ htau).mpr (by linarith [Real.pi_gt_three])
    simpa only [Real.sqrt_one] using Real.sqrt_le_sqrt hp
  have hAsq : 1000000000000000 * h ^ 2 ≤ a := by
    dsimp [a, moebiusFiniteContourCenter]
    nlinarith [mul_nonneg (sq_nonneg h) (show 0 ≤ h - 1 by linarith)]
  have hhsq : h ≤ h ^ 2 := by nlinarith [sq_nonneg (h - 1)]
  have ha : 0 ≤ a := by dsimp [a, moebiusFiniteContourCenter]; positivity
  have hawlo : 1000000000 * h ^ 2 ≤ a * w := moebiusFiniteContourCenter_mul_width_ge hh hlarge
  have hawhi : a * w ≤ a / 8 := by nlinarith [mul_le_mul_of_nonneg_left hwle ha]
  have hBbound : B ≤ C * Real.exp (132000000 * h ^ 2) := zetaReciprocalContourBound_exp_le hh
  have hDbound : D ≤ 4000000 * Real.exp h :=
    (moebiusDirichletMass_expContour_le hh hlarge).trans (by linarith [Real.add_one_le_exp h])
  have hheatL : tau * (1 - w) ^ 2 ≤ 2 := by
    have hs : (1 - w) ^ 2 ≤ 2 := by nlinarith
    nlinarith [mul_le_mul_of_nonneg_left hs htau.le]
  have hheatR : tau * (1 + w) ^ 2 ≤ 2 := by
    have hs : (1 + w) ^ 2 ≤ 2 := by nlinarith
    nlinarith [mul_le_mul_of_nonneg_left hs htau.le]
  have htailEq : tau * T ^ 2 = Real.exp h := moebius_exponentialHeat_mul_height_sq h
  have hsqrt : Real.sqrt (2 * Real.pi / tau) = Real.sqrt (2 * Real.pi) * Real.exp (h / 2) :=
    moebius_exponentialHeat_tail_sqrt h
  have hleft : (2 * T * B * Real.exp (tau * (1 - w) ^ 2) / Q) * Real.exp ((1 - w) * a) ≤
      2 * C * Real.exp (a - h) := by
    calc
      _ ≤ (2 * T * B * Real.exp (tau * (1 - w) ^ 2)) * Real.exp ((1 - w) * a) :=
        mul_le_mul_of_nonneg_right (div_le_self (by positivity) hQ) (Real.exp_pos _).le
      _ ≤ (2 * Real.exp h * (C * Real.exp (132000000 * h ^ 2)) * Real.exp (tau * (1 - w) ^ 2)) *
          Real.exp ((1 - w) * a) := by gcongr
      _ = 2 * C * Real.exp (h + 132000000 * h ^ 2 + tau * (1 - w) ^ 2 + (1 - w) * a) := by
        simp only [Real.exp_add]
        ring
      _ ≤ _ := mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by nlinarith)) (by positivity)
  have hhorizontal : (4 * w * B * Real.exp (tau * (1 + w) ^ 2 - tau * T ^ 2) / Q) *
      Real.exp ((1 + w) * a) ≤ C * Real.exp (a - h) := by
    have hcoef : 4 * w * B ≤ B := by nlinarith
    calc
      _ ≤ (4 * w * B * Real.exp (tau * (1 + w) ^ 2 - tau * T ^ 2)) * Real.exp ((1 + w) * a) :=
        mul_le_mul_of_nonneg_right (div_le_self (by positivity) hQ) (Real.exp_pos _).le
      _ ≤ (C * Real.exp (132000000 * h ^ 2)) * Real.exp (tau * (1 + w) ^ 2 - tau * T ^ 2) *
          Real.exp ((1 + w) * a) :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right (hcoef.trans hBbound) (Real.exp_pos _).le) (Real.exp_pos _).le
      _ = C * Real.exp (132000000 * h ^ 2 + (tau * (1 + w) ^ 2 - tau * T ^ 2) + (1 + w) * a) := by
        simp only [Real.exp_add]
        ring
      _ ≤ _ := mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by nlinarith)) hC.le
  have hright : (D * Real.exp (tau * (1 + w) ^ 2 - tau * T ^ 2 / 2) *
      Real.sqrt (2 * Real.pi / tau) / Q) * Real.exp ((1 + w) * a) ≤
        4000000 * Real.sqrt (2 * Real.pi) * Real.exp (a - h) := by
    calc
      _ ≤ (D * Real.exp (tau * (1 + w) ^ 2 - tau * T ^ 2 / 2) * Real.sqrt (2 * Real.pi / tau)) *
          Real.exp ((1 + w) * a) :=
        mul_le_mul_of_nonneg_right (div_le_self (by positivity) hQ) (Real.exp_pos _).le
      _ ≤ (4000000 * Real.exp h) * Real.exp (tau * (1 + w) ^ 2 - tau * T ^ 2 / 2) *
          (Real.sqrt (2 * Real.pi) * Real.exp (h / 2)) * Real.exp ((1 + w) * a) := by
        rw [hsqrt]
        gcongr
      _ = 4000000 * Real.sqrt (2 * Real.pi) *
          Real.exp (h + (tau * (1 + w) ^ 2 - tau * T ^ 2 / 2) + h / 2 + (1 + w) * a) := by
        simp only [Real.exp_add]
        ring
      _ ≤ _ := mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by nlinarith)) (by positivity)
  exact (add_le_add (add_le_add hleft hhorizontal) hright).trans_eq (by
    dsimp only [moebiusFiniteContourPrefactor, C, a]
    ring)

end

end RiemannGaussian
