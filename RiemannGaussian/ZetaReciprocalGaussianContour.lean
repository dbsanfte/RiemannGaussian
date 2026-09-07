import RiemannGaussian.ZetaReciprocalBox
import RiemannGaussian.GaussianXiDivisorContour

/-!
# An actual Gaussian reciprocal-zeta contour estimate

The entire shifted rectangle is free of reciprocal poles. Its Gaussian
Mellin kernel has an exact complex contour identity retaining both
horizontal corrections. Quantitative bounds give a left-line gain and
Gaussian suppression of the two horizontal segments. This is an analytic
input for the original Möbius sums, not a bound for the signed eta current.
-/

open Complex MeasureTheory Set
open scoped Classical Interval

namespace RiemannGaussian

noncomputable section

/-- The actual complex Gaussian Mellin kernel for the reciprocal of zeta. -/
def zetaReciprocalGaussianKernel (a tau : ℝ) (s : ℂ) : ℂ :=
  Complex.exp ((a : ℂ) * s + (tau : ℂ) * s ^ 2) * zetaReciprocalExtension s

/-- The Gaussian phase is retained in the source kernel; its norm has the exact ordinate damping. -/
theorem norm_zetaReciprocalGaussianKernel (a tau sigma t : ℝ) :
    ‖zetaReciprocalGaussianKernel a tau ((sigma : ℂ) + (t : ℂ) * I)‖ =
      Real.exp (a * sigma + tau * (sigma ^ 2 - t ^ 2)) *
        ‖zetaReciprocalExtension ((sigma : ℂ) + (t : ℂ) * I)‖ := by
  have he : ((a : ℂ) * ((sigma : ℂ) + (t : ℂ) * I) +
      (tau : ℂ) * ((sigma : ℂ) + (t : ℂ) * I) ^ 2).re =
        a * sigma + tau * (sigma ^ 2 - t ^ 2) := by simp [pow_two]
  rw [zetaReciprocalGaussianKernel, norm_mul, Complex.norm_exp, he]

/-- The actual Gaussian reciprocal kernel is analytic near every point of the whole shifted box. -/
theorem analyticAt_zetaReciprocalGaussianKernel_on_box (a tau : ℝ) {T : ℝ} {s : ℂ}
    (hre : |s.re - 1| ≤ zetaReciprocalContourWidth T) (him : |s.im| ≤ T) :
    AnalyticAt ℂ (zetaReciprocalGaussianKernel a tau) s := by
  have he : AnalyticAt ℂ (fun z : ℂ ↦ Complex.exp ((a : ℂ) * z + (tau : ℂ) * z ^ 2)) s := by fun_prop
  exact he.mul (analyticAt_zetaReciprocalExtension_on_box hre him)

/-- Cauchy's theorem applies to the full actual reciprocal rectangle, including the filled pole at one. -/
theorem rectangularBoundaryIntegral_zetaReciprocalGaussianKernel_eq_zero (a tau : ℝ)
    {T : ℝ} (hT : 2 ≤ T) :
    rectangularBoundaryIntegral (1 - zetaReciprocalContourWidth T) (1 + zetaReciprocalContourWidth T)
      (-T) T (zetaReciprocalGaussianKernel a tau) = 0 := by
  apply rectangularBoundaryIntegral_eq_zero_of_differentiableOn
  intro s hs
  have hre : s.re ∈ uIcc (1 - zetaReciprocalContourWidth T) (1 + zetaReciprocalContourWidth T) := by
    simpa using hs.1
  have him : s.im ∈ uIcc (-T) T := by simpa using hs.2
  rw [uIcc_of_le (by linarith [zetaReciprocalContourWidth_pos T])] at hre
  rw [uIcc_of_le (by linarith)] at him
  exact (analyticAt_zetaReciprocalGaussianKernel_on_box a tau
    (abs_le.mpr ⟨by linarith [hre.1], by linarith [hre.2]⟩) (abs_le.mpr him)).differentiableAt.differentiableWithinAt

/-- Moving the actual Gaussian reciprocal integral left retains the exact oriented top and bottom corrections. -/
theorem zetaReciprocalGaussian_contour_shift (a tau : ℝ) {T : ℝ} (hT : 2 ≤ T) :
    I * (∫ y : ℝ in -T..T, zetaReciprocalGaussianKernel a tau
      (((1 + zetaReciprocalContourWidth T : ℝ) : ℂ) + (y : ℂ) * I)) =
    I * (∫ y : ℝ in -T..T, zetaReciprocalGaussianKernel a tau
      (((1 - zetaReciprocalContourWidth T : ℝ) : ℂ) + (y : ℂ) * I)) +
    (∫ x : ℝ in (1 - zetaReciprocalContourWidth T)..(1 + zetaReciprocalContourWidth T),
      zetaReciprocalGaussianKernel a tau ((x : ℂ) + (T : ℂ) * I)) -
    (∫ x : ℝ in (1 - zetaReciprocalContourWidth T)..(1 + zetaReciprocalContourWidth T),
      zetaReciprocalGaussianKernel a tau ((x : ℂ) + ((-T : ℝ) : ℂ) * I)) := by
  have h := rectangularBoundaryIntegral_zetaReciprocalGaussianKernel_eq_zero a tau hT
  unfold rectangularBoundaryIntegral at h
  linear_combination h

/-- The actual pointwise reciprocal envelope retains the exact horizontal exponent and Gaussian ordinate damping. -/
theorem norm_zetaReciprocalGaussianKernel_le_on_box (a tau : ℝ) {T sigma t : ℝ}
    (hs : |sigma - 1| ≤ zetaReciprocalContourWidth T) (ht : |t| ≤ T) :
    ‖zetaReciprocalGaussianKernel a tau ((sigma : ℂ) + (t : ℂ) * I)‖ ≤
      zetaReciprocalContourBound T * Real.exp (a * sigma + tau * (sigma ^ 2 - t ^ 2)) := by
  rw [norm_zetaReciprocalGaussianKernel]
  have h := mul_le_mul_of_nonneg_left
    (norm_zetaReciprocalExtension_le_on_box (s := (sigma : ℂ) + (t : ℂ) * I)
      (by simpa using hs) (by simpa using ht)) (Real.exp_pos (a * sigma + tau * (sigma ^ 2 - t ^ 2))).le
  exact h.trans_eq (mul_comm _ _)

/-- Each horizontal correction has an explicit Gaussian suppression factor at the actual contour height. -/
theorem zetaReciprocalGaussian_horizontal_integral_le {a tau T t : ℝ}
    (ha : 0 ≤ a) (htau : 0 ≤ tau) (hT : 2 ≤ T) (ht : |t| = T) :
    ‖∫ x : ℝ in (1 - zetaReciprocalContourWidth T)..(1 + zetaReciprocalContourWidth T),
      zetaReciprocalGaussianKernel a tau ((x : ℂ) + (t : ℂ) * I)‖ ≤
      2 * zetaReciprocalContourWidth T * zetaReciprocalContourBound T *
        Real.exp (a * (1 + zetaReciprocalContourWidth T) +
          tau * (1 + zetaReciprocalContourWidth T) ^ 2 - tau * T ^ 2) := by
  let w := zetaReciprocalContourWidth T
  have hw : 0 < w := zetaReciprocalContourWidth_pos T
  have ht2 : t ^ 2 = T ^ 2 := by nlinarith [sq_abs t]
  have hb := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := 1 - w) (b := 1 + w) (f := fun x : ℝ ↦ zetaReciprocalGaussianKernel a tau ((x : ℂ) + (t : ℂ) * I))
    (C := zetaReciprocalContourBound T * Real.exp (a * (1 + w) + tau * (1 + w) ^ 2 - tau * T ^ 2)) (by
      intro x hx
      rw [uIoc_of_le (by linarith)] at hx
      have hxabs : |x - 1| ≤ w := abs_le.mpr ⟨by linarith [hx.1], by linarith [hx.2]⟩
      apply (norm_zetaReciprocalGaussianKernel_le_on_box a tau hxabs ht.le).trans
      apply mul_le_mul_of_nonneg_left _ (zetaReciprocalContourBound_pos T).le
      apply Real.exp_le_exp.mpr
      have hxpos : 0 ≤ x := by linarith [hx.1, zetaReciprocalContourWidth_le_eighth T]
      have hsquare : x ^ 2 ≤ (1 + w) ^ 2 := (sq_le_sq₀ hxpos (by positivity)).mpr hx.2
      have hax := mul_le_mul_of_nonneg_left hx.2 ha
      have htx := mul_le_mul_of_nonneg_left hsquare htau
      rw [ht2]
      nlinarith)
  rw [show 1 + w - (1 - w) = 2 * w by ring, abs_of_pos (by positivity)] at hb
  exact hb.trans_eq (by dsimp [w]; ring)

/-- The left vertical integral keeps its strictly smaller real exponential scale and the full reciprocal constant. -/
theorem zetaReciprocalGaussian_left_integral_le (a : ℝ) {tau T : ℝ} (htau : 0 ≤ tau) (hT : 2 ≤ T) :
    ‖∫ y : ℝ in -T..T, zetaReciprocalGaussianKernel a tau
      (((1 - zetaReciprocalContourWidth T : ℝ) : ℂ) + (y : ℂ) * I)‖ ≤
      2 * T * zetaReciprocalContourBound T * Real.exp
        (a * (1 - zetaReciprocalContourWidth T) + tau * (1 - zetaReciprocalContourWidth T) ^ 2) := by
  let w := zetaReciprocalContourWidth T
  have hw : 0 < w := zetaReciprocalContourWidth_pos T
  have hs : |(1 - w) - 1| ≤ w := by rw [show (1 - w) - 1 = -w by ring, abs_neg, abs_of_pos hw]
  have hb := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := -T) (b := T) (f := fun y : ℝ ↦ zetaReciprocalGaussianKernel a tau (((1 - w : ℝ) : ℂ) + (y : ℂ) * I))
    (C := zetaReciprocalContourBound T * Real.exp (a * (1 - w) + tau * (1 - w) ^ 2)) (by
      intro y hy
      rw [uIoc_of_le (by linarith)] at hy
      apply (norm_zetaReciprocalGaussianKernel_le_on_box a tau hs (abs_le.mpr ⟨hy.1.le, hy.2⟩)).trans
      apply mul_le_mul_of_nonneg_left _ (zetaReciprocalContourBound_pos T).le
      apply Real.exp_le_exp.mpr
      nlinarith [mul_nonneg htau (sq_nonneg y)])
  rw [show T - -T = 2 * T by ring, abs_of_pos (by linarith)] at hb
  exact hb.trans_eq (by dsimp [w]; ring)

/-- The actual truncated Gaussian reciprocal integral has a proved left-line gain with both horizontal errors controlled. -/
theorem zetaReciprocalGaussian_right_integral_le {a tau T : ℝ}
    (ha : 0 ≤ a) (htau : 0 ≤ tau) (hT : 2 ≤ T) :
    ‖∫ y : ℝ in -T..T, zetaReciprocalGaussianKernel a tau
      (((1 + zetaReciprocalContourWidth T : ℝ) : ℂ) + (y : ℂ) * I)‖ ≤
      2 * T * zetaReciprocalContourBound T * Real.exp
        (a * (1 - zetaReciprocalContourWidth T) + tau * (1 - zetaReciprocalContourWidth T) ^ 2) +
      4 * zetaReciprocalContourWidth T * zetaReciprocalContourBound T * Real.exp
        (a * (1 + zetaReciprocalContourWidth T) + tau * (1 + zetaReciprocalContourWidth T) ^ 2 - tau * T ^ 2) := by
  have he := zetaReciprocalGaussian_contour_shift a tau hT
  have hleft := zetaReciprocalGaussian_left_integral_le a htau hT
  have htop := zetaReciprocalGaussian_horizontal_integral_le ha htau hT
    (t := T) (abs_of_nonneg (by linarith))
  have hbottom := zetaReciprocalGaussian_horizontal_integral_le ha htau hT
    (t := -T) (by rw [abs_neg, abs_of_nonneg (by linarith)])
  let V (sigma : ℝ) : ℂ := ∫ y : ℝ in -T..T,
    zetaReciprocalGaussianKernel a tau ((sigma : ℂ) + (y : ℂ) * I)
  let H (t : ℝ) : ℂ := ∫ x : ℝ in (1 - zetaReciprocalContourWidth T)..(1 + zetaReciprocalContourWidth T),
    zetaReciprocalGaussianKernel a tau ((x : ℂ) + (t : ℂ) * I)
  let w := zetaReciprocalContourWidth T
  change I * V (1 + w) = I * V (1 - w) + H T - H (-T) at he
  have htri : ‖V (1 + w)‖ ≤ ‖V (1 - w)‖ + ‖H T‖ + ‖H (-T)‖ := by
    calc
      _ = ‖I * V (1 + w)‖ := by simp
      _ = ‖I * V (1 - w) + H T - H (-T)‖ := congrArg norm he
      _ ≤ ‖I * V (1 - w)‖ + ‖H T‖ + ‖H (-T)‖ :=
        (norm_sub_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)
      _ = _ := by simp
  change ‖V (1 - w)‖ ≤ _ at hleft
  change ‖H T‖ ≤ _ at htop
  change ‖H (-T)‖ ≤ _ at hbottom
  change ‖V (1 + w)‖ ≤ _
  linarith

end

end RiemannGaussian
