import RiemannGaussian.GaussianMoebiusMellin

/-!
# An actual Gaussian Möbius bound with every contour correction

The full right-line integral is split exactly into its finite segment and
its two infinite tails. A proved Dirichlet majorant gives Gaussian tail
suppression. Combining this with the checked finite contour identity gives
an unconditional bound for the original signed Gaussian Möbius sum.
This estimate still uses a line near real part one and does not establish
the uniform weighted signed-current bound.
-/

open Complex MeasureTheory Set
open scoped Interval

namespace RiemannGaussian

noncomputable section

/-- Outside the truncation, half the Gaussian exponent controls height and half remains integrable. -/
theorem norm_zetaReciprocalGaussianKernel_le_tail (a : ℝ) {tau sigma T t : ℝ}
    (htau : 0 ≤ tau) (hsigma : 1 < sigma) (hT : 0 ≤ T) (ht : T ≤ |t|) :
    ‖zetaReciprocalGaussianKernel a tau ((sigma : ℂ) + (t : ℂ) * I)‖ ≤
      (moebiusDirichletMass sigma * Real.exp (a * sigma + tau * sigma ^ 2 - tau * T ^ 2 / 2)) *
        Real.exp (-(tau / 2) * t ^ 2) := by
  have hsq : T ^ 2 ≤ t ^ 2 := by
    have h := (sq_le_sq₀ hT (abs_nonneg t)).mpr ht
    simpa only [sq_abs] using h
  have hmass : 0 ≤ moebiusDirichletMass sigma := le_trans zero_le_one (one_le_moebiusDirichletMass hsigma)
  calc
    _ ≤ (Real.exp (a * sigma + tau * sigma ^ 2) * Real.exp (-tau * t ^ 2)) *
        moebiusDirichletMass sigma := norm_zetaReciprocalGaussianKernel_le_dirichlet a tau hsigma t
    _ = moebiusDirichletMass sigma * Real.exp (a * sigma + tau * sigma ^ 2 - tau * t ^ 2) := by
      rw [← Real.exp_add]
      ring_nf
    _ ≤ moebiusDirichletMass sigma * Real.exp
        ((a * sigma + tau * sigma ^ 2 - tau * T ^ 2 / 2) + (-(tau / 2) * t ^ 2)) := by
      apply mul_le_mul_of_nonneg_left _ hmass
      apply Real.exp_le_exp.mpr
      nlinarith [mul_le_mul_of_nonneg_left hsq htau]
    _ = _ := by rw [Real.exp_add]; ring

/-- Both unbounded right-line tails have a single explicit Gaussian norm bound. -/
theorem zetaReciprocalGaussian_infinite_tails_le (a : ℝ) {tau sigma T : ℝ}
    (htau : 0 < tau) (hsigma : 1 < sigma) (hT : 0 ≤ T) :
    ‖∫ t : ℝ in (Ioc (-T) T)ᶜ,
      zetaReciprocalGaussianKernel a tau ((sigma : ℂ) + (t : ℂ) * I)‖ ≤
      moebiusDirichletMass sigma * Real.exp (a * sigma + tau * sigma ^ 2 - tau * T ^ 2 / 2) *
        Real.sqrt (2 * Real.pi / tau) := by
  let C := moebiusDirichletMass sigma * Real.exp (a * sigma + tau * sigma ^ 2 - tau * T ^ 2 / 2)
  have hC : 0 ≤ C := mul_nonneg (le_trans zero_le_one (one_le_moebiusDirichletMass hsigma)) (Real.exp_pos _).le
  have hg : Integrable (fun t : ℝ ↦ C * Real.exp (-(tau / 2) * t ^ 2)) :=
    (integrable_exp_neg_mul_sq (by linarith : 0 < tau / 2)).const_mul C
  have hbound : ∀ᵐ t : ℝ ∂volume.restrict (Ioc (-T) T)ᶜ,
      ‖zetaReciprocalGaussianKernel a tau ((sigma : ℂ) + (t : ℂ) * I)‖ ≤
        C * Real.exp (-(tau / 2) * t ^ 2) := by
    apply (ae_restrict_iff' measurableSet_Ioc.compl).mpr
    exact Filter.Eventually.of_forall fun t ht ↦ norm_zetaReciprocalGaussianKernel_le_tail a htau.le hsigma hT (by
      by_contra h
      have ht' := abs_lt.mp (lt_of_not_ge h)
      exact ht ⟨ht'.1, ht'.2.le⟩)
  apply (norm_integral_le_of_norm_le hg.integrableOn hbound).trans
  apply (setIntegral_le_integral hg (Filter.Eventually.of_forall fun t ↦ mul_nonneg hC (Real.exp_pos _).le)).trans_eq
  rw [integral_const_mul, integral_gaussian]
  congr 2
  ring

/-- The normalized arithmetic Gaussian sum is exactly its finite right-line segment plus both infinite tails. -/
theorem gaussianMoebiusSum_eq_truncated_add_tail (a : ℝ) {tau sigma T : ℝ}
    (htau : 0 < tau) (hsigma : 1 < sigma) (hT : 0 ≤ T) :
    ((Real.sqrt (Real.pi / tau) * gaussianMoebiusSum a tau : ℝ) : ℂ) =
      (∫ t : ℝ in -T..T, zetaReciprocalGaussianKernel a tau ((sigma : ℂ) + (t : ℂ) * I)) +
      (∫ t : ℝ in (Ioc (-T) T)ᶜ, zetaReciprocalGaussianKernel a tau ((sigma : ℂ) + (t : ℂ) * I)) := by
  rw [← integral_zetaReciprocalGaussianKernel_eq_gaussianMoebiusSum a htau hsigma,
    intervalIntegral.integral_of_le (by linarith)]
  exact (integral_add_compl measurableSet_Ioc (integrable_zetaReciprocalGaussianKernel_vertical a htau hsigma)).symm

/-- The exact oriented contour identity for the actual arithmetic Gaussian sum retains every complex boundary and tail term. -/
theorem gaussianMoebiusSum_contour_identity (a : ℝ) {tau T : ℝ}
    (htau : 0 < tau) (hT : 2 ≤ T) :
    I * ((Real.sqrt (Real.pi / tau) * gaussianMoebiusSum a tau : ℝ) : ℂ) =
      I * (∫ t : ℝ in -T..T, zetaReciprocalGaussianKernel a tau
        (((1 - zetaReciprocalContourWidth T : ℝ) : ℂ) + (t : ℂ) * I)) +
      (∫ x : ℝ in (1 - zetaReciprocalContourWidth T)..(1 + zetaReciprocalContourWidth T),
        zetaReciprocalGaussianKernel a tau ((x : ℂ) + (T : ℂ) * I)) -
      (∫ x : ℝ in (1 - zetaReciprocalContourWidth T)..(1 + zetaReciprocalContourWidth T),
        zetaReciprocalGaussianKernel a tau ((x : ℂ) + ((-T : ℝ) : ℂ) * I)) +
      I * (∫ t : ℝ in (Ioc (-T) T)ᶜ, zetaReciprocalGaussianKernel a tau
        (((1 + zetaReciprocalContourWidth T : ℝ) : ℂ) + (t : ℂ) * I)) := by
  rw [gaussianMoebiusSum_eq_truncated_add_tail a htau
    (show 1 < 1 + zetaReciprocalContourWidth T by linarith [zetaReciprocalContourWidth_pos T])
    (show 0 ≤ T by linarith), mul_add, zetaReciprocalGaussian_contour_shift a tau hT]

/-- The actual signed Gaussian Möbius sum is bounded by the proved left-line gain and all finite and infinite contour errors. -/
theorem gaussianMoebiusSum_contour_bound {a tau T : ℝ}
    (ha : 0 ≤ a) (htau : 0 < tau) (hT : 2 ≤ T) :
    |gaussianMoebiusSum a tau| ≤
      (2 * T * zetaReciprocalContourBound T * Real.exp
          (a * (1 - zetaReciprocalContourWidth T) + tau * (1 - zetaReciprocalContourWidth T) ^ 2) +
        4 * zetaReciprocalContourWidth T * zetaReciprocalContourBound T * Real.exp
          (a * (1 + zetaReciprocalContourWidth T) + tau * (1 + zetaReciprocalContourWidth T) ^ 2 - tau * T ^ 2) +
        moebiusDirichletMass (1 + zetaReciprocalContourWidth T) * Real.exp
          (a * (1 + zetaReciprocalContourWidth T) + tau * (1 + zetaReciprocalContourWidth T) ^ 2 - tau * T ^ 2 / 2) *
          Real.sqrt (2 * Real.pi / tau)) / Real.sqrt (Real.pi / tau) := by
  have hsigma : 1 < 1 + zetaReciprocalContourWidth T := by linarith [zetaReciprocalContourWidth_pos T]
  have he := gaussianMoebiusSum_eq_truncated_add_tail a htau hsigma (show 0 ≤ T by linarith)
  have hb := zetaReciprocalGaussian_right_integral_le ha htau.le hT
  have ht := zetaReciprocalGaussian_infinite_tails_le a htau hsigma (show 0 ≤ T by linarith)
  have hnorm := norm_add_le
    (∫ t : ℝ in -T..T, zetaReciprocalGaussianKernel a tau
      (((1 + zetaReciprocalContourWidth T : ℝ) : ℂ) + (t : ℂ) * I))
    (∫ t : ℝ in (Ioc (-T) T)ᶜ, zetaReciprocalGaussianKernel a tau
      (((1 + zetaReciprocalContourWidth T : ℝ) : ℂ) + (t : ℂ) * I))
  rw [← he, Complex.norm_real, Real.norm_eq_abs, abs_mul,
    abs_of_nonneg (Real.sqrt_nonneg _)] at hnorm
  rw [le_div_iff₀ (Real.sqrt_pos.mpr (div_pos Real.pi_pos htau))]
  nlinarith

end

end RiemannGaussian
