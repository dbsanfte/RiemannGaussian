import RiemannGaussian.RiemannXiSuzukiWeilSafeLineArchimedean
import RiemannGaussian.GaussianXiSubquadraticCounting
import Mathlib.Analysis.SpecialFunctions.Arsinh

/-!
# Vertical decay for the Suzuki--Weil contour

This file attacks the final vertical-side input in the global Suzuki--Weil
meeting theorem.  The estimates retain the strict `3/2 < 2` exponent gap in
the xi divisor count and integrate reciprocal zero distances along the short
vertical segment instead of replacing them by a pointwise reciprocal gap.
-/

open Complex Filter MeasureTheory MeromorphicOn Metric Polynomial Set Topology
open scoped Classical ENNReal Interval Topology lp

namespace RiemannGaussian

noncomputable section

/-! ## Subquadratic contour separation -/

/-- The subquadratic global xi growth gives a `3/2`-power bound for the
number of distinct zeros in each spectral window. -/
theorem spectralZetaZeroWindow_card_le_threeHalves_of_growth
    {A T : ℝ} (hA : 1 ≤ A) (hT : 0 ≤ T)
    (hbound : ∀ z : ℂ,
      ‖riemannXi z‖ ≤
        Real.exp (A * (‖z‖ + 1) ^ (3 / 2 : ℝ))) :
    ((spectralZetaZeroWindow T).card : ℝ) ≤
      A * (2 * (T + 1) + 1) ^ (3 / 2 : ℝ) / Real.log 2 := by
  exact (spectralZetaZeroWindow_card_le_riemannXi_divisor hT).trans
    (by
      simpa using jensen_riemannXi_divisor_le_threeHalves hA
        (by linarith : 0 < T + 1) hbound)

/-- The selected canonical disk inherits the same multiplicity-aware
`3/2`-power divisor bound. -/
theorem sum_divisor_riemannXi_ball_le_threeHalves_of_growth
    {A : ℝ} (hA : 1 ≤ A)
    (hbound : ∀ z : ℂ,
      ‖riemannXi z‖ ≤
        Real.exp (A * (‖z‖ + 1) ^ (3 / 2 : ℝ)))
    (n : ℕ) :
    ((∑ᶠ i, divisor riemannXi
        (ball 0 (xiCanonicalRadius n)) i : ℤ) : ℝ) ≤
      A * (2 * xiCanonicalRadius n + 1) ^ (3 / 2 : ℝ) /
        Real.log 2 := by
  have heq :
      (∑ᶠ i, divisor riemannXi (ball 0 (xiCanonicalRadius n)) i) =
        ∑ᶠ i, divisor riemannXi
          (closedBall 0 (xiCanonicalRadius n)) i := by
    apply finsum_congr
    intro i
    exact divisor_riemannXi_ball_eq_closedBall n i
  rw [heq]
  exact_mod_cast jensen_riemannXi_divisor_le_threeHalves hA
    (xiCanonicalRadius_pos n) hbound

/-- With the `3/2` xi count retained, the reciprocal separation radius of
the quantitative contour grows at most like a `3/2` power. -/
theorem one_div_spectralBoundarySeparation_le_threeHalves_of_growth
    {A : ℝ} (hA : 1 ≤ A)
    (hbound : ∀ z : ℂ,
      ‖riemannXi z‖ ≤
        Real.exp (A * (‖z‖ + 1) ^ (3 / 2 : ℝ)))
    (n : ℕ) :
    1 / spectralBoundarySeparation n ≤
      3 *
        (A * (2 * ((n : ℝ) + 2) + 1) ^ (3 / 2 : ℝ) /
            Real.log 2 + 4) := by
  have hwindow := spectralZetaZeroWindow_card_le_threeHalves_of_growth hA
    (show 0 ≤ (n : ℝ) + 1 by positivity) hbound
  have hwindow' :
      ((spectralZetaZeroWindow ((n : ℝ) + 1)).card : ℝ) ≤
        A * (2 * ((n : ℝ) + 2) + 1) ^ (3 / 2 : ℝ) /
          Real.log 2 := by
    convert hwindow using 1
    ring_nf
  have hobstructions :
      ((spectralBoundaryObstructions n).card : ℝ) ≤
        ((spectralZetaZeroWindow ((n : ℝ) + 1)).card : ℝ) + 2 := by
    exact_mod_cast spectralBoundaryObstructions_card_le n
  have hcard :
      ((spectralBoundaryObstructions n).card : ℝ) + 2 ≤
        A * (2 * ((n : ℝ) + 2) + 1) ^ (3 / 2 : ℝ) /
            Real.log 2 + 4 := by
    linarith
  rw [show 1 / spectralBoundarySeparation n =
      3 * (((spectralBoundaryObstructions n).card : ℝ) + 2) by
    unfold spectralBoundarySeparation
    field_simp]
  exact mul_le_mul_of_nonneg_left hcard (by norm_num)

/-- Unconditionally, one constant controls all reciprocal quantitative
separations at the sharp `3/2` counting exponent. -/
theorem exists_one_div_spectralBoundarySeparation_threeHalves_bound :
    ∃ A : ℝ, 1 ≤ A ∧ ∀ n : ℕ,
      1 / spectralBoundarySeparation n ≤
        3 *
          (A * (2 * ((n : ℝ) + 2) + 1) ^ (3 / 2 : ℝ) /
              Real.log 2 + 4) := by
  rcases riemannXi_threeHalvesGrowth with ⟨A, hA, hbound⟩
  exact ⟨A, hA,
    one_div_spectralBoundarySeparation_le_threeHalves_of_growth hA hbound⟩

/-! ## Quadratic decay of the vertical Suzuki transform -/

/-- A uniform inverse-square estimate for Suzuki's transform at any
frequency whose norm and distance from the evaluation point are both
comparable to a positive scale `T`. -/
theorem norm_suzukiWeilSpectralTransform_le_inv_sq_of_vertical_bounds
    (t : ℝ) (z : ℂ) {T : ℝ} (hT : 0 < T) {alpha : ℂ}
    (halphaNorm : T ≤ ‖alpha‖)
    (hgapNorm : T / 2 ≤ ‖z - alpha‖)
    (halphaIm : |alpha.im| ≤ 1) :
    ‖suzukiWeilSpectralTransform t z alpha‖ ≤
      2 * (Real.exp |t| + 1) / T ^ 2 := by
  have halpha : alpha ≠ 0 := by
    exact norm_ne_zero_iff.mp (ne_of_gt (hT.trans_le halphaNorm))
  have hgap : z - alpha ≠ 0 := by
    exact norm_ne_zero_iff.mp
      (ne_of_gt ((half_pos hT).trans_le hgapNorm))
  have hcoeff := norm_suzukiSpectralScrewCoefficient_le_div t halpha
  have hexp : Real.exp (alpha.im * t) ≤ Real.exp |t| := by
    apply Real.exp_le_exp.mpr
    calc
      alpha.im * t ≤ |alpha.im * t| := le_abs_self _
      _ = |alpha.im| * |t| := abs_mul _ _
      _ ≤ 1 * |t| :=
        mul_le_mul_of_nonneg_right halphaIm (abs_nonneg t)
      _ = |t| := one_mul _
  have hcoeff' :
      ‖suzukiSpectralScrewCoefficient t alpha‖ ≤
        (Real.exp |t| + 1) / T := by
    exact hcoeff.trans
      (div_le_div₀ (by positivity) (by linarith) hT halphaNorm)
  unfold suzukiWeilSpectralTransform
  rw [norm_div]
  calc
    ‖suzukiSpectralScrewCoefficient t alpha‖ / ‖z - alpha‖ ≤
        ((Real.exp |t| + 1) / T) / (T / 2) := by
      exact div_le_div₀ (by positivity) hcoeff' (half_pos hT) hgapNorm
    _ = 2 * (Real.exp |t| + 1) / T ^ 2 := by
      field_simp [hT.ne']

/-- On the selected right vertical side, Suzuki's transform has a uniform
`T⁻²` bound once the contour lies beyond twice the real evaluation
coordinate. -/
theorem norm_suzukiWeilSpectralTransform_quantitative_right_le
    (t : ℝ) (z : ℂ) (n : ℕ) (y : ℝ)
    (hy : |y| ≤ 1)
    (hzT : 2 * |z.re| ≤ quantitativeSpectralBoundaryTruncation n) :
    ‖suzukiWeilSpectralTransform t z
        ((quantitativeSpectralBoundaryTruncation n : ℂ) +
          (y : ℂ) * Complex.I)‖ ≤
      2 * (Real.exp |t| + 1) /
        quantitativeSpectralBoundaryTruncation n ^ 2 := by
  let T := quantitativeSpectralBoundaryTruncation n
  let alpha : ℂ := (T : ℂ) + (y : ℂ) * Complex.I
  have hT : 0 < T := (Nat.cast_nonneg n).trans_lt
    (quantitativeSpectralBoundaryTruncation_spec n).1
  have halphaNorm : T ≤ ‖alpha‖ := by
    calc
      T = alpha.re := by simp [alpha]
      _ ≤ ‖alpha‖ := Complex.re_le_norm _
  have hgapRe : T / 2 ≤ |(z - alpha).re| := by
    have hzre : z.re ≤ |z.re| := le_abs_self z.re
    have hdiff : T / 2 ≤ T - z.re := by linarith
    calc
      T / 2 ≤ T - z.re := hdiff
      _ = -(z - alpha).re := by simp [alpha]
      _ ≤ |(z - alpha).re| := neg_le_abs _
  have hgapNorm : T / 2 ≤ ‖z - alpha‖ :=
    hgapRe.trans (Complex.abs_re_le_norm _)
  have halphaIm : |alpha.im| ≤ 1 := by simpa [alpha] using hy
  simpa [T, alpha] using
    norm_suzukiWeilSpectralTransform_le_inv_sq_of_vertical_bounds
      t z hT halphaNorm hgapNorm halphaIm

/-- The reflected frequency on the selected left side obeys the same
inverse-square transform bound. -/
theorem norm_suzukiWeilSpectralTransform_quantitative_left_le
    (t : ℝ) (z : ℂ) (n : ℕ) (y : ℝ)
    (hy : |y| ≤ 1)
    (hzT : 2 * |z.re| ≤ quantitativeSpectralBoundaryTruncation n) :
    ‖suzukiWeilSpectralTransform t z
        (-((quantitativeSpectralBoundaryTruncation n : ℂ) +
          (y : ℂ) * Complex.I))‖ ≤
      2 * (Real.exp |t| + 1) /
        quantitativeSpectralBoundaryTruncation n ^ 2 := by
  let T := quantitativeSpectralBoundaryTruncation n
  let alpha : ℂ := -((T : ℂ) + (y : ℂ) * Complex.I)
  have hT : 0 < T := (Nat.cast_nonneg n).trans_lt
    (quantitativeSpectralBoundaryTruncation_spec n).1
  have halphaNorm : T ≤ ‖alpha‖ := by
    calc
      T = -alpha.re := by simp [alpha]
      _ ≤ |alpha.re| := neg_le_abs _
      _ ≤ ‖alpha‖ := Complex.abs_re_le_norm _
  have hgapRe : T / 2 ≤ |(z - alpha).re| := by
    have hzre : -|z.re| ≤ z.re := neg_abs_le z.re
    have hdiff : T / 2 ≤ z.re + T := by linarith
    calc
      T / 2 ≤ z.re + T := hdiff
      _ = (z - alpha).re := by simp [alpha]
      _ ≤ |(z - alpha).re| := le_abs_self _
  have hgapNorm : T / 2 ≤ ‖z - alpha‖ :=
    hgapRe.trans (Complex.abs_re_le_norm _)
  have halphaIm : |alpha.im| ≤ 1 := by simpa [alpha] using hy
  simpa [T, alpha] using
    norm_suzukiWeilSpectralTransform_le_inv_sq_of_vertical_bounds
      t z hT halphaNorm hgapNorm halphaIm

/-! ## Reflection of the left vertical side -/

/-- After reversing the height parameter, the left vertical integrand is the
negative of a reflected Suzuki transform against the logarithmic derivative
on the right vertical line. -/
theorem suzukiXiWeilSpectralIntegrand_left_reflection
    (t : ℝ) (z : ℂ) (T y : ℝ) :
    suzukiXiWeilSpectralIntegrand t z
        ((-T : ℂ) + ((-y : ℝ) : ℂ) * Complex.I) =
      -(suzukiWeilSpectralTransform t z
          (-((T : ℂ) + (y : ℂ) * Complex.I)) *
        xiSpectralNegativeLogDerivative
          ((T : ℂ) + (y : ℂ) * Complex.I)) := by
  have hpoint :
      ((-T : ℂ) + ((-y : ℝ) : ℂ) * Complex.I) =
        -((T : ℂ) + (y : ℂ) * Complex.I) := by
    push_cast
    ring
  unfold suzukiXiWeilSpectralIntegrand
  rw [hpoint, xiSpectralNegativeLogDerivative_neg]
  ring

/-- On the symmetric height interval, the complete left vertical integral
can be reflected onto the right line without any integrability assumption. -/
theorem intervalIntegral_suzukiXiWeilSpectralIntegrand_left_reflection
    (t : ℝ) (z : ℂ) (T : ℝ) :
    (∫ y : ℝ in (-1 : ℝ)..1,
      suzukiXiWeilSpectralIntegrand t z
        ((-T : ℂ) + (y : ℂ) * Complex.I)) =
      -(∫ y : ℝ in (-1 : ℝ)..1,
        suzukiWeilSpectralTransform t z
            (-((T : ℂ) + (y : ℂ) * Complex.I)) *
          xiSpectralNegativeLogDerivative
            ((T : ℂ) + (y : ℂ) * Complex.I)) := by
  calc
    (∫ y : ℝ in (-1 : ℝ)..1,
        suzukiXiWeilSpectralIntegrand t z
          ((-T : ℂ) + (y : ℂ) * Complex.I)) =
      ∫ y : ℝ in (-1 : ℝ)..1,
        suzukiXiWeilSpectralIntegrand t z
          ((-T : ℂ) + ((-y : ℝ) : ℂ) * Complex.I) := by
        simpa using
          (intervalIntegral.integral_comp_neg
            (f := fun y : ℝ ↦ suzukiXiWeilSpectralIntegrand t z
              ((-T : ℂ) + (y : ℂ) * Complex.I))
            (a := (-1 : ℝ)) (b := 1)).symm
    _ = ∫ y : ℝ in (-1 : ℝ)..1,
        -(suzukiWeilSpectralTransform t z
            (-((T : ℂ) + (y : ℂ) * Complex.I)) *
          xiSpectralNegativeLogDerivative
            ((T : ℂ) + (y : ℂ) * Complex.I)) := by
      apply intervalIntegral.integral_congr
      intro y _hy
      exact suzukiXiWeilSpectralIntegrand_left_reflection t z T y
    _ = -(∫ y : ℝ in (-1 : ℝ)..1,
        suzukiWeilSpectralTransform t z
            (-((T : ℂ) + (y : ℂ) * Complex.I)) *
          xiSpectralNegativeLogDerivative
            ((T : ℂ) + (y : ℂ) * Complex.I)) :=
      intervalIntegral.integral_neg

/-- Both oriented vertical sides are exactly two Suzuki transforms against
the same right-line xi logarithmic derivative. -/
theorem suzukiXiWeilVerticalBoundaryIntegral_eq_right_reflection
    (t : ℝ) (z : ℂ) (T : ℝ) :
    suzukiXiWeilVerticalBoundaryIntegral t z T =
      Complex.I *
          (∫ y : ℝ in (-1 : ℝ)..1,
            suzukiWeilSpectralTransform t z
                ((T : ℂ) + (y : ℂ) * Complex.I) *
              xiSpectralNegativeLogDerivative
                ((T : ℂ) + (y : ℂ) * Complex.I)) +
        Complex.I *
          (∫ y : ℝ in (-1 : ℝ)..1,
            suzukiWeilSpectralTransform t z
                (-((T : ℂ) + (y : ℂ) * Complex.I)) *
              xiSpectralNegativeLogDerivative
                ((T : ℂ) + (y : ℂ) * Complex.I)) := by
  unfold suzukiXiWeilVerticalBoundaryIntegral
  rw [intervalIntegral_suzukiXiWeilSpectralIntegrand_left_reflection]
  unfold suzukiXiWeilSpectralIntegrand
  ring

/-! ## Integrated reciprocal-distance bounds -/

/-- The quantitative contour construction separates the right vertical
line from the real coordinate of every spectral xi zero. -/
theorem spectralBoundarySeparation_le_abs_quantitative_sub_zero_re
    (n : ℕ) (rho : NontrivialZetaZero) :
    spectralBoundarySeparation n ≤
      |quantitativeSpectralBoundaryTruncation n -
        (zetaSpectralCoordinate rho.1).re| := by
  let T := quantitativeSpectralBoundaryTruncation n
  let alpha := zetaSpectralCoordinate rho.1
  have hTnonneg : 0 ≤ T :=
    (Nat.cast_nonneg n).trans
      (quantitativeSpectralBoundaryTruncation_spec n).1.le
  have hsep : spectralBoundarySeparation n ≤
      abs (T - abs alpha.re) := by
    simpa [T, alpha] using
      (quantitativeSpectralBoundaryTruncation_spec n).2.2 rho
  have habs : abs (T - abs alpha.re) ≤ abs (T - alpha.re) := by
    simpa [abs_of_nonneg hTnonneg] using
      (abs_abs_sub_abs_le T alpha.re)
  exact hsep.trans habs

/-- The inverse hyperbolic sine is an antiderivative of a translated,
rescaled reciprocal square root. -/
theorem hasDerivAt_arsinh_sub_div
    {d : ℝ} (hd : 0 < d) (b y : ℝ) :
    HasDerivAt (fun x : ℝ ↦ Real.arsinh ((x - b) / d))
      (Real.sqrt (d ^ 2 + (y - b) ^ 2))⁻¹ y := by
  have hinner : HasDerivAt (fun x : ℝ ↦ (x - b) / d) (1 / d) y := by
    simpa using ((hasDerivAt_id y).sub_const b).div_const d
  have hcomp := (Real.hasDerivAt_arsinh ((y - b) / d)).comp y hinner
  have hrewrite :
      1 + ((y - b) / d) ^ 2 =
        (d ^ 2 + (y - b) ^ 2) / d ^ 2 := by
    field_simp [hd.ne']
  have hcoefficient :
      (Real.sqrt (1 + ((y - b) / d) ^ 2))⁻¹ * (1 / d) =
        (Real.sqrt (d ^ 2 + (y - b) ^ 2))⁻¹ := by
    rw [hrewrite, Real.sqrt_div (by positivity),
      Real.sqrt_sq_eq_abs, abs_of_pos hd]
    field_simp [hd.ne']
  rw [hcoefficient] at hcomp
  simpa [Function.comp_def] using hcomp

/-- Exact integral of a translated reciprocal square root over the fixed
vertical parameter interval. -/
theorem intervalIntegral_inv_sqrt_sq_add_sq
    {d : ℝ} (hd : 0 < d) (b : ℝ) :
    (∫ y : ℝ in (-1 : ℝ)..1,
      (Real.sqrt (d ^ 2 + (y - b) ^ 2))⁻¹) =
      Real.arsinh ((1 - b) / d) -
        Real.arsinh ((-1 - b) / d) := by
  have hpositive (y : ℝ) : 0 < d ^ 2 + (y - b) ^ 2 := by
    exact add_pos_of_pos_of_nonneg (sq_pos_of_pos hd) (sq_nonneg _)
  have hcontinuous : Continuous (fun y : ℝ ↦
      (Real.sqrt (d ^ 2 + (y - b) ^ 2))⁻¹) := by
    apply Continuous.inv₀ (by fun_prop)
    intro y hzero
    exact (Real.sqrt_pos.2 (hpositive y)).ne' hzero
  exact intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun y _hy ↦ hasDerivAt_arsinh_sub_div hd b y)
    (hcontinuous.intervalIntegrable (-1) 1)

/-- Along a vertical line, the reciprocal complex distance has the exact
inverse-hyperbolic-sine integral dictated by its horizontal gap. -/
theorem intervalIntegral_inv_norm_vertical_sub
    {T : ℝ} {alpha : ℂ} (hgap : T ≠ alpha.re) :
    (∫ y : ℝ in (-1 : ℝ)..1,
      ‖((T : ℂ) + (y : ℂ) * Complex.I) - alpha‖⁻¹) =
      Real.arsinh
          ((1 - alpha.im) / |T - alpha.re|) -
        Real.arsinh
          ((-1 - alpha.im) / |T - alpha.re|) := by
  have hd : 0 < |T - alpha.re| := abs_pos.mpr (sub_ne_zero.mpr hgap)
  rw [← intervalIntegral_inv_sqrt_sq_add_sq hd alpha.im]
  apply intervalIntegral.integral_congr
  intro y _hy
  change
    ‖((T : ℂ) + (y : ℂ) * Complex.I) - alpha‖⁻¹ =
      (Real.sqrt (|T - alpha.re| ^ 2 + (y - alpha.im) ^ 2))⁻¹
  congr 1
  rw [Complex.norm_def]
  congr 1
  rw [sq_abs]
  simp [Complex.normSq_apply]
  ring

/-- A nonnegative inverse hyperbolic sine is bounded by an elementary
logarithm with twice its argument. -/
theorem arsinh_le_log_one_add_two_mul {x : ℝ} (hx : 0 ≤ x) :
    Real.arsinh x ≤ Real.log (1 + 2 * x) := by
  have hsqrtSq : (Real.sqrt (1 + x ^ 2)) ^ 2 = 1 + x ^ 2 :=
    Real.sq_sqrt (by positivity)
  have hsqrt : Real.sqrt (1 + x ^ 2) ≤ 1 + x := by
    nlinarith [Real.sqrt_nonneg (1 + x ^ 2)]
  unfold Real.arsinh
  apply Real.log_le_log
  · exact add_pos_of_nonneg_of_pos hx (Real.sqrt_pos.2 (by positivity))
  · linarith

/-- Integrating a reciprocal distance across the complete height-two
segment costs only the logarithm of the reciprocal horizontal gap. -/
theorem intervalIntegral_inv_norm_vertical_sub_le_log
    {T δ : ℝ} {alpha : ℂ} (hδ : 0 < δ)
    (hsep : δ ≤ |T - alpha.re|)
    (halphaIm : |alpha.im| ≤ 1 / 2) :
    (∫ y : ℝ in (-1 : ℝ)..1,
      ‖((T : ℂ) + (y : ℂ) * Complex.I) - alpha‖⁻¹) ≤
      2 * Real.log (1 + 3 / δ) := by
  have hgapPos : 0 < |T - alpha.re| := hδ.trans_le hsep
  have hgap : T ≠ alpha.re := sub_ne_zero.mp (abs_pos.mp hgapPos)
  rw [intervalIntegral_inv_norm_vertical_sub hgap]
  have himBounds := (abs_le.mp halphaIm)
  have hrewrite :
      Real.arsinh ((-1 - alpha.im) / |T - alpha.re|) =
        -Real.arsinh ((1 + alpha.im) / |T - alpha.re|) := by
    rw [show (-1 - alpha.im) / |T - alpha.re| =
        -((1 + alpha.im) / |T - alpha.re|) by ring,
      Real.arsinh_neg]
  rw [hrewrite, sub_neg_eq_add]
  have hfirst :
      Real.arsinh ((1 - alpha.im) / |T - alpha.re|) ≤
        Real.arsinh ((3 / 2) / δ) := by
    apply Real.arsinh_strictMono.monotone
    apply (div_le_div₀ (by norm_num) ?_ hδ hsep)
    linarith
  have hsecond :
      Real.arsinh ((1 + alpha.im) / |T - alpha.re|) ≤
        Real.arsinh ((3 / 2) / δ) := by
    apply Real.arsinh_strictMono.monotone
    apply (div_le_div₀ (by norm_num) ?_ hδ hsep)
    linarith
  calc
    Real.arsinh ((1 - alpha.im) / |T - alpha.re|) +
        Real.arsinh ((1 + alpha.im) / |T - alpha.re|) ≤
      2 * Real.arsinh ((3 / 2) / δ) := by linarith
    _ ≤ 2 * Real.log (1 + 2 * ((3 / 2) / δ)) := by
      gcongr
      exact arsinh_le_log_one_add_two_mul (by positivity)
    _ = 2 * Real.log (1 + 3 / δ) := by
      congr 2
      field_simp [hδ.ne']

/-! ## One integrated canonical factor -/

/-- The pointwise canonical-factor estimate with its pole term left as the
actual reciprocal distance, ready to be integrated. -/
theorem norm_logDeriv_canonicalFactor_le_radial_add_inv
    {R : ℝ} (hR : 0 < R) {i z : ℂ}
    (hi : i ∈ ball 0 R) (hz : ‖z‖ ≤ R / 4) (hzi : z ≠ i) :
    ‖logDeriv (Complex.canonicalFactor R i) z‖ ≤
      2 / R + 1 / ‖z - i‖ := by
  exact norm_logDeriv_canonicalFactor_le hR
    (norm_pos_iff.mpr (sub_ne_zero.mpr hzi)) hi hz le_rfl

/-- Every supported xi canonical factor has an interval-integrable
logarithmic derivative on the quantitatively separated vertical segment. -/
theorem intervalIntegrable_logDeriv_canonicalFactor_quantitative
    (n : ℕ) {i : ℂ}
    (hi : divisor riemannXi (ball 0 (xiCanonicalRadius n)) i ≠ 0) :
    IntervalIntegrable
      (fun y : ℝ ↦
        logDeriv (Complex.canonicalFactor (xiCanonicalRadius n) i)
          (completedSpectralCoordinate
            ((quantitativeSpectralBoundaryTruncation n : ℂ) +
              (y : ℂ) * Complex.I)))
      volume (-1) 1 := by
  let R := xiCanonicalRadius n
  let T := quantitativeSpectralBoundaryTruncation n
  have hR : 0 < R := xiCanonicalRadius_pos n
  have hiBall : i ∈ ball (0 : ℂ) R := by
    exact (divisor riemannXi (ball 0 R)).supportWithinDomain
      (by simpa [R] using hi)
  have hcontinuous : ContinuousOn
      (fun y : ℝ ↦
        logDeriv (Complex.canonicalFactor R i)
          (completedSpectralCoordinate
            ((T : ℂ) + (y : ℂ) * Complex.I)))
      (Icc (-1 : ℝ) 1) := by
    intro y hy
    let s := completedSpectralCoordinate
      ((T : ℂ) + (y : ℂ) * Complex.I)
    have hsquarter : ‖s‖ ≤ R / 4 := by
      simpa [s, T, R] using
        norm_quantitativeCompletedCoordinate_le_quarter n hy.1 hy.2
    have hsclosed : s ∈ closedBall (0 : ℂ) R := by
      rw [mem_closedBall, dist_zero_right]
      exact hsquarter.trans (by linarith)
    have hsi : s ≠ i := by
      intro hs
      have hxi := riemannXi_quantitativeCompletedCoordinate_ne_zero n y
      apply hxi
      rw [show completedSpectralCoordinate
          (((quantitativeSpectralBoundaryTruncation n : ℝ) : ℂ) +
            (y : ℂ) * Complex.I) = i by simpa [s, T] using hs]
      exact riemannXi_eq_zero_of_divisor_ball_ne_zero hi
    have hfactor : Complex.canonicalFactor R i s ≠ 0 :=
      Complex.canonicalFactor_ne_zero hiBall hsclosed hsi
    have hcanonical :=
      Complex.analyticOnNhd_canonicalFactor R i s hsi
    have hlog : AnalyticAt ℂ
        (logDeriv (Complex.canonicalFactor R i)) s := by
      simpa only [logDeriv] using
        hcanonical.deriv.div hcanonical hfactor
    have hcurve : Continuous
        (fun u : ℝ ↦ completedSpectralCoordinate
          ((T : ℂ) + (u : ℂ) * Complex.I)) := by
      unfold completedSpectralCoordinate
      continuity
    have hcomp : ContinuousAt
        (fun u : ℝ ↦
          logDeriv (Complex.canonicalFactor R i)
            (completedSpectralCoordinate
              ((T : ℂ) + (u : ℂ) * Complex.I))) y := by
      apply ContinuousAt.comp'
        (f := fun u : ℝ ↦ completedSpectralCoordinate
          ((T : ℂ) + (u : ℂ) * Complex.I))
        (g := logDeriv (Complex.canonicalFactor R i))
      · simpa only [s] using hlog.continuousAt
      · exact hcurve.continuousAt
    exact hcomp.continuousWithinAt
  exact hcontinuous.intervalIntegrable_of_Icc (by norm_num)

/-- Each xi canonical factor costs only a radial `4/R` term plus a
logarithmic reciprocal-separation term after integration across the complete
height-two quantitative vertical segment. -/
theorem intervalIntegral_norm_logDeriv_canonicalFactor_quantitative_le
    (n : ℕ) {i : ℂ}
    (hi : divisor riemannXi (ball 0 (xiCanonicalRadius n)) i ≠ 0) :
    (∫ y : ℝ in (-1 : ℝ)..1,
      ‖logDeriv
        (Complex.canonicalFactor (xiCanonicalRadius n) i)
        (completedSpectralCoordinate
          ((quantitativeSpectralBoundaryTruncation n : ℂ) +
            (y : ℂ) * Complex.I))‖) ≤
      4 / xiCanonicalRadius n +
        2 * Real.log (1 + 3 / spectralBoundarySeparation n) := by
  let R := xiCanonicalRadius n
  let T := quantitativeSpectralBoundaryTruncation n
  let alpha := zetaSpectralCoordinate i
  let rho : NontrivialZetaZero :=
    ⟨i, (riemannXi_eq_zero_iff_isNontrivialZetaZero i).mp
      (riemannXi_eq_zero_of_divisor_ball_ne_zero hi)⟩
  have hR : 0 < R := xiCanonicalRadius_pos n
  have hδ : 0 < spectralBoundarySeparation n :=
    spectralBoundarySeparation_pos n
  have hiBall : i ∈ ball (0 : ℂ) R := by
    exact (divisor riemannXi (ball 0 R)).supportWithinDomain
      (by simpa [R] using hi)
  have hsep : spectralBoundarySeparation n ≤ |T - alpha.re| := by
    simpa [T, alpha, rho] using
      spectralBoundarySeparation_le_abs_quantitative_sub_zero_re n rho
  have hgap : T ≠ alpha.re := by
    exact sub_ne_zero.mp (abs_pos.mp (hδ.trans_le hsep))
  have halphaIm : |alpha.im| ≤ 1 / 2 := by
    exact (NontrivialZetaZero.abs_spectralCoordinate_im_lt_half rho).le
  have hleftIntegrable : IntervalIntegrable
      (fun y : ℝ ↦
        ‖logDeriv (Complex.canonicalFactor R i)
          (completedSpectralCoordinate
            ((T : ℂ) + (y : ℂ) * Complex.I))‖)
      volume (-1) 1 :=
    (by
      simpa [R, T] using
        (intervalIntegrable_logDeriv_canonicalFactor_quantitative n hi).norm)
  have hinvContinuous : Continuous
      (fun y : ℝ ↦
        ‖((T : ℂ) + (y : ℂ) * Complex.I) - alpha‖⁻¹) := by
    apply Continuous.inv₀ (by fun_prop)
    intro y hzero
    have hsub : ((T : ℂ) + (y : ℂ) * Complex.I) - alpha = 0 :=
      norm_eq_zero.mp hzero
    apply hgap
    have hre := congrArg Complex.re hsub
    exact sub_eq_zero.mp (by simpa using hre)
  have hinvIntegrable : IntervalIntegrable
      (fun y : ℝ ↦
        ‖((T : ℂ) + (y : ℂ) * Complex.I) - alpha‖⁻¹)
      volume (-1) 1 :=
    hinvContinuous.intervalIntegrable (-1) 1
  have hrightIntegrable : IntervalIntegrable
      (fun y : ℝ ↦ 2 / R +
        ‖((T : ℂ) + (y : ℂ) * Complex.I) - alpha‖⁻¹)
      volume (-1) 1 :=
    intervalIntegrable_const.add hinvIntegrable
  have hpoint (y : ℝ) (hy : y ∈ Icc (-1 : ℝ) 1) :
      ‖logDeriv (Complex.canonicalFactor R i)
          (completedSpectralCoordinate
            ((T : ℂ) + (y : ℂ) * Complex.I))‖ ≤
        2 / R +
          ‖((T : ℂ) + (y : ℂ) * Complex.I) - alpha‖⁻¹ := by
    let w : ℂ := (T : ℂ) + (y : ℂ) * Complex.I
    let s := completedSpectralCoordinate w
    have hsquarter : ‖s‖ ≤ R / 4 := by
      simpa [s, w, T, R] using
        norm_quantitativeCompletedCoordinate_le_quarter n hy.1 hy.2
    have hsi : s ≠ i := by
      intro hs
      have hxi := riemannXi_quantitativeCompletedCoordinate_ne_zero n y
      apply hxi
      rw [show completedSpectralCoordinate
          (((quantitativeSpectralBoundaryTruncation n : ℝ) : ℂ) +
            (y : ℂ) * Complex.I) = i by simpa [s, w, T] using hs]
      exact riemannXi_eq_zero_of_divisor_ball_ne_zero hi
    calc
      ‖logDeriv (Complex.canonicalFactor R i) s‖ ≤
          2 / R + 1 / ‖s - i‖ :=
        norm_logDeriv_canonicalFactor_le_radial_add_inv
          hR hiBall hsquarter hsi
      _ = 2 / R + ‖w - alpha‖⁻¹ := by
        rw [norm_completedSpectralCoordinate_sub]
        simp only [alpha, one_div]
  have hmono :
      (∫ y : ℝ in (-1 : ℝ)..1,
        ‖logDeriv (Complex.canonicalFactor R i)
          (completedSpectralCoordinate
            ((T : ℂ) + (y : ℂ) * Complex.I))‖) ≤
        ∫ y : ℝ in (-1 : ℝ)..1,
          (2 / R +
            ‖((T : ℂ) + (y : ℂ) * Complex.I) - alpha‖⁻¹) := by
    exact intervalIntegral.integral_mono_on (by norm_num)
      hleftIntegrable hrightIntegrable hpoint
  have hinvBound :
      (∫ y : ℝ in (-1 : ℝ)..1,
        ‖((T : ℂ) + (y : ℂ) * Complex.I) - alpha‖⁻¹) ≤
        2 * Real.log (1 + 3 / spectralBoundarySeparation n) :=
    intervalIntegral_inv_norm_vertical_sub_le_log hδ hsep halphaIm
  calc
    (∫ y : ℝ in (-1 : ℝ)..1,
        ‖logDeriv (Complex.canonicalFactor R i)
          (completedSpectralCoordinate
            ((T : ℂ) + (y : ℂ) * Complex.I))‖) ≤
      ∫ y : ℝ in (-1 : ℝ)..1,
        (2 / R +
          ‖((T : ℂ) + (y : ℂ) * Complex.I) - alpha‖⁻¹) := hmono
    _ = 4 / R +
        (∫ y : ℝ in (-1 : ℝ)..1,
          ‖((T : ℂ) + (y : ℂ) * Complex.I) - alpha‖⁻¹) := by
      rw [intervalIntegral.integral_add intervalIntegrable_const
        hinvIntegrable, intervalIntegral.integral_const]
      simp only [sub_neg_eq_add, smul_eq_mul]
      norm_num
      ring
    _ ≤ 4 / R +
        2 * Real.log (1 + 3 / spectralBoundarySeparation n) :=
      add_le_add (le_refl _) hinvBound

/-! ## The complete finite canonical-factor sum -/

/-- The multiplicity-weighted finite canonical logarithmic-derivative sum is
interval integrable on the quantitative vertical segment. -/
theorem intervalIntegrable_canonicalLogDerivSum_quantitative (n : ℕ) :
    IntervalIntegrable
      (fun y : ℝ ↦
        ∑ᶠ i, divisor riemannXi
            (ball 0 (xiCanonicalRadius n)) i •
          logDeriv (Complex.canonicalFactor (xiCanonicalRadius n) i)
            (completedSpectralCoordinate
              ((quantitativeSpectralBoundaryTruncation n : ℂ) +
                (y : ℂ) * Complex.I)))
      volume (-1) 1 := by
  classical
  let R := xiCanonicalRadius n
  let T := quantitativeSpectralBoundaryTruncation n
  let d : ℂ → ℤ := fun i ↦ divisor riemannXi (ball 0 R) i
  let F : ℂ → ℝ → ℂ := fun i y ↦
    logDeriv (Complex.canonicalFactor R i)
      (completedSpectralCoordinate
        ((T : ℂ) + (y : ℂ) * Complex.I))
  have hdFinite : (Function.support d).Finite := by
    simpa [d] using
      (riemannXiCanonicalResidual_decomp n).meromorphicOn
        |>.divisor_ball_support_finite
  have hFIntegrable (i : ℂ) (hi : i ∈ hdFinite.toFinset) :
      IntervalIntegrable (F i) volume (-1) 1 := by
    have hdi : d i ≠ 0 := by
      simpa [Function.mem_support] using hdFinite.mem_toFinset.mp hi
    have hdi' : divisor riemannXi
        (ball 0 (xiCanonicalRadius n)) i ≠ 0 := by
      simpa [d, R] using hdi
    simpa [F, R, T] using
      intervalIntegrable_logDeriv_canonicalFactor_quantitative n hdi'
  have hsum : IntervalIntegrable
      (fun y : ℝ ↦
        ∑ i ∈ hdFinite.toFinset, d i • F i y)
      volume (-1) 1 := by
    have h := IntervalIntegrable.sum hdFinite.toFinset
      (fun i hi ↦ (hFIntegrable i hi).smul (d i))
    have heq :
        (∑ i ∈ hdFinite.toFinset, d i • F i) =
          (fun y : ℝ ↦
            ∑ i ∈ hdFinite.toFinset, d i • F i y) := by
      funext y
      simp
    rw [← heq]
    exact h
  have hrewrite (y : ℝ) :
      (∑ᶠ i, d i • F i y) =
        ∑ i ∈ hdFinite.toFinset, d i • F i y := by
    apply finsum_eq_sum_of_support_subset
    intro i hi
    apply hdFinite.mem_toFinset.mpr
    intro hdi
    apply hi
    simp [hdi]
  have heq :
      (fun y : ℝ ↦ ∑ᶠ i, d i • F i y) =
        (fun y : ℝ ↦
          ∑ i ∈ hdFinite.toFinset, d i • F i y) := by
    funext y
    exact hrewrite y
  change IntervalIntegrable
    (fun y : ℝ ↦ ∑ᶠ i, d i • F i y) volume (-1) 1
  rw [heq]
  exact hsum

/-- After rewriting the canonical `finsum` over its finite support, the
integral of its norm is bounded by total divisor multiplicity times the
single-factor logarithmic cost. -/
theorem intervalIntegral_norm_canonicalLogDerivSum_quantitative_le
    (n : ℕ) :
    (∫ y : ℝ in (-1 : ℝ)..1,
      ‖∑ᶠ i, divisor riemannXi
          (ball 0 (xiCanonicalRadius n)) i •
        logDeriv (Complex.canonicalFactor (xiCanonicalRadius n) i)
          (completedSpectralCoordinate
            ((quantitativeSpectralBoundaryTruncation n : ℂ) +
              (y : ℂ) * Complex.I))‖) ≤
      ((∑ᶠ i, divisor riemannXi
          (ball 0 (xiCanonicalRadius n)) i : ℤ) : ℝ) *
        (4 / xiCanonicalRadius n +
          2 * Real.log (1 + 3 / spectralBoundarySeparation n)) := by
  classical
  let R := xiCanonicalRadius n
  let T := quantitativeSpectralBoundaryTruncation n
  let d : ℂ → ℤ := fun i ↦ divisor riemannXi (ball 0 R) i
  let F : ℂ → ℝ → ℂ := fun i y ↦
    logDeriv (Complex.canonicalFactor R i)
      (completedSpectralCoordinate
        ((T : ℂ) + (y : ℂ) * Complex.I))
  let C : ℝ := 4 / R +
    2 * Real.log (1 + 3 / spectralBoundarySeparation n)
  have hdFinite : (Function.support d).Finite := by
    simpa [d] using
      (riemannXiCanonicalResidual_decomp n).meromorphicOn
        |>.divisor_ball_support_finite
  have hdnonneg : ∀ i, 0 ≤ d i := by
    intro i
    exact (analyticOnNhd_riemannXi.mono (subset_univ _)).divisor_nonneg i
  have hdmem {i : ℂ} (hi : i ∈ hdFinite.toFinset) : d i ≠ 0 := by
    simpa [Function.mem_support] using hdFinite.mem_toFinset.mp hi
  have hFIntegrable (i : ℂ) (hi : i ∈ hdFinite.toFinset) :
      IntervalIntegrable (F i) volume (-1) 1 := by
    have hdi : divisor riemannXi
        (ball 0 (xiCanonicalRadius n)) i ≠ 0 := by
      simpa [d, R] using hdmem hi
    simpa [F, R, T] using
      intervalIntegrable_logDeriv_canonicalFactor_quantitative n hdi
  have hsupport (y : ℝ) :
      Function.support (fun i ↦ d i • F i y) ⊆ hdFinite.toFinset := by
    intro i hi
    apply hdFinite.mem_toFinset.mpr
    intro hdi
    apply hi
    simp [hdi]
  have hrewrite (y : ℝ) :
      (∑ᶠ i, d i • F i y) =
        ∑ i ∈ hdFinite.toFinset, d i • F i y :=
    finsum_eq_sum_of_support_subset _ (hsupport y)
  have hsumIntegrable : IntervalIntegrable
      (fun y : ℝ ↦
        ∑ i ∈ hdFinite.toFinset, d i • F i y)
      volume (-1) 1 := by
    have h := IntervalIntegrable.sum hdFinite.toFinset
      (fun i hi ↦ (hFIntegrable i hi).smul (d i))
    have heq :
        (∑ i ∈ hdFinite.toFinset, d i • F i) =
          (fun y : ℝ ↦
            ∑ i ∈ hdFinite.toFinset, d i • F i y) := by
      funext y
      simp
    rw [← heq]
    exact h
  have hweightedIntegrable : IntervalIntegrable
      (fun y : ℝ ↦
        ∑ i ∈ hdFinite.toFinset,
          ((d i : ℤ) : ℝ) * ‖F i y‖)
      volume (-1) 1 := by
    have h := IntervalIntegrable.sum hdFinite.toFinset
      (fun i hi ↦
        (hFIntegrable i hi).norm.const_mul (((d i : ℤ) : ℝ)))
    have heq :
        (∑ i ∈ hdFinite.toFinset,
          fun y : ℝ ↦ ((d i : ℤ) : ℝ) * ‖F i y‖) =
          (fun y : ℝ ↦
            ∑ i ∈ hdFinite.toFinset,
              ((d i : ℤ) : ℝ) * ‖F i y‖) := by
      funext y
      simp
    rw [← heq]
    exact h
  have hpoint (y : ℝ) :
      ‖∑ i ∈ hdFinite.toFinset, d i • F i y‖ ≤
        ∑ i ∈ hdFinite.toFinset,
          ((d i : ℤ) : ℝ) * ‖F i y‖ := by
    calc
      ‖∑ i ∈ hdFinite.toFinset, d i • F i y‖ ≤
          ∑ i ∈ hdFinite.toFinset, ‖d i • F i y‖ :=
        norm_sum_le _ _
      _ = ∑ i ∈ hdFinite.toFinset,
          ((d i : ℤ) : ℝ) * ‖F i y‖ := by
        apply Finset.sum_congr rfl
        intro i _hi
        rw [norm_zsmul ℂ]
        rw [Complex.norm_int_of_nonneg (hdnonneg i)]
  have hmono :
      (∫ y : ℝ in (-1 : ℝ)..1,
        ‖∑ i ∈ hdFinite.toFinset, d i • F i y‖) ≤
        ∫ y : ℝ in (-1 : ℝ)..1,
          ∑ i ∈ hdFinite.toFinset,
            ((d i : ℤ) : ℝ) * ‖F i y‖ := by
    exact intervalIntegral.integral_mono_on (by norm_num)
      hsumIntegrable.norm hweightedIntegrable (fun y _hy ↦ hpoint y)
  have hfactorBound (i : ℂ) (hi : i ∈ hdFinite.toFinset) :
      (∫ y : ℝ in (-1 : ℝ)..1, ‖F i y‖) ≤ C := by
    have hdi : divisor riemannXi
        (ball 0 (xiCanonicalRadius n)) i ≠ 0 := by
      simpa [d, R] using hdmem hi
    simpa [F, C, R, T] using
      intervalIntegral_norm_logDeriv_canonicalFactor_quantitative_le n hdi
  change (∫ y : ℝ in (-1 : ℝ)..1,
      ‖∑ᶠ i, d i • F i y‖) ≤ ((∑ᶠ i, d i : ℤ) : ℝ) * C
  calc
    (∫ y : ℝ in (-1 : ℝ)..1,
        ‖∑ᶠ i, d i • F i y‖) =
      ∫ y : ℝ in (-1 : ℝ)..1,
        ‖∑ i ∈ hdFinite.toFinset, d i • F i y‖ := by
      apply intervalIntegral.integral_congr
      intro y _hy
      change ‖∑ᶠ i, d i • F i y‖ =
        ‖∑ i ∈ hdFinite.toFinset, d i • F i y‖
      rw [hrewrite y]
    _ ≤ ∫ y : ℝ in (-1 : ℝ)..1,
        ∑ i ∈ hdFinite.toFinset,
          ((d i : ℤ) : ℝ) * ‖F i y‖ := hmono
    _ = ∑ i ∈ hdFinite.toFinset,
        ((d i : ℤ) : ℝ) *
          (∫ y : ℝ in (-1 : ℝ)..1, ‖F i y‖) := by
      rw [intervalIntegral.integral_finsetSum]
      · apply Finset.sum_congr rfl
        intro i _hi
        rw [intervalIntegral.integral_const_mul]
      · intro i hi
        exact (hFIntegrable i hi).norm.const_mul (((d i : ℤ) : ℝ))
    _ ≤ ∑ i ∈ hdFinite.toFinset, ((d i : ℤ) : ℝ) * C := by
      apply Finset.sum_le_sum
      intro i hi
      exact mul_le_mul_of_nonneg_left (hfactorBound i hi) (by
        exact_mod_cast hdnonneg i)
    _ = (∑ᶠ i, ((d i : ℤ) : ℝ)) * C := by
      rw [← Finset.sum_mul]
      congr 1
      symm
      exact finsum_eq_sum_of_support_subset _ (by
        intro i hi
        apply hdFinite.mem_toFinset.mpr
        intro hdi
        apply hi
        simp [hdi])
    _ = ((∑ᶠ i, d i : ℤ) : ℝ) * C := by
      congr 1
      exact (map_finsum (Int.castRingHom ℝ) hdFinite).symm

/-- With subquadratic xi growth, the complete canonical-factor contribution
retains the strict `3/2` exponent and pays only the logarithmic contour-gap
cost. -/
theorem intervalIntegral_norm_canonicalLogDerivSum_quantitative_le_of_growth
    {A : ℝ} (hA : 1 ≤ A)
    (hbound : ∀ z : ℂ,
      ‖riemannXi z‖ ≤
        Real.exp (A * (‖z‖ + 1) ^ (3 / 2 : ℝ)))
    (n : ℕ) :
    (∫ y : ℝ in (-1 : ℝ)..1,
      ‖∑ᶠ i, divisor riemannXi
          (ball 0 (xiCanonicalRadius n)) i •
        logDeriv (Complex.canonicalFactor (xiCanonicalRadius n) i)
          (completedSpectralCoordinate
            ((quantitativeSpectralBoundaryTruncation n : ℂ) +
              (y : ℂ) * Complex.I))‖) ≤
      (A * (2 * xiCanonicalRadius n + 1) ^ (3 / 2 : ℝ) /
          Real.log 2) *
        (4 / xiCanonicalRadius n +
          2 * Real.log (1 + 3 / spectralBoundarySeparation n)) := by
  have hraw := intervalIntegral_norm_canonicalLogDerivSum_quantitative_le n
  have hcount :=
    sum_divisor_riemannXi_ball_le_threeHalves_of_growth hA hbound n
  have hcost : 0 ≤ 4 / xiCanonicalRadius n +
      2 * Real.log (1 + 3 / spectralBoundarySeparation n) := by
    have harg : 1 ≤ 1 + 3 / spectralBoundarySeparation n := by
      have hsep := spectralBoundarySeparation_pos n
      have hquot : 0 ≤ 3 / spectralBoundarySeparation n := by positivity
      linarith
    have hR := xiCanonicalRadius_pos n
    exact add_nonneg (by positivity)
      (mul_nonneg (by norm_num) (Real.log_nonneg harg))
  exact hraw.trans (mul_le_mul_of_nonneg_right hcount hcost)

/-! ## The zero-free canonical residual -/

/-- The logarithmic derivative of the zero-free canonical residual is
interval integrable on the complete quantitative vertical segment. -/
theorem intervalIntegrable_logDeriv_riemannXiCanonicalResidual_quantitative
    (n : ℕ) :
    IntervalIntegrable
      (fun y : ℝ ↦
        logDeriv (riemannXiCanonicalResidual n)
          (completedSpectralCoordinate
            ((quantitativeSpectralBoundaryTruncation n : ℂ) +
              (y : ℂ) * Complex.I)))
      volume (-1) 1 := by
  let R := xiCanonicalRadius n
  let T := quantitativeSpectralBoundaryTruncation n
  have hR : 0 < R := xiCanonicalRadius_pos n
  have hcontinuous : ContinuousOn
      (fun y : ℝ ↦
        logDeriv (riemannXiCanonicalResidual n)
          (completedSpectralCoordinate
            ((T : ℂ) + (y : ℂ) * Complex.I)))
      (Icc (-1 : ℝ) 1) := by
    intro y hy
    let s := completedSpectralCoordinate
      ((T : ℂ) + (y : ℂ) * Complex.I)
    have hsquarter : ‖s‖ ≤ R / 4 := by
      simpa [s, T, R] using
        norm_quantitativeCompletedCoordinate_le_quarter n hy.1 hy.2
    have hsclosed : s ∈ closedBall (0 : ℂ) R := by
      rw [mem_closedBall, dist_zero_right]
      exact hsquarter.trans (by linarith)
    have hresidual :=
      (riemannXiCanonicalResidual_decomp n).analyticOnNhd s hsclosed
    have hresidualNe :=
      (riemannXiCanonicalResidual_decomp n).ne_zero s hsclosed
    have hlog : AnalyticAt ℂ
        (logDeriv (riemannXiCanonicalResidual n)) s := by
      simpa only [logDeriv] using
        hresidual.deriv.div hresidual hresidualNe
    have hcurve : Continuous
        (fun u : ℝ ↦ completedSpectralCoordinate
          ((T : ℂ) + (u : ℂ) * Complex.I)) := by
      unfold completedSpectralCoordinate
      continuity
    have hcomp : ContinuousAt
        (fun u : ℝ ↦
          logDeriv (riemannXiCanonicalResidual n)
            (completedSpectralCoordinate
              ((T : ℂ) + (u : ℂ) * Complex.I))) y := by
      apply ContinuousAt.comp'
        (f := fun u : ℝ ↦ completedSpectralCoordinate
          ((T : ℂ) + (u : ℂ) * Complex.I))
        (g := logDeriv (riemannXiCanonicalResidual n))
      · simpa only [s] using hlog.continuousAt
      · exact hcurve.continuousAt
    exact hcomp.continuousWithinAt
  exact hcontinuous.intervalIntegrable_of_Icc (by norm_num)

/-- The existing Cauchy estimate for the zero-free residual gives an
explicit length-two `L¹` bound on the quantitative segment. -/
theorem intervalIntegral_norm_logDeriv_riemannXiCanonicalResidual_quantitative_le_of_growth
    {B : ℝ} (hB : 1 ≤ B)
    (hbound : ∀ z : ℂ,
      ‖riemannXi z‖ ≤ Real.exp (B * (‖z‖ + 1) ^ 2))
    (n : ℕ) :
    (∫ y : ℝ in (-1 : ℝ)..1,
      ‖logDeriv (riemannXiCanonicalResidual n)
        (completedSpectralCoordinate
          ((quantitativeSpectralBoundaryTruncation n : ℂ) +
            (y : ℂ) * Complex.I))‖) ≤
      2 * ((2 * (B * (xiCanonicalRadius n + 1) ^ 2)) /
        (xiCanonicalRadius n / 4)) := by
  let R := xiCanonicalRadius n
  let T := quantitativeSpectralBoundaryTruncation n
  let M := (2 * (B * (R + 1) ^ 2)) / (R / 4)
  have hleftIntegrable : IntervalIntegrable
      (fun y : ℝ ↦
        ‖logDeriv (riemannXiCanonicalResidual n)
          (completedSpectralCoordinate
            ((T : ℂ) + (y : ℂ) * Complex.I))‖)
      volume (-1) 1 := by
    simpa [T] using
      (intervalIntegrable_logDeriv_riemannXiCanonicalResidual_quantitative n).norm
  have hpoint (y : ℝ) (hy : y ∈ Icc (-1 : ℝ) 1) :
      ‖logDeriv (riemannXiCanonicalResidual n)
          (completedSpectralCoordinate
            ((T : ℂ) + (y : ℂ) * Complex.I))‖ ≤ M := by
    have hsquarter :=
      norm_quantitativeCompletedCoordinate_le_quarter n hy.1 hy.2
    simpa [M, R, T] using
      norm_logDeriv_riemannXiCanonicalResidual_le_of_growth
        hB hbound n hsquarter
  have hmono :
      (∫ y : ℝ in (-1 : ℝ)..1,
        ‖logDeriv (riemannXiCanonicalResidual n)
          (completedSpectralCoordinate
            ((T : ℂ) + (y : ℂ) * Complex.I))‖) ≤
        ∫ _y : ℝ in (-1 : ℝ)..1, M := by
    exact intervalIntegral.integral_mono_on (by norm_num)
      hleftIntegrable intervalIntegrable_const hpoint
  calc
    (∫ y : ℝ in (-1 : ℝ)..1,
        ‖logDeriv (riemannXiCanonicalResidual n)
          (completedSpectralCoordinate
            ((T : ℂ) + (y : ℂ) * Complex.I))‖) ≤
      ∫ _y : ℝ in (-1 : ℝ)..1, M := hmono
    _ = 2 * M := by
      rw [intervalIntegral.integral_const]
      simp only [sub_neg_eq_add, smul_eq_mul]
      norm_num
    _ = 2 * ((2 * (B * (xiCanonicalRadius n + 1) ^ 2)) /
        (xiCanonicalRadius n / 4)) := by
      rfl

/-! ## The complete right-line xi logarithmic derivative -/

/-- The genuine spectral-xi negative logarithmic derivative is interval
integrable on every quantitatively separated vertical segment. -/
theorem intervalIntegrable_xiSpectralNegativeLogDerivative_quantitative
    (n : ℕ) :
    IntervalIntegrable
      (fun y : ℝ ↦
        xiSpectralNegativeLogDerivative
          ((quantitativeSpectralBoundaryTruncation n : ℂ) +
            (y : ℂ) * Complex.I))
      volume (-1) 1 := by
  let T := quantitativeSpectralBoundaryTruncation n
  let w : ℝ → ℂ := fun y ↦ (T : ℂ) + (y : ℂ) * Complex.I
  have hw : Continuous w := by
    dsimp only [w]
    fun_prop
  have hcontinuous : Continuous
      (fun y : ℝ ↦ xiSpectralNegativeLogDerivative (w y)) := by
    apply continuous_comp_of_forall_analyticAt
      xiSpectralNegativeLogDerivative w hw
    intro y
    apply analyticAt_xiSpectralNegativeLogDerivative_of_ne
    simpa [riemannXiSpectral, w, T] using
      riemannXi_quantitativeCompletedCoordinate_ne_zero n y
  simpa [w, T] using hcontinuous.intervalIntegrable (-1) 1

/-- Combining the exact canonical decomposition with the integrated residual
and multiplicity-weighted factor estimates gives the required `L¹` bound for
the genuine spectral-xi negative logarithmic derivative. -/
theorem intervalIntegral_norm_xiSpectralNegativeLogDerivative_quantitative_le_of_growth
    {A B : ℝ} (hA : 1 ≤ A)
    (hThreeHalves : ∀ z : ℂ,
      ‖riemannXi z‖ ≤
        Real.exp (A * (‖z‖ + 1) ^ (3 / 2 : ℝ)))
    (hB : 1 ≤ B)
    (hQuadratic : ∀ z : ℂ,
      ‖riemannXi z‖ ≤ Real.exp (B * (‖z‖ + 1) ^ 2))
    (n : ℕ) :
    (∫ y : ℝ in (-1 : ℝ)..1,
      ‖xiSpectralNegativeLogDerivative
        ((quantitativeSpectralBoundaryTruncation n : ℂ) +
          (y : ℂ) * Complex.I)‖) ≤
      2 * ((2 * (B * (xiCanonicalRadius n + 1) ^ 2)) /
          (xiCanonicalRadius n / 4)) +
        (A * (2 * xiCanonicalRadius n + 1) ^ (3 / 2 : ℝ) /
            Real.log 2) *
          (4 / xiCanonicalRadius n +
            2 * Real.log (1 + 3 / spectralBoundarySeparation n)) := by
  let R := xiCanonicalRadius n
  let T := quantitativeSpectralBoundaryTruncation n
  let w : ℝ → ℂ := fun y ↦ (T : ℂ) + (y : ℂ) * Complex.I
  let s : ℝ → ℂ := fun y ↦ completedSpectralCoordinate (w y)
  let d : ℂ → ℤ := fun i ↦ divisor riemannXi (ball 0 R) i
  let S : ℝ → ℂ := fun y ↦
    ∑ᶠ i, d i • logDeriv (Complex.canonicalFactor R i) (s y)
  have hR : 0 < R := xiCanonicalRadius_pos n
  have hwContinuous : Continuous w := by
    dsimp only [w]
    fun_prop
  have hleftContinuous : Continuous
      (fun y : ℝ ↦ xiSpectralNegativeLogDerivative (w y)) := by
    apply continuous_comp_of_forall_analyticAt
      xiSpectralNegativeLogDerivative w hwContinuous
    intro y
    apply analyticAt_xiSpectralNegativeLogDerivative_of_ne
    simpa [riemannXiSpectral, w, T] using
      riemannXi_quantitativeCompletedCoordinate_ne_zero n y
  have hleftIntegrable : IntervalIntegrable
      (fun y : ℝ ↦ ‖xiSpectralNegativeLogDerivative (w y)‖)
      volume (-1) 1 :=
    hleftContinuous.norm.intervalIntegrable (-1) 1
  have hresidualIntegrable : IntervalIntegrable
      (fun y : ℝ ↦
        ‖logDeriv (riemannXiCanonicalResidual n) (s y)‖)
      volume (-1) 1 := by
    simpa [s, w, T] using
      (intervalIntegrable_logDeriv_riemannXiCanonicalResidual_quantitative n).norm
  have hsumIntegrable : IntervalIntegrable
      (fun y : ℝ ↦ ‖S y‖) volume (-1) 1 := by
    simpa [S, d, s, w, R, T] using
      (intervalIntegrable_canonicalLogDerivSum_quantitative n).norm
  have hpoint (y : ℝ) (hy : y ∈ Icc (-1 : ℝ) 1) :
      ‖xiSpectralNegativeLogDerivative (w y)‖ ≤
        ‖logDeriv (riemannXiCanonicalResidual n) (s y)‖ + ‖S y‖ := by
    have hsquarter : ‖s y‖ ≤ R / 4 := by
      simpa [s, w, T, R] using
        norm_quantitativeCompletedCoordinate_le_quarter n hy.1 hy.2
    have hsball : s y ∈ ball (0 : ℂ) R := by
      rw [mem_ball, dist_zero_right]
      exact hsquarter.trans_lt (by linarith)
    have hxi : riemannXi (s y) ≠ 0 := by
      simpa [s, w, T] using
        riemannXi_quantitativeCompletedCoordinate_ne_zero n y
    have hdecomp := logDeriv_riemannXi_eq_residual_sub_canonical_sum n
      hsball hxi
    calc
      ‖xiSpectralNegativeLogDerivative (w y)‖ =
          ‖logDeriv riemannXi (s y)‖ := by
        exact norm_xiSpectralNegativeLogDerivative (w y)
      _ = ‖logDeriv (riemannXiCanonicalResidual n) (s y) - S y‖ := by
        rw [hdecomp]
      _ ≤ ‖logDeriv (riemannXiCanonicalResidual n) (s y)‖ + ‖S y‖ :=
        norm_sub_le _ _
  have hmono :
      (∫ y : ℝ in (-1 : ℝ)..1,
        ‖xiSpectralNegativeLogDerivative (w y)‖) ≤
        ∫ y : ℝ in (-1 : ℝ)..1,
          (‖logDeriv (riemannXiCanonicalResidual n) (s y)‖ + ‖S y‖) := by
    exact intervalIntegral.integral_mono_on (by norm_num)
      hleftIntegrable (hresidualIntegrable.add hsumIntegrable) hpoint
  have hresidualBound :=
    intervalIntegral_norm_logDeriv_riemannXiCanonicalResidual_quantitative_le_of_growth
      hB hQuadratic n
  have hsumBound :=
    intervalIntegral_norm_canonicalLogDerivSum_quantitative_le_of_growth
      hA hThreeHalves n
  calc
    (∫ y : ℝ in (-1 : ℝ)..1,
        ‖xiSpectralNegativeLogDerivative (w y)‖) ≤
      ∫ y : ℝ in (-1 : ℝ)..1,
        (‖logDeriv (riemannXiCanonicalResidual n) (s y)‖ + ‖S y‖) := hmono
    _ = (∫ y : ℝ in (-1 : ℝ)..1,
          ‖logDeriv (riemannXiCanonicalResidual n) (s y)‖) +
        (∫ y : ℝ in (-1 : ℝ)..1, ‖S y‖) := by
      rw [intervalIntegral.integral_add hresidualIntegrable hsumIntegrable]
    _ ≤ 2 * ((2 * (B * (R + 1) ^ 2)) / (R / 4)) +
        (A * (2 * R + 1) ^ (3 / 2 : ℝ) / Real.log 2) *
          (4 / R +
            2 * Real.log (1 + 3 / spectralBoundarySeparation n)) := by
      exact add_le_add
        (by simpa [s, w, R, T] using hresidualBound)
        (by simpa [S, d, s, w, R, T] using hsumBound)

/-! ## Attaching Suzuki's inverse-square transform -/

/-- A uniform pointwise bound on one factor can be pulled outside an
interval integral against an interval-integrable complex function. -/
theorem norm_intervalIntegral_mul_le_const_mul_integral_norm
    {H L : ℝ → ℂ} {M : ℝ}
    (hL : IntervalIntegrable L volume (-1) 1)
    (hH : ∀ y ∈ Ioc (-1 : ℝ) 1, ‖H y‖ ≤ M) :
    ‖∫ y : ℝ in (-1 : ℝ)..1, H y * L y‖ ≤
      M * (∫ y : ℝ in (-1 : ℝ)..1, ‖L y‖) := by
  have hmajorant : IntervalIntegrable
      (fun y : ℝ ↦ M * ‖L y‖) volume (-1) 1 :=
    hL.norm.const_mul M
  have hnorm :
      ‖∫ y : ℝ in (-1 : ℝ)..1, H y * L y‖ ≤
        ∫ y : ℝ in (-1 : ℝ)..1, M * ‖L y‖ := by
    apply intervalIntegral.norm_integral_le_of_norm_le (by norm_num)
      (Filter.Eventually.of_forall fun y hy ↦ ?_) hmajorant
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_right (hH y hy) (norm_nonneg _)
  calc
    ‖∫ y : ℝ in (-1 : ℝ)..1, H y * L y‖ ≤
        ∫ y : ℝ in (-1 : ℝ)..1, M * ‖L y‖ := hnorm
    _ = M * (∫ y : ℝ in (-1 : ℝ)..1, ‖L y‖) := by
      rw [intervalIntegral.integral_const_mul]

/-- The right vertical Suzuki-weighted xi integral is bounded by the
inverse-square transform constant times the checked `L¹` logarithmic-
derivative norm. -/
theorem norm_intervalIntegral_suzukiXiWeil_quantitative_right_le
    (t : ℝ) (z : ℂ) (n : ℕ)
    (hzT : 2 * |z.re| ≤ quantitativeSpectralBoundaryTruncation n) :
    ‖∫ y : ℝ in (-1 : ℝ)..1,
      suzukiWeilSpectralTransform t z
          ((quantitativeSpectralBoundaryTruncation n : ℂ) +
            (y : ℂ) * Complex.I) *
        xiSpectralNegativeLogDerivative
          ((quantitativeSpectralBoundaryTruncation n : ℂ) +
            (y : ℂ) * Complex.I)‖ ≤
      (2 * (Real.exp |t| + 1) /
          quantitativeSpectralBoundaryTruncation n ^ 2) *
        (∫ y : ℝ in (-1 : ℝ)..1,
          ‖xiSpectralNegativeLogDerivative
            ((quantitativeSpectralBoundaryTruncation n : ℂ) +
              (y : ℂ) * Complex.I)‖) := by
  apply norm_intervalIntegral_mul_le_const_mul_integral_norm
    (intervalIntegrable_xiSpectralNegativeLogDerivative_quantitative n)
  intro y hy
  apply norm_suzukiWeilSpectralTransform_quantitative_right_le t z n y
  · exact (abs_le).mpr ⟨hy.1.le, hy.2⟩
  · exact hzT

/-- The reflected-left Suzuki transform obeys the identical weighted
right-line integral bound. -/
theorem norm_intervalIntegral_suzukiXiWeil_quantitative_left_le
    (t : ℝ) (z : ℂ) (n : ℕ)
    (hzT : 2 * |z.re| ≤ quantitativeSpectralBoundaryTruncation n) :
    ‖∫ y : ℝ in (-1 : ℝ)..1,
      suzukiWeilSpectralTransform t z
          (-((quantitativeSpectralBoundaryTruncation n : ℂ) +
            (y : ℂ) * Complex.I)) *
        xiSpectralNegativeLogDerivative
          ((quantitativeSpectralBoundaryTruncation n : ℂ) +
            (y : ℂ) * Complex.I)‖ ≤
      (2 * (Real.exp |t| + 1) /
          quantitativeSpectralBoundaryTruncation n ^ 2) *
        (∫ y : ℝ in (-1 : ℝ)..1,
          ‖xiSpectralNegativeLogDerivative
            ((quantitativeSpectralBoundaryTruncation n : ℂ) +
              (y : ℂ) * Complex.I)‖) := by
  apply norm_intervalIntegral_mul_le_const_mul_integral_norm
    (intervalIntegrable_xiSpectralNegativeLogDerivative_quantitative n)
  intro y hy
  apply norm_suzukiWeilSpectralTransform_quantitative_left_le t z n y
  · exact (abs_le).mpr ⟨hy.1.le, hy.2⟩
  · exact hzT

/-- The literal two-sided vertical boundary is controlled by twice the
inverse-square Suzuki constant times the right-line xi logarithmic-derivative
`L¹` norm. -/
theorem norm_suzukiXiWeilVerticalBoundaryIntegral_quantitative_le
    (t : ℝ) (z : ℂ) (n : ℕ)
    (hzT : 2 * |z.re| ≤ quantitativeSpectralBoundaryTruncation n) :
    ‖suzukiXiWeilVerticalBoundaryIntegral t z
        (quantitativeSpectralBoundaryTruncation n)‖ ≤
      2 * ((2 * (Real.exp |t| + 1) /
          quantitativeSpectralBoundaryTruncation n ^ 2) *
        (∫ y : ℝ in (-1 : ℝ)..1,
          ‖xiSpectralNegativeLogDerivative
            ((quantitativeSpectralBoundaryTruncation n : ℂ) +
              (y : ℂ) * Complex.I)‖)) := by
  let T := quantitativeSpectralBoundaryTruncation n
  let L : ℝ → ℂ := fun y ↦ xiSpectralNegativeLogDerivative
    ((T : ℂ) + (y : ℂ) * Complex.I)
  let IR : ℂ := ∫ y : ℝ in (-1 : ℝ)..1,
    suzukiWeilSpectralTransform t z
        ((T : ℂ) + (y : ℂ) * Complex.I) * L y
  let IL : ℂ := ∫ y : ℝ in (-1 : ℝ)..1,
    suzukiWeilSpectralTransform t z
        (-((T : ℂ) + (y : ℂ) * Complex.I)) * L y
  let M : ℝ := 2 * (Real.exp |t| + 1) / T ^ 2
  let J : ℝ := ∫ y : ℝ in (-1 : ℝ)..1, ‖L y‖
  have hright : ‖IR‖ ≤ M * J := by
    simpa [IR, M, J, L, T] using
      norm_intervalIntegral_suzukiXiWeil_quantitative_right_le
        t z n hzT
  have hleft : ‖IL‖ ≤ M * J := by
    simpa [IL, M, J, L, T] using
      norm_intervalIntegral_suzukiXiWeil_quantitative_left_le
        t z n hzT
  rw [suzukiXiWeilVerticalBoundaryIntegral_eq_right_reflection]
  change ‖Complex.I * IR + Complex.I * IL‖ ≤ 2 * (M * J)
  calc
    ‖Complex.I * IR + Complex.I * IL‖ ≤
        ‖Complex.I * IR‖ + ‖Complex.I * IL‖ := norm_add_le _ _
    _ = ‖IR‖ + ‖IL‖ := by simp
    _ ≤ M * J + M * J := add_le_add hright hleft
    _ = 2 * (M * J) := by ring

/-- Substituting the complete checked logarithmic-derivative estimate gives
one explicit real majorant for the literal vertical boundary. -/
theorem norm_suzukiXiWeilVerticalBoundaryIntegral_quantitative_le_of_growth
    {A B : ℝ} (hA : 1 ≤ A)
    (hThreeHalves : ∀ w : ℂ,
      ‖riemannXi w‖ ≤
        Real.exp (A * (‖w‖ + 1) ^ (3 / 2 : ℝ)))
    (hB : 1 ≤ B)
    (hQuadratic : ∀ w : ℂ,
      ‖riemannXi w‖ ≤ Real.exp (B * (‖w‖ + 1) ^ 2))
    (t : ℝ) (z : ℂ) (n : ℕ)
    (hzT : 2 * |z.re| ≤ quantitativeSpectralBoundaryTruncation n) :
    ‖suzukiXiWeilVerticalBoundaryIntegral t z
        (quantitativeSpectralBoundaryTruncation n)‖ ≤
      2 * ((2 * (Real.exp |t| + 1) /
          quantitativeSpectralBoundaryTruncation n ^ 2) *
        (2 * ((2 * (B * (xiCanonicalRadius n + 1) ^ 2)) /
            (xiCanonicalRadius n / 4)) +
          (A * (2 * xiCanonicalRadius n + 1) ^ (3 / 2 : ℝ) /
              Real.log 2) *
            (4 / xiCanonicalRadius n +
              2 * Real.log
                (1 + 3 / spectralBoundarySeparation n)))) := by
  have hvertical :=
    norm_suzukiXiWeilVerticalBoundaryIntegral_quantitative_le t z n hzT
  have hlog :=
    intervalIntegral_norm_xiSpectralNegativeLogDerivative_quantitative_le_of_growth
      hA hThreeHalves hB hQuadratic n
  calc
    ‖suzukiXiWeilVerticalBoundaryIntegral t z
        (quantitativeSpectralBoundaryTruncation n)‖ ≤
      2 * ((2 * (Real.exp |t| + 1) /
          quantitativeSpectralBoundaryTruncation n ^ 2) *
        (∫ y : ℝ in (-1 : ℝ)..1,
          ‖xiSpectralNegativeLogDerivative
            ((quantitativeSpectralBoundaryTruncation n : ℂ) +
              (y : ℂ) * Complex.I)‖)) := hvertical
    _ ≤ 2 * ((2 * (Real.exp |t| + 1) /
          quantitativeSpectralBoundaryTruncation n ^ 2) *
        (2 * ((2 * (B * (xiCanonicalRadius n + 1) ^ 2)) /
            (xiCanonicalRadius n / 4)) +
          (A * (2 * xiCanonicalRadius n + 1) ^ (3 / 2 : ℝ) /
              Real.log 2) *
            (4 / xiCanonicalRadius n +
              2 * Real.log
                (1 + 3 / spectralBoundarySeparation n)))) := by
      have hT : 0 < quantitativeSpectralBoundaryTruncation n :=
        (Nat.cast_nonneg n).trans_lt
          (quantitativeSpectralBoundaryTruncation_spec n).1
      gcongr

end

end RiemannGaussian
