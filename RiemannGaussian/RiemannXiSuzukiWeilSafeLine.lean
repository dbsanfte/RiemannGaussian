import RiemannGaussian.RiemannXiSuzukiWeilGlobal
import Mathlib.Analysis.Fourier.Inversion

/-!
# The Suzuki--Weil horizontal safe line

This file reduces the two horizontal sides of the global Suzuki--xi contour
to one lower safe-line integral.  Its spectral weight is then identified with
the ordinary Fourier transform of a continuous, absolutely integrable
symmetrization of Suzuki's literal time-domain Weil test.

These identities are finite or absolutely convergent.  No explicit formula
or Fourier inversion assertion is assumed here.
-/

open Complex Filter MeasureTheory Metric Polynomial Set Topology
open scoped Classical ENNReal FourierTransform Interval Topology lp

namespace RiemannGaussian

noncomputable section

/-! ## Reflection of the two horizontal sides -/

/-- The spectral weight produced by reflecting the upper height-one line to
the lower height-one line. -/
def suzukiWeilSafeLineSpectralWeight
    (t : ℝ) (z : ℂ) (r : ℝ) : ℂ :=
  suzukiWeilSpectralTransform t z ((r : ℂ) - Complex.I) +
    suzukiWeilSpectralTransform t z (((-r : ℝ) : ℂ) + Complex.I)

/-- Pointwise, the upper horizontal Suzuki--xi integrand is the negative
reflection of the lower xi logarithmic derivative, with its Suzuki transform
left at the reflected upper frequency. -/
theorem suzukiXiWeilSpectralIntegrand_upper_reflection
    (t : ℝ) (z : ℂ) (r : ℝ) :
    suzukiXiWeilSpectralIntegrand t z ((r : ℂ) + Complex.I) =
      -(suzukiWeilSpectralTransform t z ((r : ℂ) + Complex.I) *
        xiSpectralNegativeLogDerivative
          (((-r : ℝ) : ℂ) - Complex.I)) := by
  have hpoint : (r : ℂ) + Complex.I =
      -((((-r : ℝ) : ℂ) - Complex.I)) := by
    push_cast
    ring
  unfold suzukiXiWeilSpectralIntegrand
  rw [hpoint, xiSpectralNegativeLogDerivative_neg]
  ring

/-- On a symmetric finite interval, the upper horizontal integral is the
negative of the reflected-transform integral on the lower safe line. -/
theorem intervalIntegral_suzukiXiWeilSpectralIntegrand_upper_reflection
    (t : ℝ) (z : ℂ) (T : ℝ) :
    (∫ r : ℝ in -T..T,
      suzukiXiWeilSpectralIntegrand t z ((r : ℂ) + Complex.I)) =
      -(∫ r : ℝ in -T..T,
        suzukiWeilSpectralTransform t z
            (((-r : ℝ) : ℂ) + Complex.I) *
          xiSpectralNegativeLogDerivative
            ((r : ℂ) - Complex.I)) := by
  calc
    (∫ r : ℝ in -T..T,
        suzukiXiWeilSpectralIntegrand t z ((r : ℂ) + Complex.I)) =
      ∫ r : ℝ in -T..T,
        -(suzukiWeilSpectralTransform t z ((r : ℂ) + Complex.I) *
          xiSpectralNegativeLogDerivative
            (((-r : ℝ) : ℂ) - Complex.I)) := by
        apply intervalIntegral.integral_congr
        intro r _hr
        exact suzukiXiWeilSpectralIntegrand_upper_reflection t z r
    _ = -(∫ r : ℝ in -T..T,
        suzukiWeilSpectralTransform t z ((r : ℂ) + Complex.I) *
          xiSpectralNegativeLogDerivative
            (((-r : ℝ) : ℂ) - Complex.I)) :=
      intervalIntegral.integral_neg
    _ = -(∫ r : ℝ in -T..T,
        suzukiWeilSpectralTransform t z
            (((-r : ℝ) : ℂ) + Complex.I) *
          xiSpectralNegativeLogDerivative
            ((r : ℂ) - Complex.I)) := by
      apply congrArg Neg.neg
      simpa using
        (intervalIntegral.integral_comp_neg
          (f := fun r : ℝ ↦
            suzukiWeilSpectralTransform t z ((r : ℂ) + Complex.I) *
              xiSpectralNegativeLogDerivative
                (((-r : ℝ) : ℂ) - Complex.I))
          (a := -T) (b := T)).symm

/-- For `Im z > 1`, the literal horizontal boundary is exactly one lower
safe-line integral against the reflected Suzuki spectral weight. -/
theorem suzukiXiWeilHorizontalBoundaryIntegral_eq_safeLineWeight
    (t : ℝ) {z : ℂ} (hz : 1 < z.im) (T : ℝ) :
    suzukiXiWeilHorizontalBoundaryIntegral t z T =
      ∫ r : ℝ in -T..T,
        suzukiWeilSafeLineSpectralWeight t z r *
          xiSpectralNegativeLogDerivative ((r : ℂ) - Complex.I) := by
  have hlower : IntervalIntegrable
      (fun r : ℝ ↦
        suzukiWeilSpectralTransform t z ((r : ℂ) - Complex.I) *
          xiSpectralNegativeLogDerivative ((r : ℂ) - Complex.I))
      volume (-T) T := by
    apply (continuous_comp_of_forall_analyticAt
      (suzukiXiWeilSpectralIntegrand t z)
      (fun r : ℝ ↦ (r : ℂ) - Complex.I) (by fun_prop) ?_).intervalIntegrable
    intro r
    apply analyticAt_suzukiXiWeilSpectralIntegrand_of_ne
    · intro heq
      have him := congrArg Complex.im heq
      simp at him
      linarith
    · apply riemannXiSpectral_ne_zero_of_half_le_abs_im
      norm_num
  have hreflected : IntervalIntegrable
      (fun r : ℝ ↦
        suzukiWeilSpectralTransform t z
            (((-r : ℝ) : ℂ) + Complex.I) *
          xiSpectralNegativeLogDerivative ((r : ℂ) - Complex.I))
      volume (-T) T := by
    apply (show Continuous (fun r : ℝ ↦
      suzukiWeilSpectralTransform t z
          (((-r : ℝ) : ℂ) + Complex.I) *
        xiSpectralNegativeLogDerivative ((r : ℂ) - Complex.I)) by
      apply Continuous.mul
      · apply continuous_comp_of_forall_analyticAt
          (suzukiWeilSpectralTransform t z)
          (fun r : ℝ ↦ (((-r : ℝ) : ℂ) + Complex.I)) (by fun_prop)
        intro r
        apply analyticAt_suzukiWeilSpectralTransform_of_ne
        intro heq
        have him := congrArg Complex.im heq
        simp at him
        linarith
      · apply continuous_comp_of_forall_analyticAt
          xiSpectralNegativeLogDerivative
          (fun r : ℝ ↦ (r : ℂ) - Complex.I) (by fun_prop)
        intro r
        apply analyticAt_xiSpectralNegativeLogDerivative_of_ne
        apply riemannXiSpectral_ne_zero_of_half_le_abs_im
        norm_num).intervalIntegrable
  unfold suzukiXiWeilHorizontalBoundaryIntegral
  rw [intervalIntegral_suzukiXiWeilSpectralIntegrand_upper_reflection]
  rw [sub_neg_eq_add]
  unfold suzukiXiWeilSpectralIntegrand
  rw [← intervalIntegral.integral_add hlower hreflected]
  apply intervalIntegral.integral_congr
  intro r _hr
  unfold suzukiWeilSafeLineSpectralWeight
  ring

/-! ## The symmetrized time-domain test -/

/-- Time-domain test whose ordinary Fourier transform is the reflected
height-one spectral weight. -/
def suzukiWeilSymmetricSafeLineTest
    (t : ℝ) (z : ℂ) (x : ℝ) : ℂ :=
  (Real.exp (-x) : ℂ) *
    (suzukiWeilTest t z x + suzukiWeilTest t z (-x))

/-- Suzuki's piecewise Weil test is continuous at both join points. -/
theorem continuous_suzukiWeilTest
    {t : ℝ} (ht : 0 ≤ t) (z : ℂ) :
    Continuous (suzukiWeilTest t z) := by
  let middle : ℝ → ℂ := fun x ↦
    (1 - Complex.exp (Complex.I * z * (x : ℂ))) /
      (Complex.I * z)
  let tail : ℝ → ℂ := fun x ↦
    Complex.exp (Complex.I * z * (x : ℂ)) *
      (Complex.exp (-Complex.I * z * (t : ℂ)) - 1) /
        (Complex.I * z)
  have hmiddle : Continuous middle := by
    dsimp [middle]
    fun_prop
  have htail : Continuous tail := by
    dsimp [tail]
    fun_prop
  have hjoin : middle t = tail t := by
    dsimp [middle, tail]
    have hcancel :
        Complex.exp (Complex.I * z * (t : ℂ)) *
            Complex.exp (-Complex.I * z * (t : ℂ)) = 1 := by
      rw [← Complex.exp_add]
      rw [show Complex.I * z * (t : ℂ) +
          -Complex.I * z * (t : ℂ) = 0 by ring,
        Complex.exp_zero]
    rw [mul_sub, hcancel, mul_one]
  have hinner : Continuous
      (fun x : ℝ ↦ if x ≤ t then middle x else tail x) := by
    apply Continuous.if
    · intro x hx
      change x ∈ frontier (Iic t) at hx
      have hxEq : x = t := by
        simpa only [frontier_Iic, mem_singleton_iff] using hx
      subst x
      exact hjoin
    · exact hmiddle
    · exact htail
  rw [show suzukiWeilTest t z =
      fun x : ℝ ↦ if x < 0 then 0
        else if x ≤ t then middle x else tail x by
    funext x
    rfl]
  apply Continuous.if
  · intro x hx
    change x ∈ frontier (Iio (0 : ℝ)) at hx
    have hxEq : x = 0 := by
      simpa only [frontier_Iio, mem_singleton_iff] using hx
    subst x
    simp [middle, ht]
  · exact continuous_const
  · exact hinner

/-- The symmetrized safe-line test is continuous. -/
theorem continuous_suzukiWeilSymmetricSafeLineTest
    {t : ℝ} (ht : 0 ≤ t) (z : ℂ) :
    Continuous (suzukiWeilSymmetricSafeLineTest t z) := by
  unfold suzukiWeilSymmetricSafeLineTest
  exact (by fun_prop : Continuous (fun x : ℝ ↦ (Real.exp (-x) : ℂ))).mul
    ((continuous_suzukiWeilTest ht z).add
      ((continuous_suzukiWeilTest ht z).comp continuous_neg))

/-- At frequency `-i`, the Fourier integrand is the test weighted by
`exp(-x)`. -/
theorem suzukiWeilFourierIntegrand_lowerSafeLine
    (t : ℝ) (z : ℂ) (x : ℝ) :
    suzukiWeilFourierIntegrand t z (-Complex.I) x =
      suzukiWeilTest t z x * (Real.exp (-x) : ℂ) := by
  unfold suzukiWeilFourierIntegrand
  congr 1
  rw [Complex.ofReal_exp]
  congr 1
  push_cast
  ring_nf
  rw [Complex.I_sq]
  ring

/-- At frequency `i`, the Fourier integrand is the test weighted by
`exp(x)`. -/
theorem suzukiWeilFourierIntegrand_upperSafeLine
    (t : ℝ) (z : ℂ) (x : ℝ) :
    suzukiWeilFourierIntegrand t z Complex.I x =
      suzukiWeilTest t z x * (Real.exp x : ℂ) := by
  unfold suzukiWeilFourierIntegrand
  congr 1
  rw [Complex.ofReal_exp]
  congr 1
  ring_nf
  rw [Complex.I_sq]
  ring

/-- The symmetrized time-domain test is absolutely integrable whenever the
evaluation point lies above the height-one contour. -/
theorem integrable_suzukiWeilSymmetricSafeLineTest
    {t : ℝ} (ht : 0 ≤ t) {z : ℂ} (hz : 1 < z.im) :
    Integrable (suzukiWeilSymmetricSafeLineTest t z) := by
  have hlowerGap : (-Complex.I).im < z.im := by
    simp
    linarith
  have hupperGap : Complex.I.im < z.im := by
    simpa using hz
  have hlower := integrable_suzukiWeilFourierIntegrand
    (z := z) ht hlowerGap
  have hupper := integrable_suzukiWeilFourierIntegrand
    (z := z) ht hupperGap
  have hlower' : Integrable (fun x : ℝ ↦
      (Real.exp (-x) : ℂ) * suzukiWeilTest t z x) := by
    refine hlower.congr (Filter.Eventually.of_forall fun x ↦ ?_)
    rw [suzukiWeilFourierIntegrand_lowerSafeLine]
    ring
  have hupperReflected : Integrable (fun x : ℝ ↦
      (Real.exp (-x) : ℂ) * suzukiWeilTest t z (-x)) := by
    have hreflected := hupper.comp_neg
    refine hreflected.congr (Filter.Eventually.of_forall fun x ↦ ?_)
    change suzukiWeilFourierIntegrand t z Complex.I (-x) = _
    rw [suzukiWeilFourierIntegrand_upperSafeLine]
    ring
  unfold suzukiWeilSymmetricSafeLineTest
  refine (hlower'.add hupperReflected).congr
    (Filter.Eventually.of_forall fun x ↦ ?_)
  change
    (Real.exp (-x) : ℂ) * suzukiWeilTest t z x +
        (Real.exp (-x) : ℂ) * suzukiWeilTest t z (-x) =
      (Real.exp (-x) : ℂ) *
        (suzukiWeilTest t z x + suzukiWeilTest t z (-x))
  ring

/-- On any nonzero horizontal frequency line distinct from the evaluation
height, Suzuki's spectral transform is absolutely integrable.  The proof
uses its two genuine linear denominators and dominates their reciprocal
product by a sum of shifted Cauchy kernels. -/
theorem integrable_suzukiWeilSpectralTransform_horizontal
    (t : ℝ) (z : ℂ) {c : ℝ} (hc : c ≠ 0)
    (hzc : z.im ≠ c) :
    Integrable (fun r : ℝ ↦
      suzukiWeilSpectralTransform t z
        ((r : ℂ) + (c : ℂ) * Complex.I)) := by
  let A : ℝ → ℝ := fun r ↦ (r ^ 2 + c ^ 2)⁻¹
  let B : ℝ → ℝ := fun r ↦ ((r - z.re) ^ 2 + (c - z.im) ^ 2)⁻¹
  let C : ℝ := Real.exp (c * t) + 1
  have hcAbs : 0 < |c| := abs_pos.mpr hc
  have hgap : c - z.im ≠ 0 := sub_ne_zero.mpr hzc.symm
  have hgapAbs : 0 < |c - z.im| := abs_pos.mpr hgap
  have hA : Integrable A := by
    simpa only [A, sq_abs] using integrable_inv_sq_add_sq hcAbs
  have hBbase : Integrable
      (fun x : ℝ ↦ (x ^ 2 + (c - z.im) ^ 2)⁻¹) := by
    simpa only [sq_abs] using integrable_inv_sq_add_sq hgapAbs
  have hB : Integrable B := by
    simpa only [B, neg_add_eq_sub] using hBbase.comp_add_left (-z.re)
  have hmajor : Integrable (fun r ↦ C * (A r + B r)) :=
    (hA.add hB).const_mul C
  have hcont : Continuous (fun r : ℝ ↦
      suzukiWeilSpectralTransform t z
        ((r : ℂ) + (c : ℂ) * Complex.I)) := by
    apply continuous_comp_of_forall_analyticAt
      (suzukiWeilSpectralTransform t z)
      (fun r : ℝ ↦ (r : ℂ) + (c : ℂ) * Complex.I) (by fun_prop)
    intro r
    apply analyticAt_suzukiWeilSpectralTransform_of_ne
    intro heq
    have him := congrArg Complex.im heq
    simp at him
    exact hzc him.symm
  apply hmajor.mono' hcont.aestronglyMeasurable
  filter_upwards with r
  let alpha : ℂ := (r : ℂ) + (c : ℂ) * Complex.I
  have halpha : alpha ≠ 0 := by
    intro ha
    have him := congrArg Complex.im ha
    simp [alpha] at him
    exact hc him
  have hza : z - alpha ≠ 0 := by
    intro hza
    have him := congrArg Complex.im hza
    simp [alpha] at him
    exact hzc (sub_eq_zero.mp him)
  have haPos : 0 < ‖alpha‖ := norm_pos_iff.mpr halpha
  have hzaPos : 0 < ‖z - alpha‖ := norm_pos_iff.mpr hza
  have hrecip :
      1 / (‖alpha‖ * ‖z - alpha‖) ≤
        (1 / 2 : ℝ) *
          (1 / ‖alpha‖ ^ 2 + 1 / ‖z - alpha‖ ^ 2) := by
    field_simp [haPos.ne', hzaPos.ne']
    nlinarith [sq_nonneg (‖alpha‖ - ‖z - alpha‖)]
  have hcoeff := norm_suzukiSpectralScrewCoefficient_le_div t halpha
  have hCnonneg : 0 ≤ C := by
    dsimp [C]
    positivity
  unfold suzukiWeilSpectralTransform
  rw [norm_div]
  calc
    ‖suzukiSpectralScrewCoefficient t alpha‖ / ‖z - alpha‖ ≤
        ((Real.exp (alpha.im * t) + 1) / ‖alpha‖) /
          ‖z - alpha‖ := by gcongr
    _ = C * (1 / (‖alpha‖ * ‖z - alpha‖)) := by
      have halphaIm : alpha.im = c := by simp [alpha]
      rw [halphaIm]
      dsimp [C]
      field_simp [haPos.ne', hzaPos.ne']
    _ ≤ C * ((1 / 2 : ℝ) *
          (1 / ‖alpha‖ ^ 2 + 1 / ‖z - alpha‖ ^ 2)) := by
      gcongr
    _ ≤ C * (A r + B r) := by
      have halphaSq : ‖alpha‖ ^ 2 = r ^ 2 + c ^ 2 := by
        rw [Complex.sq_norm]
        simp [alpha, Complex.normSq_apply]
        ring
      have hgapSq : ‖z - alpha‖ ^ 2 =
          (r - z.re) ^ 2 + (c - z.im) ^ 2 := by
        rw [Complex.sq_norm]
        simp [alpha, Complex.normSq_apply]
        ring
      rw [halphaSq, hgapSq]
      dsimp [A, B]
      have hnonnegA : 0 ≤ (r ^ 2 + c ^ 2)⁻¹ := by positivity
      have hnonnegB :
          0 ≤ ((r - z.re) ^ 2 + (c - z.im) ^ 2)⁻¹ := by positivity
      apply mul_le_mul_of_nonneg_left _ hCnonneg
      simp only [one_div]
      nlinarith

/-- The reflected height-one spectral weight is absolutely integrable. -/
theorem integrable_suzukiWeilSafeLineSpectralWeight
    (t : ℝ) {z : ℂ} (hz : 1 < z.im) :
    Integrable (suzukiWeilSafeLineSpectralWeight t z) := by
  have hlower :=
    integrable_suzukiWeilSpectralTransform_horizontal
      t z (c := -1) (by norm_num) (by simp; linarith)
  have hupper :=
    integrable_suzukiWeilSpectralTransform_horizontal
      t z (c := 1) (by norm_num) (by norm_num; linarith)
  unfold suzukiWeilSafeLineSpectralWeight
  refine (hlower.add hupper.comp_neg).congr
    (Filter.Eventually.of_forall fun r ↦ ?_)
  simp only [Pi.add_apply, Complex.ofReal_neg, Complex.ofReal_one,
    one_mul, neg_mul]
  rw [show (r : ℂ) + -Complex.I = (r : ℂ) - Complex.I by ring]

/-! ## Exact Fourier-transform representation -/

/-- The two reflected Fourier integrands combine pointwise into the
symmetrized safe-line test times the ordinary oscillation `exp(-i*r*x)`. -/
theorem suzukiWeilFourierIntegrand_safeLine_reflection
    (t : ℝ) (z : ℂ) (r x : ℝ) :
    suzukiWeilFourierIntegrand t z ((r : ℂ) - Complex.I) x +
        suzukiWeilFourierIntegrand t z
          (((-r : ℝ) : ℂ) + Complex.I) (-x) =
      suzukiWeilSymmetricSafeLineTest t z x *
        Complex.exp (-Complex.I * (r : ℂ) * (x : ℂ)) := by
  unfold suzukiWeilFourierIntegrand
    suzukiWeilSymmetricSafeLineTest
  have hlowerExp :
      Complex.exp
          (-Complex.I * ((r : ℂ) - Complex.I) * (x : ℂ)) =
        (Real.exp (-x) : ℂ) *
          Complex.exp (-Complex.I * (r : ℂ) * (x : ℂ)) := by
    rw [Complex.ofReal_exp, ← Complex.exp_add]
    congr 1
    push_cast
    ring_nf
    rw [Complex.I_sq]
    ring
  have hupperExp :
      Complex.exp
          (-Complex.I * (((-r : ℝ) : ℂ) + Complex.I) *
            ((-x : ℝ) : ℂ)) =
        (Real.exp (-x) : ℂ) *
          Complex.exp (-Complex.I * (r : ℂ) * (x : ℂ)) := by
    rw [Complex.ofReal_exp, ← Complex.exp_add]
    congr 1
    push_cast
    ring_nf
    rw [Complex.I_sq]
    ring
  rw [hlowerExp, hupperExp]
  ring

/-- The reflected spectral weight is exactly the unnormalized ordinary
Fourier transform of the symmetrized time-domain test. -/
theorem suzukiWeilSafeLineSpectralWeight_eq_integral
    {t : ℝ} (ht : 0 ≤ t) {z : ℂ} (hz : 1 < z.im) (r : ℝ) :
    suzukiWeilSafeLineSpectralWeight t z r =
      ∫ x : ℝ, suzukiWeilSymmetricSafeLineTest t z x *
        Complex.exp (-Complex.I * (r : ℂ) * (x : ℂ)) := by
  have hz0 : z ≠ 0 := by
    intro hzero
    subst z
    norm_num at hz
  have hlowerGap : (((r : ℂ) - Complex.I).im) < z.im := by
    simp
    linarith
  have hupperGap :
      (((( -r : ℝ) : ℂ) + Complex.I).im) < z.im := by
    simpa using hz
  have hlower := integral_suzukiWeilFourierIntegrand
    (z := z) ht hz0 hlowerGap
  have hupper := integral_suzukiWeilFourierIntegrand
    (z := z) ht hz0 hupperGap
  have hupperChange :
      (∫ x : ℝ, suzukiWeilFourierIntegrand t z
        (((-r : ℝ) : ℂ) + Complex.I) x) =
      ∫ x : ℝ, suzukiWeilFourierIntegrand t z
        (((-r : ℝ) : ℂ) + Complex.I) (-x) := by
    have hchange := Measure.integral_comp_mul_left
      (fun x : ℝ ↦ suzukiWeilFourierIntegrand t z
        (((-r : ℝ) : ℂ) + Complex.I) x) (-1)
    simpa using hchange.symm
  have hlowerIntegrable := integrable_suzukiWeilFourierIntegrand
    (z := z) ht hlowerGap
  have hupperIntegrable := integrable_suzukiWeilFourierIntegrand
    (z := z) ht hupperGap |>.comp_neg
  unfold suzukiWeilSafeLineSpectralWeight
    suzukiWeilSpectralTransform
  rw [← hlower, ← hupper, hupperChange,
    ← integral_add hlowerIntegrable hupperIntegrable]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun x ↦
    suzukiWeilFourierIntegrand_safeLine_reflection t z r x

/-- In Mathlib's `2π`-normalized convention, evaluating the Fourier transform
at `r/(2π)` gives exactly the reflected safe-line spectral weight. -/
theorem fourier_suzukiWeilSymmetricSafeLineTest
    {t : ℝ} (ht : 0 ≤ t) {z : ℂ} (hz : 1 < z.im) (r : ℝ) :
    𝓕 (suzukiWeilSymmetricSafeLineTest t z) (r / (2 * Real.pi)) =
      suzukiWeilSafeLineSpectralWeight t z r := by
  rw [Real.fourier_eq',
    suzukiWeilSafeLineSpectralWeight_eq_integral ht hz]
  apply integral_congr_ae
  filter_upwards with x
  simp only [RCLike.inner_apply, conj_trivial, ofReal_mul]
  rw [smul_eq_mul, mul_comm]
  congr 1
  congr 1
  push_cast
  field_simp [Real.pi_ne_zero]

/-- The Mathlib-normalized Fourier transform of the symmetrized test is
absolutely integrable, so the pointwise Fourier inversion theorem applies. -/
theorem integrable_fourier_suzukiWeilSymmetricSafeLineTest
    {t : ℝ} (ht : 0 ≤ t) {z : ℂ} (hz : 1 < z.im) :
    Integrable (𝓕 (suzukiWeilSymmetricSafeLineTest t z)) := by
  have hscale : Integrable (fun x : ℝ ↦
      suzukiWeilSafeLineSpectralWeight t z (2 * Real.pi * x)) :=
    (integrable_suzukiWeilSafeLineSpectralWeight t hz).comp_mul_left'
      (mul_ne_zero (by norm_num) Real.pi_ne_zero)
  refine hscale.congr (Filter.Eventually.of_forall fun x ↦ ?_)
  have hfourier := fourier_suzukiWeilSymmetricSafeLineTest
    ht hz (2 * Real.pi * x)
  convert hfourier.symm using 1
  field_simp [Real.pi_ne_zero]

/-- Unnormalized Fourier inversion for the exact reflected safe-line weight.
This is the form needed to evaluate the prime Dirichlet series term by term. -/
theorem integral_suzukiWeilSafeLineSpectralWeight_mul_cexp
    {t : ℝ} (ht : 0 ≤ t) {z : ℂ} (hz : 1 < z.im) (x : ℝ) :
    (∫ r : ℝ, suzukiWeilSafeLineSpectralWeight t z r *
        Complex.exp (Complex.I * (r : ℂ) * (x : ℂ))) =
      ((2 * Real.pi : ℝ) : ℂ) *
        suzukiWeilSymmetricSafeLineTest t z x := by
  have hinv :=
    (integrable_suzukiWeilSymmetricSafeLineTest ht hz).fourierInv_fourier_eq
      (v := x) (integrable_fourier_suzukiWeilSymmetricSafeLineTest ht hz)
      (continuous_suzukiWeilSymmetricSafeLineTest ht z).continuousAt
  rw [Real.fourierInv_eq'] at hinv
  have hinvScaled :
      (∫ u : ℝ,
        suzukiWeilSafeLineSpectralWeight t z (2 * Real.pi * u) *
          Complex.exp
            (Complex.I * ((2 * Real.pi * u : ℝ) : ℂ) * (x : ℂ))) =
        suzukiWeilSymmetricSafeLineTest t z x := by
    rw [← hinv]
    apply integral_congr_ae
    filter_upwards with u
    have hfourier := fourier_suzukiWeilSymmetricSafeLineTest
      ht hz (2 * Real.pi * u)
    have hfourier' :
        𝓕 (suzukiWeilSymmetricSafeLineTest t z) u =
          suzukiWeilSafeLineSpectralWeight t z (2 * Real.pi * u) := by
      convert hfourier using 1
      field_simp [Real.pi_ne_zero]
    rw [hfourier', smul_eq_mul, mul_comm]
    congr 1
    congr 1
    simp only [RCLike.inner_apply, conj_trivial, ofReal_mul]
    push_cast
    ring
  let G : ℝ → ℂ := fun r ↦
    suzukiWeilSafeLineSpectralWeight t z r *
      Complex.exp (Complex.I * (r : ℂ) * (x : ℂ))
  have hscale := Measure.integral_comp_mul_left G (2 * Real.pi)
  have hscaleEq :
      (∫ u : ℝ, G (2 * Real.pi * u)) =
        (((2 * Real.pi)⁻¹ : ℝ) : ℂ) * (∫ r : ℝ, G r) := by
    calc
      (∫ u : ℝ, G (2 * Real.pi * u)) =
          |(2 * Real.pi)⁻¹| • (∫ r : ℝ, G r) := hscale
      _ = (((2 * Real.pi)⁻¹ : ℝ) : ℂ) * (∫ r : ℝ, G r) := by
        rw [abs_of_pos (inv_pos.mpr (mul_pos (by norm_num) Real.pi_pos))]
        rfl
  have hinvG : (∫ u : ℝ, G (2 * Real.pi * u)) =
      suzukiWeilSymmetricSafeLineTest t z x := by
    simpa [G] using hinvScaled
  change (∫ r : ℝ, G r) = _
  calc
    (∫ r : ℝ, G r) =
        ((2 * Real.pi : ℝ) : ℂ) *
          ((((2 * Real.pi)⁻¹ : ℝ) : ℂ) * (∫ r : ℝ, G r)) := by
      push_cast
      field_simp [Real.pi_ne_zero]
    _ = ((2 * Real.pi : ℝ) : ℂ) *
        (∫ u : ℝ, G (2 * Real.pi * u)) := by rw [hscaleEq]
    _ = ((2 * Real.pi : ℝ) : ℂ) *
        suzukiWeilSymmetricSafeLineTest t z x := by rw [hinvG]

end

end RiemannGaussian
