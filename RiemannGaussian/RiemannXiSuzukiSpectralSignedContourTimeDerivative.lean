import Mathlib.Analysis.Calculus.ParametricIntervalIntegral
import RiemannGaussian.RiemannXiSuzukiSpectralSignedContourProjection

/-!
# Direct time differentiation of the signed Suzuki contour

The signed contour projection already identifies the finite Blaschke detector
with the time derivative of a contour response.  This file proves the stronger
analytic statement needed for boundary estimates: time differentiation may be
passed through each of the four finite side integrals.  The proof uses an
explicit local exponential majorant for Suzuki's screw coefficient, so no
interchange of derivative and integral is assumed.
-/

open Complex Filter MeasureTheory Metric Set Topology
open scoped Classical ComplexConjugate ENNReal Interval Topology

namespace RiemannGaussian

noncomputable section

/-! ## The literal differentiated spectral integrand -/

/-- The time derivative of Suzuki's spectral transform. -/
def suzukiWeilSpectralTransformTimeDerivative
    (t : ℝ) (z gamma : ℂ) : ℂ :=
  suzukiSpectralScrewCoefficientDerivative t gamma / (z - gamma)

/-- The literal time derivative of the Suzuki-weighted spectral-xi
logarithmic-derivative integrand. -/
def suzukiXiWeilSpectralIntegrandTimeDerivative
    (t : ℝ) (z w : ℂ) : ℂ :=
  suzukiWeilSpectralTransformTimeDerivative t z w *
    xiSpectralNegativeLogDerivative w

/-- Pointwise, the proposed integrand is the exact real-time derivative of
the original Suzuki-weighted spectral-xi integrand. -/
theorem hasDerivAt_suzukiXiWeilSpectralIntegrand_time
    (t : ℝ) (z w : ℂ) :
    HasDerivAt (fun u : ℝ ↦ suzukiXiWeilSpectralIntegrand u z w)
      (suzukiXiWeilSpectralIntegrandTimeDerivative t z w) t := by
  unfold suzukiXiWeilSpectralIntegrand
    suzukiWeilSpectralTransform
    suzukiXiWeilSpectralIntegrandTimeDerivative
    suzukiWeilSpectralTransformTimeDerivative
  exact ((hasDerivAt_suzukiSpectralScrewCoefficient t w).div_const
    (z - w)).mul_const (xiSpectralNegativeLogDerivative w)

/-- As a function of spectral frequency, the differentiated Suzuki transform
is analytic away from its evaluation pole. -/
theorem analyticAt_suzukiWeilSpectralTransformTimeDerivative_of_ne
    (t : ℝ) (z : ℂ) {w : ℂ} (hw : w ≠ z) :
    AnalyticAt ℂ (suzukiWeilSpectralTransformTimeDerivative t z) w := by
  unfold suzukiWeilSpectralTransformTimeDerivative
    suzukiSpectralScrewCoefficientDerivative
    spectralScrewExponential
  have hnumerator : AnalyticAt ℂ
      (fun gamma : ℂ ↦
        -Complex.I * Complex.exp (-Complex.I * gamma * (t : ℂ))) w := by
    fun_prop
  exact hnumerator.div (analyticAt_const.sub analyticAt_id)
    (sub_ne_zero.mpr hw.symm)

/-- Away from the evaluation pole and the genuine xi divisor, the literal
time-derivative integrand is analytic in the spectral variable. -/
theorem analyticAt_suzukiXiWeilSpectralIntegrandTimeDerivative_of_ne
    (t : ℝ) (z : ℂ) {w : ℂ}
    (hwz : w ≠ z) (hxi : riemannXiSpectral w ≠ 0) :
    AnalyticAt ℂ (suzukiXiWeilSpectralIntegrandTimeDerivative t z) w := by
  unfold suzukiXiWeilSpectralIntegrandTimeDerivative
  exact (analyticAt_suzukiWeilSpectralTransformTimeDerivative_of_ne
    t z hwz).mul
      (analyticAt_xiSpectralNegativeLogDerivative_of_ne hxi)

/-- A continuous path through points avoiding both singular sets gives an
interval-integrable differentiated integrand. -/
theorem intervalIntegrable_suzukiXiWeilSpectralIntegrandTimeDerivative_comp
    (t a b : ℝ) (z : ℂ) (gamma : ℝ → ℂ)
    (hgamma : Continuous gamma)
    (havoid : ∀ x ∈ uIcc a b,
      gamma x ≠ z ∧ riemannXiSpectral (gamma x) ≠ 0) :
    IntervalIntegrable
      (fun x : ℝ ↦
        suzukiXiWeilSpectralIntegrandTimeDerivative t z (gamma x))
      volume a b := by
  apply ContinuousOn.intervalIntegrable
  intro x hx
  apply ContinuousAt.continuousWithinAt
  have hanalytic :=
    analyticAt_suzukiXiWeilSpectralIntegrandTimeDerivative_of_ne
      t z (havoid x hx).1 (havoid x hx).2
  have hcomp : ContinuousAt
      (suzukiXiWeilSpectralIntegrandTimeDerivative t z ∘ gamma) x :=
    ContinuousAt.comp_of_eq hanalytic.continuousAt
      hgamma.continuousAt rfl
  exact hcomp.congr (Eventually.of_forall fun _ ↦ rfl)

/-- On the unit spectral strip and in a unit time neighborhood of `t`, the
literal derivative integrand is dominated by its time-zero norm times one
explicit constant. -/
theorem norm_suzukiXiWeilSpectralIntegrandTimeDerivative_le_local
    (t u : ℝ) (z w : ℂ)
    (hu : u ∈ Icc (t - 1) (t + 1)) (hw : |w.im| ≤ 1) :
    ‖suzukiXiWeilSpectralIntegrandTimeDerivative u z w‖ ≤
      Real.exp (|t| + 1) *
        ‖suzukiXiWeilSpectralIntegrandTimeDerivative 0 z w‖ := by
  rcases hu with ⟨huLower, huUpper⟩
  have huabs : |u| ≤ |t| + 1 := by
    rw [abs_le]
    constructor
    · linarith [neg_abs_le t]
    · linarith [le_abs_self t]
  have hproduct : w.im * u ≤ |t| + 1 := calc
    w.im * u ≤ |w.im * u| := le_abs_self _
    _ = |w.im| * |u| := abs_mul _ _
    _ ≤ 1 * (|t| + 1) := by
      exact mul_le_mul hw huabs (abs_nonneg u) (by norm_num)
    _ = |t| + 1 := one_mul _
  unfold suzukiXiWeilSpectralIntegrandTimeDerivative
    suzukiWeilSpectralTransformTimeDerivative
  rw [norm_mul, norm_div,
    norm_suzukiSpectralScrewCoefficientDerivative,
    norm_mul, norm_div,
    norm_suzukiSpectralScrewCoefficientDerivative]
  simp only [mul_zero, Real.exp_zero]
  have hexp : Real.exp (w.im * u) ≤ Real.exp (|t| + 1) :=
    Real.exp_le_exp.mpr hproduct
  simpa only [div_eq_mul_inv, one_mul, mul_assoc] using
    mul_le_mul_of_nonneg_right hexp
      (mul_nonneg (inv_nonneg.mpr (norm_nonneg (z - w)))
        (norm_nonneg (xiSpectralNegativeLogDerivative w)))

/-! ## A dominated interval-side differentiation lemma -/

/-- A reusable side lemma.  Interval integrability is supplied separately;
the only analytic estimate needed for differentiation is that the path stays
in the closed unit spectral strip. -/
theorem hasDerivAt_intervalIntegral_suzukiXiWeilSpectralIntegrand_time
    (t a b : ℝ) (z : ℂ) (gamma : ℝ → ℂ)
    (hintegrable : ∀ u : ℝ, IntervalIntegrable
      (fun x : ℝ ↦ suzukiXiWeilSpectralIntegrand u z (gamma x))
      volume a b)
    (hderivIntegrable : ∀ u : ℝ, IntervalIntegrable
      (fun x : ℝ ↦
        suzukiXiWeilSpectralIntegrandTimeDerivative u z (gamma x))
      volume a b)
    (hstrip : ∀ x ∈ uIcc a b, |(gamma x).im| ≤ 1) :
    HasDerivAt
      (fun u : ℝ ↦ ∫ x : ℝ in a..b,
        suzukiXiWeilSpectralIntegrand u z (gamma x))
      (∫ x : ℝ in a..b,
        suzukiXiWeilSpectralIntegrandTimeDerivative t z (gamma x)) t := by
  let s : Set ℝ := Icc (t - 1) (t + 1)
  let bound : ℝ → ℝ := fun x ↦
    Real.exp (|t| + 1) *
      ‖suzukiXiWeilSpectralIntegrandTimeDerivative 0 z (gamma x)‖
  have hs : s ∈ 𝓝 t := by
    exact Icc_mem_nhds (by linarith) (by linarith)
  have hFmeas : ∀ᶠ u in 𝓝 t,
      AEStronglyMeasurable
        (fun x : ℝ ↦ suzukiXiWeilSpectralIntegrand u z (gamma x))
        (volume.restrict (Ι a b)) := by
    filter_upwards with u
    exact (intervalIntegrable_iff.mp (hintegrable u)).aestronglyMeasurable
  have hDmeas : AEStronglyMeasurable
      (fun x : ℝ ↦
        suzukiXiWeilSpectralIntegrandTimeDerivative t z (gamma x))
      (volume.restrict (Ι a b)) := by
    exact (intervalIntegrable_iff.mp
      (hderivIntegrable t)).aestronglyMeasurable
  have hbound : ∀ᵐ x : ℝ ∂volume, x ∈ Ι a b →
      ∀ u ∈ s,
        ‖suzukiXiWeilSpectralIntegrandTimeDerivative u z (gamma x)‖ ≤
          bound x := by
    exact Eventually.of_forall fun x hx u hu ↦
      norm_suzukiXiWeilSpectralIntegrandTimeDerivative_le_local
        t u z (gamma x) hu (hstrip x (uIoc_subset_uIcc hx))
  have hboundInt : IntervalIntegrable bound volume a b := by
    exact (hderivIntegrable 0).norm.const_mul (Real.exp (|t| + 1))
  have hdiff : ∀ᵐ x : ℝ ∂volume, x ∈ Ι a b →
      ∀ u ∈ s,
        HasDerivAt
          (fun v : ℝ ↦ suzukiXiWeilSpectralIntegrand v z (gamma x))
          (suzukiXiWeilSpectralIntegrandTimeDerivative u z (gamma x)) u := by
    exact Eventually.of_forall fun x _hx u _hu ↦
      hasDerivAt_suzukiXiWeilSpectralIntegrand_time u z (gamma x)
  exact (intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le
    hs hFmeas (hintegrable t) hDmeas hbound hboundInt hdiff).2

/-! ## Integrability of the differentiated rectangle boundaries -/

/-- The literal time-derivative integrand is integrable on all four sides of
the upper zero-selecting rectangle. -/
theorem rectangularBoundaryIntegrable_suzukiXiWeilSpectralIntegrandTimeDerivative_upper
    (t : ℝ) {z : ℂ} (hz : 1 < z.im)
    {T eta : ℝ} (hT : 0 ≤ T)
    (hboundary : ∀ rho : NontrivialZetaZero,
      |(zetaSpectralCoordinate rho.1).re| ≠ T)
    (heta : SuzukiXiUpperContourBottomAdmissible T eta) :
    rectangularBoundaryIntegrable (-T) T eta 1
      (suzukiXiWeilSpectralIntegrandTimeDerivative t z) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · apply intervalIntegrable_suzukiXiWeilSpectralIntegrandTimeDerivative_comp
      t (-T) T z
      (fun x : ℝ ↦ (x : ℂ) + (eta : ℂ) * Complex.I) (by fun_prop)
    intro x hx
    rw [uIcc_of_le (by linarith)] at hx
    constructor
    · intro heq
      have him := congrArg Complex.im heq
      simp at him
      linarith [heta.2.1]
    · intro hzero
      apply suzukiXiUpperContourBottom_not_mem_spectralXiZeroWindow heta x
      apply (mem_spectralXiZeroWindow_iff hT _).mpr
      exact ⟨hzero, by simpa using (abs_le).2 hx⟩
  · apply intervalIntegrable_suzukiXiWeilSpectralIntegrandTimeDerivative_comp
      t (-T) T z
      (fun x : ℝ ↦ (x : ℂ) + (((1 : ℝ) : ℂ)) * Complex.I) (by fun_prop)
    intro x _hx
    constructor
    · intro heq
      have him := congrArg Complex.im heq
      simp at him
      linarith
    · apply riemannXiSpectral_ne_zero_of_half_le_abs_im
      norm_num
  · apply intervalIntegrable_suzukiXiWeilSpectralIntegrandTimeDerivative_comp
      t eta 1 z
      (fun y : ℝ ↦ (T : ℂ) + (y : ℂ) * Complex.I) (by fun_prop)
    intro y hy
    rw [uIcc_of_le heta.2.1.le] at hy
    constructor
    · intro heq
      have him := congrArg Complex.im heq
      simp at him
      linarith [hy.2]
    · apply riemannXiSpectral_ne_zero_of_abs_re_ne hboundary
      simp [abs_of_nonneg hT]
  · apply intervalIntegrable_suzukiXiWeilSpectralIntegrandTimeDerivative_comp
      t eta 1 z
      (fun y : ℝ ↦ (((-T : ℝ) : ℂ)) + (y : ℂ) * Complex.I) (by fun_prop)
    intro y hy
    rw [uIcc_of_le heta.2.1.le] at hy
    constructor
    · intro heq
      have him := congrArg Complex.im heq
      simp at him
      linarith [hy.2]
    · apply riemannXiSpectral_ne_zero_of_abs_re_ne hboundary
      simp [abs_of_nonneg hT]

/-- The literal time-derivative integrand is integrable on all four sides of
the reflected lower zero-selecting rectangle. -/
theorem rectangularBoundaryIntegrable_suzukiXiWeilSpectralIntegrandTimeDerivative_lower
    (t : ℝ) {z : ℂ} (hz : 1 < z.im)
    {T eta : ℝ} (hT : 0 ≤ T)
    (hboundary : ∀ rho : NontrivialZetaZero,
      |(zetaSpectralCoordinate rho.1).re| ≠ T)
    (heta : SuzukiXiUpperContourBottomAdmissible T eta) :
    rectangularBoundaryIntegrable (-T) T (-1) (-eta)
      (suzukiXiWeilSpectralIntegrandTimeDerivative t z) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · apply intervalIntegrable_suzukiXiWeilSpectralIntegrandTimeDerivative_comp
      t (-T) T z
      (fun x : ℝ ↦
        (x : ℂ) + (((-1 : ℝ) : ℂ)) * Complex.I) (by fun_prop)
    intro x _hx
    constructor
    · intro heq
      have him := congrArg Complex.im heq
      simp at him
      linarith
    · apply riemannXiSpectral_ne_zero_of_half_le_abs_im
      norm_num
  · apply intervalIntegrable_suzukiXiWeilSpectralIntegrandTimeDerivative_comp
      t (-T) T z
      (fun x : ℝ ↦
        (x : ℂ) + ((-eta : ℝ) : ℂ) * Complex.I) (by fun_prop)
    intro x hx
    rw [uIcc_of_le (by linarith)] at hx
    constructor
    · intro heq
      have him := congrArg Complex.im heq
      simp at him
      linarith [heta.1]
    · intro hzero
      apply suzukiXiLowerContourTop_not_mem_spectralXiZeroWindow
        hT heta x
      apply (mem_spectralXiZeroWindow_iff hT _).mpr
      exact ⟨hzero, by simpa using (abs_le).2 hx⟩
  · apply intervalIntegrable_suzukiXiWeilSpectralIntegrandTimeDerivative_comp
      t (-1) (-eta) z
      (fun y : ℝ ↦ (T : ℂ) + (y : ℂ) * Complex.I) (by fun_prop)
    intro y hy
    rw [uIcc_of_le (by linarith [heta.2.1])] at hy
    constructor
    · intro heq
      have him := congrArg Complex.im heq
      simp at him
      linarith [hy.2, heta.1]
    · apply riemannXiSpectral_ne_zero_of_abs_re_ne hboundary
      simp [abs_of_nonneg hT]
  · apply intervalIntegrable_suzukiXiWeilSpectralIntegrandTimeDerivative_comp
      t (-1) (-eta) z
      (fun y : ℝ ↦ (((-T : ℝ) : ℂ)) + (y : ℂ) * Complex.I) (by fun_prop)
    intro y hy
    rw [uIcc_of_le (by linarith [heta.2.1])] at hy
    constructor
    · intro heq
      have him := congrArg Complex.im heq
      simp at him
      linarith [hy.2, heta.1]
    · apply riemannXiSpectral_ne_zero_of_abs_re_ne hboundary
      simp [abs_of_nonneg hT]

/-! ## Differentiation through the four side integrals -/

/-- Time differentiation passes through the complete upper rectangular
boundary integral. -/
theorem hasDerivAt_rectangularBoundaryIntegral_suzukiXiWeilSpectralIntegrand_upper_time
    (t : ℝ) {z : ℂ} (hz : 1 < z.im)
    {T eta : ℝ} (hT : 0 ≤ T)
    (hboundary : ∀ rho : NontrivialZetaZero,
      |(zetaSpectralCoordinate rho.1).re| ≠ T)
    (heta : SuzukiXiUpperContourBottomAdmissible T eta) :
    HasDerivAt
      (fun u : ℝ ↦ rectangularBoundaryIntegral (-T) T eta 1
        (suzukiXiWeilSpectralIntegrand u z))
      (rectangularBoundaryIntegral (-T) T eta 1
        (suzukiXiWeilSpectralIntegrandTimeDerivative t z)) t := by
  have hbase (u : ℝ) :=
    rectangularBoundaryIntegrable_suzukiXiWeilSpectralIntegrand_upper
      u hz hT hboundary heta
  have hderiv (u : ℝ) :=
    rectangularBoundaryIntegrable_suzukiXiWeilSpectralIntegrandTimeDerivative_upper
      u hz hT hboundary heta
  have hbottom :=
    hasDerivAt_intervalIntegral_suzukiXiWeilSpectralIntegrand_time
      t (-T) T z
      (fun x : ℝ ↦ (x : ℂ) + (eta : ℂ) * Complex.I)
      (fun u ↦ (hbase u).1) (fun u ↦ (hderiv u).1) (by
        intro x _hx
        simpa [abs_of_pos heta.1] using heta.2.1.le)
  have htop :=
    hasDerivAt_intervalIntegral_suzukiXiWeilSpectralIntegrand_time
      t (-T) T z
      (fun x : ℝ ↦ (x : ℂ) + (((1 : ℝ) : ℂ)) * Complex.I)
      (fun u ↦ (hbase u).2.1) (fun u ↦ (hderiv u).2.1) (by
        intro x _hx
        norm_num)
  have hright :=
    hasDerivAt_intervalIntegral_suzukiXiWeilSpectralIntegrand_time
      t eta 1 z
      (fun y : ℝ ↦ (T : ℂ) + (y : ℂ) * Complex.I)
      (fun u ↦ (hbase u).2.2.1) (fun u ↦ (hderiv u).2.2.1) (by
        intro y hy
        rw [uIcc_of_le heta.2.1.le] at hy
        have hyNonneg : 0 ≤ y := heta.1.le.trans hy.1
        simpa [abs_of_nonneg hyNonneg] using hy.2)
  have hleft :=
    hasDerivAt_intervalIntegral_suzukiXiWeilSpectralIntegrand_time
      t eta 1 z
      (fun y : ℝ ↦ (((-T : ℝ) : ℂ)) + (y : ℂ) * Complex.I)
      (fun u ↦ (hbase u).2.2.2) (fun u ↦ (hderiv u).2.2.2) (by
        intro y hy
        rw [uIcc_of_le heta.2.1.le] at hy
        have hyNonneg : 0 ≤ y := heta.1.le.trans hy.1
        simpa [abs_of_nonneg hyNonneg] using hy.2)
  have hcombined :=
    ((hbottom.sub htop).add (hright.const_mul Complex.I)).sub
      (hleft.const_mul Complex.I)
  apply hcombined.congr_of_eventuallyEq
  exact Eventually.of_forall fun u ↦ by
    simp [rectangularBoundaryIntegral]

/-- Time differentiation passes through the complete reflected lower
rectangular boundary integral. -/
theorem hasDerivAt_rectangularBoundaryIntegral_suzukiXiWeilSpectralIntegrand_lower_time
    (t : ℝ) {z : ℂ} (hz : 1 < z.im)
    {T eta : ℝ} (hT : 0 ≤ T)
    (hboundary : ∀ rho : NontrivialZetaZero,
      |(zetaSpectralCoordinate rho.1).re| ≠ T)
    (heta : SuzukiXiUpperContourBottomAdmissible T eta) :
    HasDerivAt
      (fun u : ℝ ↦ rectangularBoundaryIntegral (-T) T (-1) (-eta)
        (suzukiXiWeilSpectralIntegrand u z))
      (rectangularBoundaryIntegral (-T) T (-1) (-eta)
        (suzukiXiWeilSpectralIntegrandTimeDerivative t z)) t := by
  have hbase (u : ℝ) :=
    rectangularBoundaryIntegrable_suzukiXiWeilSpectralIntegrand_lower
      u hz hT hboundary heta
  have hderiv (u : ℝ) :=
    rectangularBoundaryIntegrable_suzukiXiWeilSpectralIntegrandTimeDerivative_lower
      u hz hT hboundary heta
  have hbottom :=
    hasDerivAt_intervalIntegral_suzukiXiWeilSpectralIntegrand_time
      t (-T) T z
      (fun x : ℝ ↦
        (x : ℂ) + (((-1 : ℝ) : ℂ)) * Complex.I)
      (fun u ↦ (hbase u).1) (fun u ↦ (hderiv u).1) (by
        intro x _hx
        norm_num)
  have htop :=
    hasDerivAt_intervalIntegral_suzukiXiWeilSpectralIntegrand_time
      t (-T) T z
      (fun x : ℝ ↦
        (x : ℂ) + ((-eta : ℝ) : ℂ) * Complex.I)
      (fun u ↦ (hbase u).2.1) (fun u ↦ (hderiv u).2.1) (by
        intro x _hx
        simpa [abs_of_pos heta.1] using heta.2.1.le)
  have hright :=
    hasDerivAt_intervalIntegral_suzukiXiWeilSpectralIntegrand_time
      t (-1) (-eta) z
      (fun y : ℝ ↦ (T : ℂ) + (y : ℂ) * Complex.I)
      (fun u ↦ (hbase u).2.2.1) (fun u ↦ (hderiv u).2.2.1) (by
        intro y hy
        rw [uIcc_of_le (by linarith [heta.2.1])] at hy
        have hyNonpos : y ≤ 0 := by linarith [hy.2, heta.1]
        have hneg : -y ≤ 1 := by linarith [hy.1]
        simpa [abs_of_nonpos hyNonpos] using hneg)
  have hleft :=
    hasDerivAt_intervalIntegral_suzukiXiWeilSpectralIntegrand_time
      t (-1) (-eta) z
      (fun y : ℝ ↦ (((-T : ℝ) : ℂ)) + (y : ℂ) * Complex.I)
      (fun u ↦ (hbase u).2.2.2) (fun u ↦ (hderiv u).2.2.2) (by
        intro y hy
        rw [uIcc_of_le (by linarith [heta.2.1])] at hy
        have hyNonpos : y ≤ 0 := by linarith [hy.2, heta.1]
        have hneg : -y ≤ 1 := by linarith [hy.1]
        simpa [abs_of_nonpos hyNonpos] using hneg)
  have hcombined :=
    ((hbottom.sub htop).add (hright.const_mul Complex.I)).sub
      (hleft.const_mul Complex.I)
  apply hcombined.congr_of_eventuallyEq
  exact Eventually.of_forall fun u ↦ by
    simp [rectangularBoundaryIntegral]

/-! ## The directly differentiated signed contour -/

/-- Upper differentiated rectangle minus lower differentiated rectangle.
This is a boundary integral of the literal time derivative of the actual
Suzuki-weighted spectral-xi logarithmic derivative. -/
def suzukiXiWeilSignedContourTimeDerivativeWindow
    (t T eta : ℝ) (z : ℂ) : ℂ :=
  rectangularBoundaryIntegral (-T) T eta 1
      (suzukiXiWeilSpectralIntegrandTimeDerivative t z) -
    rectangularBoundaryIntegral (-T) T (-1) (-eta)
      (suzukiXiWeilSpectralIntegrandTimeDerivative t z)

/-- The signed contour response differentiates directly to the signed
boundary integral of its literal pointwise time derivative. -/
theorem hasDerivAt_suzukiXiWeilSignedContourResponseWindow_direct
    (t : ℝ) {z : ℂ} (hz : 1 < z.im)
    {T eta : ℝ} (hT : 0 ≤ T)
    (hboundary : ∀ rho : NontrivialZetaZero,
      |(zetaSpectralCoordinate rho.1).re| ≠ T)
    (heta : SuzukiXiUpperContourBottomAdmissible T eta) :
    HasDerivAt
      (fun u : ℝ ↦ suzukiXiWeilSignedContourResponseWindow u T eta z)
      (suzukiXiWeilSignedContourTimeDerivativeWindow t T eta z) t := by
  have hupper :=
    hasDerivAt_rectangularBoundaryIntegral_suzukiXiWeilSpectralIntegrand_upper_time
      t hz hT hboundary heta
  have hlower :=
    hasDerivAt_rectangularBoundaryIntegral_suzukiXiWeilSpectralIntegrand_lower_time
      t hz hT hboundary heta
  have hcombined := hupper.sub hlower
  apply hcombined.congr_of_eventuallyEq
  exact Eventually.of_forall fun u ↦ by
    simp [suzukiXiWeilSignedContourResponseWindow]

/-- The actual derivative of the signed contour response is its literal
differentiated boundary integral. -/
theorem deriv_suzukiXiWeilSignedContourResponseWindow_eq_direct
    (t : ℝ) {z : ℂ} (hz : 1 < z.im)
    {T eta : ℝ} (hT : 0 ≤ T)
    (hboundary : ∀ rho : NontrivialZetaZero,
      |(zetaSpectralCoordinate rho.1).re| ≠ T)
    (heta : SuzukiXiUpperContourBottomAdmissible T eta) :
    deriv (fun u : ℝ ↦
      suzukiXiWeilSignedContourResponseWindow u T eta z) t =
      suzukiXiWeilSignedContourTimeDerivativeWindow t T eta z :=
  (hasDerivAt_suzukiXiWeilSignedContourResponseWindow_direct
    t hz hT hboundary heta).deriv

/-- At every screw time, the direct differentiated xi-contour equals the
finite signed spectral response derivative with the exact contour factor. -/
theorem suzukiXiWeilSignedContourTimeDerivativeWindow_eq_spectralResponseDerivative
    (t : ℝ) {z : ℂ} (hz : 1 < z.im)
    {T eta : ℝ} (hT : 0 ≤ T)
    (hboundary : ∀ rho : NontrivialZetaZero,
      |(zetaSpectralCoordinate rho.1).re| ≠ T)
    (heta : SuzukiXiUpperContourBottomAdmissible T eta) :
    suzukiXiWeilSignedContourTimeDerivativeWindow t T eta z =
      -(((2 * Real.pi : ℝ) : ℂ)) *
        suzukiXiOffAxisSignedSpectralPResponseDerivativeWindow t T z :=
  (hasDerivAt_suzukiXiWeilSignedContourResponseWindow_direct
    t hz hT hboundary heta).unique
      (hasDerivAt_suzukiXiWeilSignedContourResponseWindow_time
        t hz hT hboundary heta)

/-- At time zero, the literal differentiated boundary integral of the actual
transformed xi logarithmic derivative is exactly the finite Blaschke
logarithmic derivative, including the full contour normalization. -/
theorem suzukiXiWeilSignedContourTimeDerivativeWindow_zero_eq_blaschke
    {z : ℂ} (hz : 1 < z.im)
    {T eta : ℝ} (hT : 0 ≤ T)
    (hboundary : ∀ rho : NontrivialZetaZero,
      |(zetaSpectralCoordinate rho.1).re| ≠ T)
    (heta : SuzukiXiUpperContourBottomAdmissible T eta) :
    suzukiXiWeilSignedContourTimeDerivativeWindow 0 T eta z =
      -(((2 * Real.pi : ℝ) : ℂ)) *
        (-Complex.I * riemannXiUpperBlaschkeLogDerivativeWindow z T) :=
  (hasDerivAt_suzukiXiWeilSignedContourResponseWindow_direct
    0 hz hT hboundary heta).unique
      (hasDerivAt_suzukiXiWeilSignedContourResponseWindow_zero_time
        hz hT hboundary heta)

/-! ## A static xi-logarithmic-derivative boundary formula -/

/-- The Cauchy kernel formed directly from the genuine spectral-xi negative
logarithmic derivative. -/
def xiSpectralBlaschkeContourKernel (z w : ℂ) : ℂ :=
  xiSpectralNegativeLogDerivative w / (z - w)

/-- At time zero, the literal differentiated Suzuki integrand is `-i` times
the static xi logarithmic-derivative Cauchy kernel. -/
theorem suzukiXiWeilSpectralIntegrandTimeDerivative_zero
    (z w : ℂ) :
    suzukiXiWeilSpectralIntegrandTimeDerivative 0 z w =
      -Complex.I * xiSpectralBlaschkeContourKernel z w := by
  unfold suzukiXiWeilSpectralIntegrandTimeDerivative
    suzukiWeilSpectralTransformTimeDerivative
    suzukiSpectralScrewCoefficientDerivative
    spectralScrewExponential
    xiSpectralBlaschkeContourKernel
  simp
  ring

/-- Constant factors pass through an arbitrary rectangular boundary
integral. -/
theorem rectangularBoundaryIntegral_const_mul
    (c : ℂ) (l r b u : ℝ) (f : ℂ → ℂ) :
    rectangularBoundaryIntegral l r b u (fun w ↦ c * f w) =
      c * rectangularBoundaryIntegral l r b u f := by
  unfold rectangularBoundaryIntegral
  rw [intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const_mul]
  ring

/-- Signed upper-minus-lower boundary integral of the genuine static
spectral-xi logarithmic-derivative Cauchy kernel. -/
def xiSpectralBlaschkeSignedContourWindow
    (T eta : ℝ) (z : ℂ) : ℂ :=
  rectangularBoundaryIntegral (-T) T eta 1
      (xiSpectralBlaschkeContourKernel z) -
    rectangularBoundaryIntegral (-T) T (-1) (-eta)
      (xiSpectralBlaschkeContourKernel z)

/-- The time-zero differentiated signed Suzuki contour is exactly `-i`
times the static xi-logarithmic-derivative contour. -/
theorem suzukiXiWeilSignedContourTimeDerivativeWindow_zero_eq_staticContour
    (T eta : ℝ) (z : ℂ) :
    suzukiXiWeilSignedContourTimeDerivativeWindow 0 T eta z =
      -Complex.I * xiSpectralBlaschkeSignedContourWindow T eta z := by
  unfold suzukiXiWeilSignedContourTimeDerivativeWindow
    xiSpectralBlaschkeSignedContourWindow
  rw [show suzukiXiWeilSpectralIntegrandTimeDerivative 0 z =
      fun w ↦ -Complex.I * xiSpectralBlaschkeContourKernel z w by
        funext w
        exact suzukiXiWeilSpectralIntegrandTimeDerivative_zero z w,
    rectangularBoundaryIntegral_const_mul,
    rectangularBoundaryIntegral_const_mul]
  ring

/-- The finite Blaschke logarithmic derivative is recovered directly from
the signed boundary integral of the genuine spectral `-xi'/xi` Cauchy
kernel.  No time derivative remains in this final static identity. -/
theorem xiSpectralBlaschkeSignedContourWindow_eq_blaschke
    {z : ℂ} (hz : 1 < z.im)
    {T eta : ℝ} (hT : 0 ≤ T)
    (hboundary : ∀ rho : NontrivialZetaZero,
      |(zetaSpectralCoordinate rho.1).re| ≠ T)
    (heta : SuzukiXiUpperContourBottomAdmissible T eta) :
    xiSpectralBlaschkeSignedContourWindow T eta z =
      -(((2 * Real.pi : ℝ) : ℂ)) *
        riemannXiUpperBlaschkeLogDerivativeWindow z T := by
  have htime :=
    suzukiXiWeilSignedContourTimeDerivativeWindow_zero_eq_blaschke
      hz hT hboundary heta
  rw [suzukiXiWeilSignedContourTimeDerivativeWindow_zero_eq_staticContour]
    at htime
  have hfactored :
      -Complex.I * xiSpectralBlaschkeSignedContourWindow T eta z =
        -Complex.I *
          (-(((2 * Real.pi : ℝ) : ℂ)) *
            riemannXiUpperBlaschkeLogDerivativeWindow z T) := by
    calc
      -Complex.I * xiSpectralBlaschkeSignedContourWindow T eta z =
          -(((2 * Real.pi : ℝ) : ℂ)) *
            (-Complex.I * riemannXiUpperBlaschkeLogDerivativeWindow z T) :=
        htime
      _ = -Complex.I *
          (-(((2 * Real.pi : ℝ) : ℂ)) *
            riemannXiUpperBlaschkeLogDerivativeWindow z T) := by ring
  exact mul_left_cancel₀ (neg_ne_zero.mpr Complex.I_ne_zero) hfactored

end

end RiemannGaussian
