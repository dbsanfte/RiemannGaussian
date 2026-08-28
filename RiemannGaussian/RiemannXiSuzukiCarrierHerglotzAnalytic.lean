import RiemannGaussian.RiemannXiSuzukiCarrierHerglotz

/-!
# Analyticity of Suzuki's arithmetic carrier Herglotz transform

This file differentiates the normalized arithmetic carrier transform under
its defining integral.  The derivative is the density-weighted squared
resolvent, and the transform is analytic on the complement of the real axis.
This also supplies the confluent value of the carrier Pick kernel when the
two spectral parameters collide after reflection.

No boundary limit, tail vanishing, or RH conclusion is asserted here.
-/

open Asymptotics Complex Filter MeasureTheory Metric Polynomial Set Topology
open scoped Classical ComplexConjugate ENNReal Topology lp

namespace RiemannGaussian

noncomputable section

/-- The squared resolvent occurring as the parameter derivative of the
normalized Cauchy kernel. -/
def suzukiXiSquaredResolvent (z : ℂ) (x : ℝ) : ℂ :=
  1 / (((x : ℂ) - z) ^ 2)

/-- The real-boundary squared resolvent is absolutely integrable for every
nonreal parameter. -/
theorem integrable_suzukiXiSquaredResolvent
    {z : ℂ} (hz : z.im ≠ 0) :
    Integrable (suzukiXiSquaredResolvent z) := by
  have hgap :
      (1 : ℂ[X]).natDegree + 2 ≤ ((X - C z) ^ 2).natDegree := by
    have hden : ((X - C z) ^ 2).natDegree = 2 := by
      compute_degree
      norm_num
    rw [hden]
    norm_num
  have hreal : ∀ x : ℝ, ((X - C z) ^ 2).eval (x : ℂ) ≠ 0 := by
    intro x
    simp only [eval_pow, eval_sub, eval_X, eval_C]
    exact pow_ne_zero 2 (ofReal_sub_ne_zero_of_im_ne_zero hz x)
  have h := polynomialBoundaryQuotient_integrable_of_natDegree_add_two_le
    hgap hreal
  apply h.congr
  exact Eventually.of_forall fun x ↦ by
    simp [suzukiXiSquaredResolvent]

/-- The density-weighted squared resolvent that will be the derivative
integrand of the arithmetic carrier transform. -/
def suzukiXiCarrierHerglotzDerivativeIntegrand
    (z : ℂ) (x : ℝ) : ℂ :=
  (suzukiXiRealAxisArithmeticCarrierDensity x : ℂ) *
    suzukiXiSquaredResolvent z x

/-- The derivative integrand is absolutely integrable at every nonreal
parameter. -/
theorem integrable_suzukiXiCarrierHerglotzDerivativeIntegrand
    {z : ℂ} (hz : z.im ≠ 0) :
    Integrable (suzukiXiCarrierHerglotzDerivativeIntegrand z) := by
  have hdensity : AEStronglyMeasurable (fun x : ℝ ↦
      (suzukiXiRealAxisArithmeticCarrierDensity x : ℂ)) :=
    (Complex.continuous_ofReal.measurable.comp
      measurable_suzukiXiRealAxisArithmeticCarrierDensity).aestronglyMeasurable
  have hbound : ∀ᵐ x : ℝ ∂volume,
      ‖(suzukiXiRealAxisArithmeticCarrierDensity x : ℂ)‖ ≤ 1 := by
    exact Eventually.of_forall fun x ↦ by
      rw [Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (suzukiXiRealAxisArithmeticCarrierDensity_nonneg x)]
      exact suzukiXiRealAxisArithmeticCarrierDensity_le_one x
  exact (integrable_suzukiXiSquaredResolvent hz).bdd_mul
    hdensity hbound

/-- Pointwise differentiation of the normalized Cauchy kernel with respect
to its nonreal parameter. -/
theorem hasDerivAt_suzukiXiNormalizedCauchyKernel
    {z : ℂ} (hz : z.im ≠ 0) (x : ℝ) :
    HasDerivAt (fun w : ℂ ↦ suzukiXiNormalizedCauchyKernel w x)
      (suzukiXiSquaredResolvent z x) z := by
  unfold suzukiXiNormalizedCauchyKernel suzukiXiSquaredResolvent
  have hxz := ofReal_sub_ne_zero_of_im_ne_zero hz x
  have hlinear : HasDerivAt (fun w : ℂ ↦ (x : ℂ) - w) (-1) z :=
    (hasDerivAt_id' z).const_sub (x : ℂ)
  have hinverse := hlinear.inv hxz
  simpa [one_div] using
    hinverse.sub_const ((x : ℂ) / (1 + (x : ℂ) ^ 2))

/-- Pointwise differentiation of the arithmetic carrier Herglotz integrand
with respect to its nonreal parameter. -/
theorem hasDerivAt_suzukiXiCarrierHerglotzIntegrand
    {z : ℂ} (hz : z.im ≠ 0) (x : ℝ) :
    HasDerivAt (fun w : ℂ ↦ suzukiXiCarrierHerglotzIntegrand w x)
      (suzukiXiCarrierHerglotzDerivativeIntegrand z x) z := by
  unfold suzukiXiCarrierHerglotzIntegrand
    suzukiXiCarrierHerglotzDerivativeIntegrand
  exact (hasDerivAt_suzukiXiNormalizedCauchyKernel hz x).const_mul _

/-- On the half-height ball around a nonreal parameter, every squared
resolvent is bounded by four times the squared resolvent at the center. -/
theorem norm_suzukiXiSquaredResolvent_le_four_mul
    {z w : ℂ} (hz : z.im ≠ 0)
    (hw : w ∈ ball z (|z.im| / 2)) (x : ℝ) :
    ‖suzukiXiSquaredResolvent w x‖ ≤
      4 * ‖suzukiXiSquaredResolvent z x‖ := by
  have hxz : (x : ℂ) - z ≠ 0 :=
    ofReal_sub_ne_zero_of_im_ne_zero hz x
  have hheight : |z.im| ≤ ‖(x : ℂ) - z‖ := by
    simpa only [Complex.sub_im, Complex.ofReal_im, zero_sub, abs_neg] using
      Complex.abs_im_le_norm ((x : ℂ) - z)
  have hwlt : ‖w - z‖ < ‖(x : ℂ) - z‖ / 2 := by
    rw [mem_ball, dist_eq_norm] at hw
    exact hw.trans_le (div_le_div_of_nonneg_right hheight (by norm_num))
  have hhalf : ‖(x : ℂ) - z‖ / 2 < ‖(x : ℂ) - w‖ := by
    have htriangle : ‖(x : ℂ) - z‖ ≤
        ‖(x : ℂ) - w‖ + ‖w - z‖ :=
      norm_sub_le_norm_sub_add_norm_sub (x : ℂ) w z
    linarith
  have hcenter : 0 < ‖(x : ℂ) - z‖ := norm_pos_iff.mpr hxz
  have hmoving : 0 < ‖(x : ℂ) - w‖ := by linarith
  have hcross : ‖(x : ℂ) - z‖ ^ 2 ≤
      4 * ‖(x : ℂ) - w‖ ^ 2 := by
    nlinarith [sq_nonneg
      (2 * ‖(x : ℂ) - w‖ - ‖(x : ℂ) - z‖)]
  simp only [suzukiXiSquaredResolvent, norm_div, norm_one, norm_pow]
  calc
    1 / ‖(x : ℂ) - w‖ ^ 2 ≤ 4 / ‖(x : ℂ) - z‖ ^ 2 := by
      exact (div_le_div_iff₀ (sq_pos_of_pos hmoving)
        (sq_pos_of_pos hcenter)).2 (by simpa using hcross)
    _ = 4 * (1 / ‖(x : ℂ) - z‖ ^ 2) := by ring

/-- The half-height ball about a nonreal point does not meet the real axis. -/
theorem im_ne_zero_of_mem_half_height_ball
    {z w : ℂ} (hz : z.im ≠ 0)
    (hw : w ∈ ball z (|z.im| / 2)) :
    w.im ≠ 0 := by
  intro hwim
  have himnorm : |z.im| ≤ ‖w - z‖ := by
    simpa only [Complex.sub_im, hwim, zero_sub, abs_neg] using
      Complex.abs_im_le_norm (w - z)
  rw [mem_ball, dist_eq_norm] at hw
  have habs : 0 < |z.im| := abs_pos.mpr hz
  linarith

/-- The same center-resolvent majorant controls the full density-weighted
derivative integrand throughout the half-height ball. -/
theorem norm_suzukiXiCarrierHerglotzDerivativeIntegrand_le
    {z w : ℂ} (hz : z.im ≠ 0)
    (hw : w ∈ ball z (|z.im| / 2)) (x : ℝ) :
    ‖suzukiXiCarrierHerglotzDerivativeIntegrand w x‖ ≤
      4 * ‖suzukiXiSquaredResolvent z x‖ := by
  have hdensity :
      ‖(suzukiXiRealAxisArithmeticCarrierDensity x : ℂ)‖ ≤ 1 := by
    rw [Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (suzukiXiRealAxisArithmeticCarrierDensity_nonneg x)]
    exact suzukiXiRealAxisArithmeticCarrierDensity_le_one x
  unfold suzukiXiCarrierHerglotzDerivativeIntegrand
  rw [norm_mul]
  calc
    ‖(suzukiXiRealAxisArithmeticCarrierDensity x : ℂ)‖ *
        ‖suzukiXiSquaredResolvent w x‖ ≤
        1 * (4 * ‖suzukiXiSquaredResolvent z x‖) :=
      mul_le_mul hdensity
        (norm_suzukiXiSquaredResolvent_le_four_mul hz hw x)
        (norm_nonneg _) zero_le_one
    _ = 4 * ‖suzukiXiSquaredResolvent z x‖ := by ring

/-- Differentiation under the literal infinite-density integral: away from
the real axis, the derivative of the normalized carrier transform is the
integral of its density-weighted squared resolvent. -/
theorem hasDerivAt_suzukiXiCarrierHerglotzTransform
    {z : ℂ} (hz : z.im ≠ 0) :
    HasDerivAt suzukiXiCarrierHerglotzTransform
      (∫ x : ℝ, suzukiXiCarrierHerglotzDerivativeIntegrand z x) z := by
  let s : Set ℂ := ball z (|z.im| / 2)
  have hradius : 0 < |z.im| / 2 := div_pos (abs_pos.mpr hz) (by norm_num)
  have hs : s ∈ 𝓝 z := ball_mem_nhds z hradius
  have hF_meas : ∀ᶠ w in 𝓝 z,
      AEStronglyMeasurable (suzukiXiCarrierHerglotzIntegrand w) := by
    filter_upwards [hs] with w hw
    exact (integrable_suzukiXiCarrierHerglotzIntegrand
      (im_ne_zero_of_mem_half_height_ball hz hw)).aestronglyMeasurable
  have hbound : ∀ᵐ x : ℝ ∂volume, ∀ w ∈ s,
      ‖suzukiXiCarrierHerglotzDerivativeIntegrand w x‖ ≤
        4 * ‖suzukiXiSquaredResolvent z x‖ := by
    exact Eventually.of_forall fun x w hw ↦
      norm_suzukiXiCarrierHerglotzDerivativeIntegrand_le hz hw x
  have hdiff : ∀ᵐ x : ℝ ∂volume, ∀ w ∈ s,
      HasDerivAt (fun u : ℂ ↦ suzukiXiCarrierHerglotzIntegrand u x)
        (suzukiXiCarrierHerglotzDerivativeIntegrand w x) w := by
    exact Eventually.of_forall fun x w hw ↦
      hasDerivAt_suzukiXiCarrierHerglotzIntegrand
        (im_ne_zero_of_mem_half_height_ball hz hw) x
  have hmajor : Integrable (fun x : ℝ ↦
      4 * ‖suzukiXiSquaredResolvent z x‖) :=
    (integrable_suzukiXiSquaredResolvent hz).norm.const_mul 4
  exact (hasDerivAt_integral_of_dominated_loc_of_deriv_le
    hs hF_meas (integrable_suzukiXiCarrierHerglotzIntegrand hz)
    (integrable_suzukiXiCarrierHerglotzDerivativeIntegrand hz).aestronglyMeasurable
    hbound hmajor hdiff).2

/-- Exact derivative formula for the normalized arithmetic carrier
Herglotz transform away from the real axis. -/
theorem deriv_suzukiXiCarrierHerglotzTransform
    {z : ℂ} (hz : z.im ≠ 0) :
    deriv suzukiXiCarrierHerglotzTransform z =
      ∫ x : ℝ, suzukiXiCarrierHerglotzDerivativeIntegrand z x :=
  (hasDerivAt_suzukiXiCarrierHerglotzTransform hz).deriv

/-- The normalized arithmetic carrier transform is analytic on the full
complement of the real axis. -/
theorem analyticOn_suzukiXiCarrierHerglotzTransform :
    AnalyticOn ℂ suzukiXiCarrierHerglotzTransform
      {z : ℂ | z.im ≠ 0} := by
  have hopen : IsOpen {z : ℂ | z.im ≠ 0} :=
    isOpen_ne.preimage Complex.continuous_im
  rw [analyticOn_iff_differentiableOn hopen]
  intro z hz
  exact (hasDerivAt_suzukiXiCarrierHerglotzTransform hz).differentiableAt
    |>.differentiableWithinAt

/-- When a node parameter coincides with the reflected second parameter,
the carrier Gram kernel is the derivative of the scalar Herglotz transform.
This is the confluent case missing from an ordinary divided quotient. -/
theorem suzukiXiBoundaryCarrierGramKernel_eq_herglotzDeriv_of_collision
    (rho sigma : NontrivialZetaZero)
    (hsigma : (zetaSpectralCoordinate sigma.1).im ≠ 0)
    (hcollision : zetaSpectralCoordinate sigma.1 =
      starRingEnd ℂ (zetaSpectralCoordinate rho.1)) :
    suzukiXiBoundaryCarrierGramKernel rho sigma =
      deriv suzukiXiCarrierHerglotzTransform
        (zetaSpectralCoordinate sigma.1) := by
  rw [suzukiXiBoundaryCarrierGramKernel_eq_arithmetic_integral,
    deriv_suzukiXiCarrierHerglotzTransform hsigma]
  apply integral_congr_ae
  exact Eventually.of_forall fun x ↦ by
    simp [suzukiXiBoundaryArithmeticCarrierGramIntegrand,
      suzukiXiCarrierHerglotzDerivativeIntegrand,
      suzukiXiSquaredResolvent, ← hcollision, pow_two,
      div_eq_mul_inv, mul_inv_rev]

/-- The total confluent divided difference of the normalized arithmetic
carrier transform.  At equal parameters it is the complex derivative; away
from equality it is the ordinary divided quotient. -/
def suzukiXiCarrierHerglotzConfluentDividedDifference
    (z w : ℂ) : ℂ :=
  if z = w then
    deriv suzukiXiCarrierHerglotzTransform z
  else
    (suzukiXiCarrierHerglotzTransform z -
      suzukiXiCarrierHerglotzTransform w) / (z - w)

/-- For every pair of genuine off-axis xi nodes, the common-carrier Gram
kernel is exactly the total confluent divided difference of one scalar
analytic Herglotz transform. -/
theorem suzukiXiBoundaryCarrierGramKernel_eq_herglotzConfluent
    (rho sigma : NontrivialZetaZero)
    (hrho : (zetaSpectralCoordinate rho.1).im ≠ 0)
    (hsigma : (zetaSpectralCoordinate sigma.1).im ≠ 0) :
    suzukiXiBoundaryCarrierGramKernel rho sigma =
      suzukiXiCarrierHerglotzConfluentDividedDifference
        (zetaSpectralCoordinate sigma.1)
        (starRingEnd ℂ (zetaSpectralCoordinate rho.1)) := by
  by_cases hcollision : zetaSpectralCoordinate sigma.1 =
      starRingEnd ℂ (zetaSpectralCoordinate rho.1)
  · rw [suzukiXiCarrierHerglotzConfluentDividedDifference,
      if_pos hcollision]
    exact suzukiXiBoundaryCarrierGramKernel_eq_herglotzDeriv_of_collision
      rho sigma hsigma hcollision
  · rw [suzukiXiCarrierHerglotzConfluentDividedDifference,
      if_neg hcollision]
    have hidentity := suzukiXiCarrierHerglotzTransform_node_sub
      rho sigma hrho hsigma
    rw [hidentity]
    exact (mul_div_cancel_left₀
      (suzukiXiBoundaryCarrierGramKernel rho sigma)
      (sub_ne_zero.mpr hcollision)).symm

end

end RiemannGaussian
