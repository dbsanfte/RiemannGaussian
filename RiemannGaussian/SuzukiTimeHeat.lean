/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.GaussianLaplaceHeat
import RiemannGaussian.SuzukiBalancedCells

/-!
# Gaussian time averaging of the actual signed Suzuki signal

The literal positive-time arithmetic signal has a convergent heat average
at every positive width. Its exact value is the full Gaussian-weighted
completed-xi Laplace contour. The abscissa is arbitrary in the proved
convergence half-plane; this is not a contour shift through zeros.

Each hypothetical zero retains its actual multiplicity residue, multiplied
by `exp(a*z + tau*z^2)`. Recording this factor is essential when heat width
grows with time: it can suppress the source as well as the remainder.
No lower bound on the unsmoothed arithmetic potential is asserted here.
-/

namespace RiemannGaussian
noncomputable section
open Complex Filter MeasureTheory Set
open scoped Topology

/-- The Gaussian average of the original signed signal, extended by zero
to nonpositive time. The coefficient equals `1/sqrt(4*pi*tau)` when
`tau > 0`. -/
def suzukiLogTimeHeat (tau a : ℝ) : ℝ :=
  (Real.sqrt (Real.pi / tau) / (2 * Real.pi)) *
    ∫ u : ℝ in Ioi 0, suzukiChebyshevLogAverageLaplaceSignal u *
      Real.exp (-(a - u) ^ 2 / (4 * tau))

/-- The heat normalization is the usual probability Gaussian coefficient. -/
theorem suzukiLogTimeHeat_normalization {tau : ℝ} (htau : 0 < tau) :
    Real.sqrt (Real.pi / tau) / (2 * Real.pi) =
      1 / Real.sqrt (4 * Real.pi * tau) := by
  rw [Real.sqrt_div Real.pi_pos.le,
    Real.sqrt_mul (show 0 ≤ 4 * Real.pi by positivity),
    Real.sqrt_mul (show (0 : ℝ) ≤ 4 by norm_num)]
  norm_num
  have hp := Real.sq_sqrt Real.pi_pos.le
  have hpn := (Real.sqrt_pos.mpr Real.pi_pos).ne'
  have htn := (Real.sqrt_pos.mpr htau).ne'
  field_simp
  nlinarith

/-- The complete signed arithmetic Laplace integrand is integrable on its
literal positive-time support throughout the safe half-plane. -/
theorem integrableOn_suzukiSignal_complex_laplace {z : ℂ} (hz : 1 / 2 < z.re) :
    IntegrableOn (fun u : ℝ => (suzukiChebyshevLogAverageLaplaceSignal u : ℂ) *
      Complex.exp (-z * (u : ℂ))) (Ioi 0) := by
  have h := integrable_suzukiChebyshevLogAverageComplexLaplaceIntegrand hz
  exact (integrable_indicator_iff measurableSet_Ioi).mp h

/-- Every positive-width heat integral of the actual signed signal is
absolutely convergent, including at centers before time zero. -/
theorem integrableOn_suzukiSignal_timeGaussian {tau : ℝ} (htau : 0 < tau) (a : ℝ) :
    IntegrableOn (fun u : ℝ => suzukiChebyshevLogAverageLaplaceSignal u *
      Real.exp (-(a - u) ^ 2 / (4 * tau))) (Ioi 0) := by
  have h := integrable_timeGaussian_mul_of_integrable_laplace (sigma := 1) htau
    (integrableOn_suzukiSignal_complex_laplace (z := 1) (by norm_num)) a
  simpa only [IntegrableOn, RCLike.re_to_complex, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    zero_mul, sub_zero] using h.re

/-- The entire heat multiplier times the genuine completed Laplace
response, before any real part, norm, or contour deformation. -/
def suzukiTimeHeatResponse (a tau : ℝ) (z : ℂ) : ℂ :=
  Complex.exp ((a : ℂ) * z + (tau : ℂ) * z ^ 2) *
    suzukiChebyshevLogAverageLaplaceCompletedContinuation z

private theorem suzukiLaplace_eq_setIntegral (z : ℂ) :
    suzukiChebyshevLogAverageComplexLaplaceTransform z =
      ∫ u : ℝ in Ioi 0, (suzukiChebyshevLogAverageLaplaceSignal u : ℂ) *
        Complex.exp (-z * (u : ℂ)) := by
  exact integral_indicator measurableSet_Ioi

/-- The genuine completed response is integrable on each safe vertical
line after Gaussian time averaging. -/
theorem integrable_suzukiTimeHeatResponse_vertical {tau sigma : ℝ}
    (htau : 0 < tau) (hsigma : 1 / 2 < sigma) (a : ℝ) :
    Integrable (fun y : ℝ =>
      suzukiTimeHeatResponse a tau ((sigma : ℂ) + (y : ℂ) * I)) := by
  have h := integrable_gaussianLaplace_vertical htau
    (integrableOn_suzukiSignal_complex_laplace (z := sigma) hsigma) a
  apply h.congr
  filter_upwards with y
  rw [← suzukiLaplace_eq_setIntegral,
    suzukiChebyshevLogAverageComplexLaplaceTransform_eq_completedContinuation
      (by simpa [suzukiChebyshevLogAverageComplexLaplaceDomain] using hsigma)]
  rfl

/-- Exact time-heat formula for the actual arithmetic signal. The full
complex contour, all zero residues, and positive-time support are retained. -/
theorem integral_suzukiTimeHeatResponse_vertical {tau sigma : ℝ}
    (htau : 0 < tau) (hsigma : 1 / 2 < sigma) (a : ℝ) :
    (∫ y : ℝ, suzukiTimeHeatResponse a tau ((sigma : ℂ) + (y : ℂ) * I)) =
      ((2 * Real.pi * suzukiLogTimeHeat tau a : ℝ) : ℂ) := by
  have h := integral_gaussianLaplace_vertical_eq_timeHeat htau
    (integrableOn_suzukiSignal_complex_laplace (z := sigma) hsigma) a
  simp_rw [← suzukiLaplace_eq_setIntegral] at h
  have heq (y : ℝ) : suzukiChebyshevLogAverageComplexLaplaceTransform
      ((sigma : ℂ) + (y : ℂ) * I) =
      suzukiChebyshevLogAverageLaplaceCompletedContinuation
        ((sigma : ℂ) + (y : ℂ) * I) :=
    suzukiChebyshevLogAverageComplexLaplaceTransform_eq_completedContinuation
      (by simpa [suzukiChebyshevLogAverageComplexLaplaceDomain] using hsigma)
  simp_rw [heq] at h
  change (∫ y : ℝ, suzukiTimeHeatResponse a tau ((sigma : ℂ) + (y : ℂ) * I)) = _ at h
  rw [h]
  simp_rw [← Complex.ofReal_mul]
  rw [integral_complex_ofReal, ← Complex.ofReal_mul]
  congr 1
  unfold suzukiLogTimeHeat
  field_simp

/-- Every safe abscissa gives exactly the same signed time average. No
zero-free assumption between arbitrary contours is being introduced. -/
theorem integral_suzukiTimeHeatResponse_vertical_independent {tau sigma eta : ℝ}
    (htau : 0 < tau) (hsigma : 1 / 2 < sigma) (heta : 1 / 2 < eta) (a : ℝ) :
    (∫ y : ℝ, suzukiTimeHeatResponse a tau ((sigma : ℂ) + (y : ℂ) * I)) =
      ∫ y : ℝ, suzukiTimeHeatResponse a tau ((eta : ℂ) + (y : ℂ) * I) := by
  rw [integral_suzukiTimeHeatResponse_vertical htau hsigma,
    integral_suzukiTimeHeatResponse_vertical htau heta]

/-- The exact source at an actual zero, including its analytic multiplicity. -/
def suzukiTimeHeatZeroSource (rho : NontrivialZetaZero) (a tau : ℝ) : ℂ :=
  Complex.exp ((a : ℂ) * suzukiChebyshevLaplaceZeroCoordinate rho +
    (tau : ℂ) * suzukiChebyshevLaplaceZeroCoordinate rho ^ 2) *
      ((analyticZetaZeroMultiplicity rho : ℂ) /
        suzukiChebyshevLaplaceZeroCoordinate rho ^ 2)

/-- Heat weighting preserves the exact local pole identity. This statement
alone does not sum residues or justify a contour crossing. -/
theorem tendsto_suzukiTimeHeatResponse_zero_residue (rho : NontrivialZetaZero)
    (hp : suzukiChebyshevLaplaceZeroCoordinate rho ≠ 0) (a tau : ℝ) :
    Tendsto (fun z : ℂ => (z - suzukiChebyshevLaplaceZeroCoordinate rho) *
      suzukiTimeHeatResponse a tau z) (𝓝[≠] suzukiChebyshevLaplaceZeroCoordinate rho)
      (𝓝 (suzukiTimeHeatZeroSource rho a tau)) := by
  have hc : Continuous (fun z : ℂ => Complex.exp ((a : ℂ) * z + (tau : ℂ) * z ^ 2)) := by
    fun_prop
  have h := (hc.continuousAt.tendsto.mono_left nhdsWithin_le_nhds).mul
    (tendsto_suzukiChebyshevLaplaceZeroCoordinate_mul_completedContinuation rho hp)
  apply h.congr'
  filter_upwards with z
  dsimp [suzukiTimeHeatResponse]
  ring

/-- No finite heat width cancels a nonzero zero residue. -/
theorem suzukiTimeHeatZeroSource_ne_zero (rho : NontrivialZetaZero)
    (hp : suzukiChebyshevLaplaceZeroCoordinate rho ≠ 0) (a tau : ℝ) :
    suzukiTimeHeatZeroSource rho a tau ≠ 0 := by
  apply mul_ne_zero (Complex.exp_ne_zero _)
  exact div_ne_zero (by exact_mod_cast (analyticZetaZeroMultiplicity_positive rho).ne')
    (pow_ne_zero _ hp)

/-- Exact source magnitude: real-part growth and ordinate damping remain
separate until this downstream equality. -/
theorem norm_suzukiTimeHeatZeroSource (rho : NontrivialZetaZero) (a tau : ℝ) :
    ‖suzukiTimeHeatZeroSource rho a tau‖ =
      Real.exp (a * (rho.1.re - 1 / 2) +
        tau * ((rho.1.re - 1 / 2) ^ 2 - rho.1.im ^ 2)) *
        ((analyticZetaZeroMultiplicity rho : ℝ) /
          ‖suzukiChebyshevLaplaceZeroCoordinate rho‖ ^ 2) := by
  rw [suzukiTimeHeatZeroSource, norm_mul, Complex.norm_exp, norm_div, norm_pow,
    Complex.norm_natCast]
  congr 2
  simp [suzukiChebyshevLaplaceZeroCoordinate, Complex.mul_re, pow_two]

/-- For width proportional to log time, the exact source exponent is
`delta + kappa * (delta^2 - gamma^2)`. Wider heat can therefore change its
exponential growth into decay; it is not free arithmetic cancellation. -/
theorem norm_suzukiTimeHeatZeroSource_linear_width
    (rho : NontrivialZetaZero) (a kappa : ℝ) :
    ‖suzukiTimeHeatZeroSource rho a (kappa * a)‖ =
      Real.exp (a * ((rho.1.re - 1 / 2) +
        kappa * ((rho.1.re - 1 / 2) ^ 2 - rho.1.im ^ 2))) *
        ((analyticZetaZeroMultiplicity rho : ℝ) /
          ‖suzukiChebyshevLaplaceZeroCoordinate rho‖ ^ 2) := by
  rw [norm_suzukiTimeHeatZeroSource]
  congr 2
  ring

/-- The logarithmic size keeps the complete width penalty and the
multiplicity constant explicitly. -/
theorem log_norm_suzukiTimeHeatZeroSource (rho : NontrivialZetaZero)
    (hp : suzukiChebyshevLaplaceZeroCoordinate rho ≠ 0) (a tau : ℝ) :
    Real.log ‖suzukiTimeHeatZeroSource rho a tau‖ =
      a * (rho.1.re - 1 / 2) +
        tau * ((rho.1.re - 1 / 2) ^ 2 - rho.1.im ^ 2) +
        Real.log ((analyticZetaZeroMultiplicity rho : ℝ) /
          ‖suzukiChebyshevLaplaceZeroCoordinate rho‖ ^ 2) := by
  have hc : 0 < (analyticZetaZeroMultiplicity rho : ℝ) /
      ‖suzukiChebyshevLaplaceZeroCoordinate rho‖ ^ 2 :=
    div_pos (by exact_mod_cast analyticZetaZeroMultiplicity_positive rho)
      (pow_pos (norm_pos_iff.mpr hp) _)
  rw [norm_suzukiTimeHeatZeroSource,
    Real.log_mul (Real.exp_ne_zero _) hc.ne', Real.log_exp]

/-- Every sublinear heat-width schedule preserves the exact exponential
rate of each zero source. This covers all such schedules, not a sampled
choice of widths or frequencies. It does not control interference between
different zero contributions. -/
theorem tendsto_log_norm_suzukiTimeHeatZeroSource_div_time
    (rho : NontrivialZetaZero) (hp : suzukiChebyshevLaplaceZeroCoordinate rho ≠ 0)
    {tau : ℝ → ℝ} (htau : Tendsto (fun a => tau a / a) atTop (𝓝 0)) :
    Tendsto (fun a : ℝ => Real.log ‖suzukiTimeHeatZeroSource rho a (tau a)‖ / a)
      atTop (𝓝 (rho.1.re - 1 / 2)) := by
  have hc : Tendsto (fun a : ℝ =>
      Real.log ((analyticZetaZeroMultiplicity rho : ℝ) /
        ‖suzukiChebyshevLaplaceZeroCoordinate rho‖ ^ 2) / a) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop tendsto_id
  have h := ((tendsto_const_nhds (x := rho.1.re - 1 / 2)).add
    (htau.mul_const ((rho.1.re - 1 / 2) ^ 2 - rho.1.im ^ 2))).add hc
  simp only [zero_mul, add_zero] at h
  apply h.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with a ha
  rw [log_norm_suzukiTimeHeatZeroSource rho hp]
  field_simp

/-- A hypothetical right-half zero has an unbounded source under every
sublinear width schedule. The estimate concerns the individual residue,
not the sum of residues. -/
theorem tendsto_norm_suzukiTimeHeatZeroSource_atTop_of_sublinear
    (rho : NontrivialZetaZero) (hrho : 1 / 2 < rho.1.re)
    {tau : ℝ → ℝ} (htau : Tendsto (fun a => tau a / a) atTop (𝓝 0)) :
    Tendsto (fun a : ℝ => ‖suzukiTimeHeatZeroSource rho a (tau a)‖) atTop atTop := by
  have hp : suzukiChebyshevLaplaceZeroCoordinate rho ≠ 0 := by
    intro h
    have hreal := congrArg Complex.re h
    norm_num [suzukiChebyshevLaplaceZeroCoordinate] at hreal
    linarith
  have hd : 0 < (rho.1.re - 1 / 2) / 2 := by linarith
  have hr := tendsto_log_norm_suzukiTimeHeatZeroSource_div_time rho hp htau
  have he : Tendsto (fun a : ℝ => Real.exp (((rho.1.re - 1 / 2) / 2) * a)) atTop atTop :=
    Real.tendsto_exp_atTop.comp (tendsto_id.const_mul_atTop hd)
  apply tendsto_atTop_mono' atTop _ he
  filter_upwards [hr.eventually (lt_mem_nhds (show
    (rho.1.re - 1 / 2) / 2 < rho.1.re - 1 / 2 by linarith)),
    eventually_gt_atTop (0 : ℝ)] with a hra ha
  have hlog := (le_div_iff₀ ha).mp hra.le
  calc
    _ ≤ Real.exp (Real.log ‖suzukiTimeHeatZeroSource rho a (tau a)‖) :=
      Real.exp_le_exp.mpr hlog
    _ = _ := Real.exp_log (norm_pos_iff.mpr (suzukiTimeHeatZeroSource_ne_zero rho hp a (tau a)))

end
end RiemannGaussian
