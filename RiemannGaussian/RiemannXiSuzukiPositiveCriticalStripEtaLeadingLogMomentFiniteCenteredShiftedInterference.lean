import RiemannGaussian.RiemannXiSuzukiPositiveCriticalStripEtaLeadingLogMomentFiniteCenteredShiftedCoupling

/-!
# One-measure interference form for the centered finite eta residual

The shifted coupling module writes the completed finite partner residual as a
unit phase times a difference of two Fourier--Laplace moments.  Here those two
moments are combined into one absolutely integrable function on the common
shifted eta tail measure.

Writing `delta = rho.re - 1/2`, the common integrand has the exact form

`u^m exp (-u/2) * (A_N exp (delta*u) exp (-I*gamma*u)
  + B_N exp (-delta*u) exp (I*gamma*u))`.

Thus horizontal displacement appears only through the reciprocal real tilts
`exp (delta*u)` and `exp (-delta*u)` inside one interference factor.  Lean
proves both the complex residual identity and the resulting exact norm
identity, including every integrability condition.  This does not prevent
oscillatory cancellation of the integral; an eta-specific coercivity theorem
for this one-measure interference form remains open.
-/

open Complex Filter MeasureTheory Metric Set Topology
open scoped Classical ComplexConjugate ENNReal Interval Topology

namespace RiemannGaussian

noncomputable section

/-- The completion and cutoff-decay coefficient of the shifted partner-tail
moment. -/
def pairedEtaCompletedLeadingLogCutoffCenteredShiftedPartnerCoefficient
    (rho : NontrivialZetaZero) (N : ℕ) : ℂ :=
  pairedEtaXiCompletionFactor
      (NontrivialZetaZero.conjugatePartner rho).1 *
    (NontrivialZetaZero.conjugatePartner rho).1 *
    (Real.exp
      (-(1 - rho.1.re) * pairedEtaLogTailCutoff N) : ℂ)

/-- The parity, conjugated completion, cutoff decay, and relative phase
coefficient of the shifted original-tail moment. -/
def pairedEtaCompletedLeadingLogCutoffCenteredShiftedConjugateCoefficient
    (rho : NontrivialZetaZero) (N : ℕ) : ℂ :=
  (-1 : ℂ) ^ (analyticZetaZeroMultiplicity rho) *
    starRingEnd ℂ (pairedEtaXiCompletionFactor rho.1 * rho.1) *
    (Real.exp (-rho.1.re * pairedEtaLogTailCutoff N) : ℂ) *
    pairedEtaLogTailCutoffRelativeOscillation rho.1.im N

/-- The two complementary shifted Fourier--Laplace tails combined pointwise
on their common positive measure. -/
def pairedEtaCompletedLeadingLogCutoffCenteredShiftedCoupledIntegrand
    (rho : NontrivialZetaZero) (N : ℕ) (u : ℝ) : ℂ :=
  -pairedEtaCompletedLeadingLogCutoffCenteredShiftedPartnerCoefficient rho N *
      ((u : ℂ) ^ analyticZetaZeroMultiplicity rho *
        (Real.exp (-(1 - rho.1.re) * u) : ℂ) *
        Complex.exp (-((rho.1.im * u : ℝ) : ℂ) * I)) +
    pairedEtaCompletedLeadingLogCutoffCenteredShiftedConjugateCoefficient rho N *
      ((u : ℂ) ^ analyticZetaZeroMultiplicity rho *
        (Real.exp (-rho.1.re * u) : ℂ) *
        Complex.exp (-((-rho.1.im * u : ℝ) : ℂ) * I))

/-- The shifted coupled core is the coefficient-weighted sum of its two
complementary Fourier--Laplace moments. -/
theorem pairedEtaCompletedLeadingLogCutoffCenteredShiftedCoupledCore_eq_coefficients_mul_moments
    (rho : NontrivialZetaZero) (N : ℕ) :
    pairedEtaCompletedLeadingLogCutoffCenteredShiftedCoupledCore rho N =
      -pairedEtaCompletedLeadingLogCutoffCenteredShiftedPartnerCoefficient rho N *
          pairedEtaShiftedLogTailFourierMoment
            (analyticZetaZeroMultiplicity rho)
            (1 - rho.1.re) rho.1.im N +
        pairedEtaCompletedLeadingLogCutoffCenteredShiftedConjugateCoefficient rho N *
          pairedEtaShiftedLogTailFourierMoment
            (analyticZetaZeroMultiplicity rho)
            rho.1.re (-rho.1.im) N := by
  unfold pairedEtaCompletedLeadingLogCutoffCenteredShiftedCoupledCore
    pairedEtaCompletedLeadingLogCutoffCenteredShiftedPartnerCoefficient
    pairedEtaCompletedLeadingLogCutoffCenteredShiftedConjugateCoefficient
  ring

/-- The pointwise coupled integrand is absolutely integrable on the common
shifted eta tail measure. -/
theorem integrable_pairedEtaCompletedLeadingLogCutoffCenteredShiftedCoupledIntegrand
    (rho : NontrivialZetaZero) (N : ℕ) :
    Integrable
      (pairedEtaCompletedLeadingLogCutoffCenteredShiftedCoupledIntegrand rho N)
      (pairedEtaShiftedLogTailMeasure N) := by
  have hpartner :=
    integrable_pairedEtaShiftedLogTailFourierMoment_integrand
      (analyticZetaZeroMultiplicity rho)
      (sub_pos.mpr (NontrivialZetaZero.re_lt_one rho))
      rho.1.im N
  have hrho :=
    integrable_pairedEtaShiftedLogTailFourierMoment_integrand
      (analyticZetaZeroMultiplicity rho)
      (NontrivialZetaZero.zero_lt_re rho) (-rho.1.im) N
  exact
    (hpartner.const_mul
      (-pairedEtaCompletedLeadingLogCutoffCenteredShiftedPartnerCoefficient
        rho N)).add
      (hrho.const_mul
        (pairedEtaCompletedLeadingLogCutoffCenteredShiftedConjugateCoefficient
          rho N))

/-- The shifted coupled core is one integral over the common positive tail
measure, rather than a difference of two separately presented moments. -/
theorem pairedEtaCompletedLeadingLogCutoffCenteredShiftedCoupledCore_eq_integral_coupledIntegrand
    (rho : NontrivialZetaZero) (N : ℕ) :
    pairedEtaCompletedLeadingLogCutoffCenteredShiftedCoupledCore rho N =
      ∫ u : ℝ,
        pairedEtaCompletedLeadingLogCutoffCenteredShiftedCoupledIntegrand
          rho N u
        ∂pairedEtaShiftedLogTailMeasure N := by
  rw [pairedEtaCompletedLeadingLogCutoffCenteredShiftedCoupledCore_eq_coefficients_mul_moments]
  unfold pairedEtaShiftedLogTailFourierMoment
    pairedEtaCompletedLeadingLogCutoffCenteredShiftedCoupledIntegrand
  rw [integral_add]
  · rw [integral_const_mul, integral_const_mul]
  · exact
      (integrable_pairedEtaShiftedLogTailFourierMoment_integrand
        (analyticZetaZeroMultiplicity rho)
        (sub_pos.mpr (NontrivialZetaZero.re_lt_one rho))
        rho.1.im N).const_mul
          (-pairedEtaCompletedLeadingLogCutoffCenteredShiftedPartnerCoefficient
            rho N)
  · exact
      (integrable_pairedEtaShiftedLogTailFourierMoment_integrand
        (analyticZetaZeroMultiplicity rho)
        (NontrivialZetaZero.zero_lt_re rho) (-rho.1.im) N).const_mul
          (pairedEtaCompletedLeadingLogCutoffCenteredShiftedConjugateCoefficient
            rho N)

/-- After extracting the critical half-tilt, this is the remaining
complementary exponential and oscillatory interference factor. -/
def pairedEtaCompletedLeadingLogCutoffCenteredShiftedInterferenceFactor
    (rho : NontrivialZetaZero) (N : ℕ) (u : ℝ) : ℂ :=
  -pairedEtaCompletedLeadingLogCutoffCenteredShiftedPartnerCoefficient rho N *
      (Real.exp ((rho.1.re - 1 / 2) * u) : ℂ) *
      Complex.exp (-((rho.1.im * u : ℝ) : ℂ) * I) +
    pairedEtaCompletedLeadingLogCutoffCenteredShiftedConjugateCoefficient rho N *
      (Real.exp (-(rho.1.re - 1 / 2) * u) : ℂ) *
      Complex.exp (-((-rho.1.im * u : ℝ) : ℂ) * I)

/-- The common shifted coupled integrand centered exactly at horizontal tilt
`1/2`. -/
def pairedEtaCompletedLeadingLogCutoffCenteredShiftedHalfIntegrand
    (rho : NontrivialZetaZero) (N : ℕ) (u : ℝ) : ℂ :=
  (u : ℂ) ^ analyticZetaZeroMultiplicity rho *
    (Real.exp (-(1 / 2) * u) : ℂ) *
    pairedEtaCompletedLeadingLogCutoffCenteredShiftedInterferenceFactor
      rho N u

/-- Pointwise, complementary tilts factor into the common critical half-tilt
and reciprocal exponentials of the horizontal displacement. -/
theorem pairedEtaCompletedLeadingLogCutoffCenteredShiftedCoupledIntegrand_eq_halfIntegrand
    (rho : NontrivialZetaZero) (N : ℕ) (u : ℝ) :
    pairedEtaCompletedLeadingLogCutoffCenteredShiftedCoupledIntegrand rho N u =
      pairedEtaCompletedLeadingLogCutoffCenteredShiftedHalfIntegrand rho N u := by
  have hpartnerExp : Real.exp (-(1 - rho.1.re) * u) =
      Real.exp (-(1 / 2) * u) *
        Real.exp ((rho.1.re - 1 / 2) * u) := by
    rw [← Real.exp_add]
    congr 1
    ring
  have hrhoExp : Real.exp (-rho.1.re * u) =
      Real.exp (-(1 / 2) * u) *
        Real.exp (-(rho.1.re - 1 / 2) * u) := by
    rw [← Real.exp_add]
    congr 1
    ring
  unfold pairedEtaCompletedLeadingLogCutoffCenteredShiftedCoupledIntegrand
    pairedEtaCompletedLeadingLogCutoffCenteredShiftedHalfIntegrand
    pairedEtaCompletedLeadingLogCutoffCenteredShiftedInterferenceFactor
  rw [hpartnerExp, hrhoExp]
  push_cast
  ring

/-- The half-centered one-measure interference integrand is absolutely
integrable. -/
theorem integrable_pairedEtaCompletedLeadingLogCutoffCenteredShiftedHalfIntegrand
    (rho : NontrivialZetaZero) (N : ℕ) :
    Integrable
      (pairedEtaCompletedLeadingLogCutoffCenteredShiftedHalfIntegrand rho N)
      (pairedEtaShiftedLogTailMeasure N) := by
  apply
    (integrable_pairedEtaCompletedLeadingLogCutoffCenteredShiftedCoupledIntegrand
      rho N).congr
  filter_upwards with u
  exact
    pairedEtaCompletedLeadingLogCutoffCenteredShiftedCoupledIntegrand_eq_halfIntegrand
      rho N u

/-- The shifted coupled core is exactly the integral of its critical-half
centered interference form over one positive measure. -/
theorem pairedEtaCompletedLeadingLogCutoffCenteredShiftedCoupledCore_eq_integral_halfIntegrand
    (rho : NontrivialZetaZero) (N : ℕ) :
    pairedEtaCompletedLeadingLogCutoffCenteredShiftedCoupledCore rho N =
      ∫ u : ℝ,
        pairedEtaCompletedLeadingLogCutoffCenteredShiftedHalfIntegrand rho N u
        ∂pairedEtaShiftedLogTailMeasure N := by
  rw [pairedEtaCompletedLeadingLogCutoffCenteredShiftedCoupledCore_eq_integral_coupledIntegrand]
  apply integral_congr_ae
  filter_upwards with u
  exact
    pairedEtaCompletedLeadingLogCutoffCenteredShiftedCoupledIntegrand_eq_halfIntegrand
      rho N u

/-- The completed centered residual itself is a unit cutoff phase times the
single critical-half-centered interference integral. -/
theorem pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidual_eq_oscillation_mul_integral_halfIntegrand
    (rho : NontrivialZetaZero) (N : ℕ) :
    pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidual rho N =
      pairedEtaLogTailCutoffOscillation rho.1.im N *
        ∫ u : ℝ,
          pairedEtaCompletedLeadingLogCutoffCenteredShiftedHalfIntegrand rho N u
          ∂pairedEtaShiftedLogTailMeasure N := by
  rw [pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidual_eq_oscillation_mul_shiftedCoupledCore,
    pairedEtaCompletedLeadingLogCutoffCenteredShiftedCoupledCore_eq_integral_halfIntegrand]

/-- The completed centered residual norm is exactly the norm of one
critical-half-centered interference integral over the shifted positive
measure. -/
theorem norm_pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidual_eq_integral_halfIntegrand
    (rho : NontrivialZetaZero) (N : ℕ) :
    ‖pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidual rho N‖ =
      ‖∫ u : ℝ,
          pairedEtaCompletedLeadingLogCutoffCenteredShiftedHalfIntegrand rho N u
          ∂pairedEtaShiftedLogTailMeasure N‖ := by
  rw [norm_pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidual_eq_shiftedCoupledCore,
    pairedEtaCompletedLeadingLogCutoffCenteredShiftedCoupledCore_eq_integral_halfIntegrand]

end

end RiemannGaussian
