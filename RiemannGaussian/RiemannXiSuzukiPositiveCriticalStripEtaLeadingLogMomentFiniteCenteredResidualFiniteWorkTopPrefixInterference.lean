import RiemannGaussian.RiemannXiSuzukiPositiveCriticalStripEtaLeadingLogMomentFiniteCenteredResidualFiniteWorkTopPrefixReduction
import RiemannGaussian.RiemannXiSuzukiPositiveCriticalStripEtaLeadingLogMomentFiniteCenteredShiftedInterference

/-!
# One-measure interference form of the top finite-work prefix

The remaining square-root frontier is the order-`m-1` completed finite prefix
`C_(m-1,N+1)`.  Lower-moment vanishing identifies this finite prefix with a
coupled tail on the shifted positive eta measure.  This module combines its
two complementary Fourier--Laplace moments pointwise, factors out the common
critical half-tilt, and proves the exact norm identity

`|C_(m-1,N+1)| = |integral u^(m-1) exp(-u/2) F_(rho,N+1)(u) d mu_(N+1)(u)|`.

Thus the open half-power estimate is now attached directly to one
phase-sensitive integral over one positive arithmetic measure.  No positivity
or cancellation estimate for that integral is assumed here.
-/

open Complex Filter MeasureTheory Metric Set Topology
open scoped Classical ComplexConjugate ENNReal Interval Topology

namespace RiemannGaussian

noncomputable section

/-- The two complementary order-`m-1` Fourier--Laplace integrands combined
pointwise on the common shifted eta-tail measure at cutoff `N+1`. -/
def pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidualFiniteWorkTopPrefixCoupledIntegrand
    (rho : NontrivialZetaZero) (N : ℕ) (u : ℝ) : ℂ :=
  -pairedEtaCompletedLeadingLogCutoffCenteredShiftedPartnerCoefficient
      rho (N + 1) *
      ((u : ℂ) ^ (analyticZetaZeroMultiplicity rho - 1) *
        (Real.exp (-(1 - rho.1.re) * u) : ℂ) *
        Complex.exp (-((rho.1.im * u : ℝ) : ℂ) * I)) +
    pairedEtaCompletedLeadingLogCutoffCenteredShiftedConjugateCoefficient
      rho (N + 1) *
      ((u : ℂ) ^ (analyticZetaZeroMultiplicity rho - 1) *
        (Real.exp (-rho.1.re * u) : ℂ) *
        Complex.exp (-((-rho.1.im * u : ℝ) : ℂ) * I))

/-- The top-prefix coupled integrand is absolutely integrable on its shifted
positive eta-tail measure. -/
theorem
    integrable_pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidualFiniteWorkTopPrefixCoupledIntegrand
    (rho : NontrivialZetaZero) (N : ℕ) :
    Integrable
      (pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidualFiniteWorkTopPrefixCoupledIntegrand
        rho N)
      (pairedEtaShiftedLogTailMeasure (N + 1)) := by
  have hpartner :=
    integrable_pairedEtaShiftedLogTailFourierMoment_integrand
      (analyticZetaZeroMultiplicity rho - 1)
      (sub_pos.mpr (NontrivialZetaZero.re_lt_one rho))
      rho.1.im (N + 1)
  have hrho :=
    integrable_pairedEtaShiftedLogTailFourierMoment_integrand
      (analyticZetaZeroMultiplicity rho - 1)
      (NontrivialZetaZero.zero_lt_re rho) (-rho.1.im) (N + 1)
  exact
    (hpartner.const_mul
      (-pairedEtaCompletedLeadingLogCutoffCenteredShiftedPartnerCoefficient
        rho (N + 1))).add
      (hrho.const_mul
        (pairedEtaCompletedLeadingLogCutoffCenteredShiftedConjugateCoefficient
          rho (N + 1)))

/-- The generic shifted coupled moment at order `m-1` is the integral of the
top-prefix coupled integrand. -/
theorem
    pairedEtaCompletedLeadingLogCutoffCenteredShiftedCoupledMoment_topOrderPred_eq_integral
    (rho : NontrivialZetaZero) (N : ℕ) :
    pairedEtaCompletedLeadingLogCutoffCenteredShiftedCoupledMoment
        rho (analyticZetaZeroMultiplicity rho - 1) (N + 1) =
      ∫ u : ℝ,
        pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidualFiniteWorkTopPrefixCoupledIntegrand
          rho N u
        ∂pairedEtaShiftedLogTailMeasure (N + 1) := by
  unfold
    pairedEtaCompletedLeadingLogCutoffCenteredShiftedCoupledMoment
    pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidualFiniteWorkTopPrefixCoupledIntegrand
    pairedEtaShiftedLogTailFourierMoment
  rw [integral_add]
  · rw [integral_const_mul, integral_const_mul]
  · exact
      (integrable_pairedEtaShiftedLogTailFourierMoment_integrand
        (analyticZetaZeroMultiplicity rho - 1)
        (sub_pos.mpr (NontrivialZetaZero.re_lt_one rho))
        rho.1.im (N + 1)).const_mul
          (-pairedEtaCompletedLeadingLogCutoffCenteredShiftedPartnerCoefficient
            rho (N + 1))
  · exact
      (integrable_pairedEtaShiftedLogTailFourierMoment_integrand
        (analyticZetaZeroMultiplicity rho - 1)
        (NontrivialZetaZero.zero_lt_re rho) (-rho.1.im) (N + 1)).const_mul
          (pairedEtaCompletedLeadingLogCutoffCenteredShiftedConjugateCoefficient
            rho (N + 1))

/-- The top finite prefix is exactly a unit cutoff phase times one integral
over the shifted positive tail measure. -/
theorem
    pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidualFiniteWorkTopPrefix_eq_oscillation_mul_integral_coupledIntegrand
    (rho : NontrivialZetaZero) (N : ℕ) :
    pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidualFiniteWorkTopPrefix
        rho N =
      pairedEtaLogTailCutoffOscillation rho.1.im (N + 1) *
        ∫ u : ℝ,
          pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidualFiniteWorkTopPrefixCoupledIntegrand
            rho N u
          ∂pairedEtaShiftedLogTailMeasure (N + 1) := by
  have hk : analyticZetaZeroMultiplicity rho - 1 <
      analyticZetaZeroMultiplicity rho := by
    have hm : 0 < analyticZetaZeroMultiplicity rho :=
      analyticZetaZeroMultiplicity_positive rho
    omega
  have hprefix :=
    pairedEtaCompletedLeadingLogCutoffCenteredShiftedPhaseWeightedCoupledMoment_eq_finitePrefix_of_lt_multiplicity
      rho hk (N + 1)
  unfold
    pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidualFiniteWorkTopPrefix
  rw [← hprefix]
  unfold
    pairedEtaCompletedLeadingLogCutoffCenteredShiftedPhaseWeightedCoupledMoment
  rw [
    pairedEtaCompletedLeadingLogCutoffCenteredShiftedCoupledMoment_topOrderPred_eq_integral]

/-- The common critical-half-tilted integrand for the order-`m-1` top prefix.
The interference factor is exactly the one already used for the leading
residual; only the polynomial order changes. -/
def pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidualFiniteWorkTopPrefixHalfIntegrand
    (rho : NontrivialZetaZero) (N : ℕ) (u : ℝ) : ℂ :=
  (u : ℂ) ^ (analyticZetaZeroMultiplicity rho - 1) *
    (Real.exp (-(1 / 2) * u) : ℂ) *
    pairedEtaCompletedLeadingLogCutoffCenteredShiftedInterferenceFactor
      rho (N + 1) u

/-- Pointwise, the top-prefix coupled integrand is its critical-half form. -/
theorem
    pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidualFiniteWorkTopPrefixCoupledIntegrand_eq_halfIntegrand
    (rho : NontrivialZetaZero) (N : ℕ) (u : ℝ) :
    pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidualFiniteWorkTopPrefixCoupledIntegrand
        rho N u =
      pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidualFiniteWorkTopPrefixHalfIntegrand
        rho N u := by
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
  unfold
    pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidualFiniteWorkTopPrefixCoupledIntegrand
    pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidualFiniteWorkTopPrefixHalfIntegrand
    pairedEtaCompletedLeadingLogCutoffCenteredShiftedInterferenceFactor
  rw [hpartnerExp, hrhoExp]
  push_cast
  ring

/-- The half-centered top-prefix integrand is absolutely integrable. -/
theorem
    integrable_pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidualFiniteWorkTopPrefixHalfIntegrand
    (rho : NontrivialZetaZero) (N : ℕ) :
    Integrable
      (pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidualFiniteWorkTopPrefixHalfIntegrand
        rho N)
      (pairedEtaShiftedLogTailMeasure (N + 1)) := by
  apply
    (integrable_pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidualFiniteWorkTopPrefixCoupledIntegrand
      rho N).congr
  filter_upwards with u
  exact
    pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidualFiniteWorkTopPrefixCoupledIntegrand_eq_halfIntegrand
      rho N u

/-- The remaining finite prefix is a unit phase times its one-measure
critical-half interference integral. -/
theorem
    pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidualFiniteWorkTopPrefix_eq_oscillation_mul_integral_halfIntegrand
    (rho : NontrivialZetaZero) (N : ℕ) :
    pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidualFiniteWorkTopPrefix
        rho N =
      pairedEtaLogTailCutoffOscillation rho.1.im (N + 1) *
        ∫ u : ℝ,
          pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidualFiniteWorkTopPrefixHalfIntegrand
            rho N u
          ∂pairedEtaShiftedLogTailMeasure (N + 1) := by
  rw [
    pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidualFiniteWorkTopPrefix_eq_oscillation_mul_integral_coupledIntegrand]
  congr 1
  apply integral_congr_ae
  filter_upwards with u
  exact
    pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidualFiniteWorkTopPrefixCoupledIntegrand_eq_halfIntegrand
      rho N u

/-- Exact norm identity for the isolated square-root prefix frontier. -/
theorem
    norm_pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidualFiniteWorkTopPrefix_eq_integral_halfIntegrand
    (rho : NontrivialZetaZero) (N : ℕ) :
    ‖pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidualFiniteWorkTopPrefix
        rho N‖ =
      ‖∫ u : ℝ,
          pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidualFiniteWorkTopPrefixHalfIntegrand
            rho N u
          ∂pairedEtaShiftedLogTailMeasure (N + 1)‖ := by
  rw [
    pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidualFiniteWorkTopPrefix_eq_oscillation_mul_integral_halfIntegrand,
    norm_mul, norm_pairedEtaLogTailCutoffOscillation, one_mul]

/-- The direct positive-measure envelope for the top prefix.  This is the
triangle-inequality bound, so it deliberately discards the interference phase;
the missing square-root theorem cannot be inferred from this statement alone. -/
theorem
    norm_pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidualFiniteWorkTopPrefix_le_integral_norm_halfIntegrand
    (rho : NontrivialZetaZero) (N : ℕ) :
    ‖pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidualFiniteWorkTopPrefix
        rho N‖ ≤
      ∫ u : ℝ,
        ‖pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidualFiniteWorkTopPrefixHalfIntegrand
          rho N u‖
        ∂pairedEtaShiftedLogTailMeasure (N + 1) := by
  rw [
    norm_pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidualFiniteWorkTopPrefix_eq_integral_halfIntegrand]
  exact norm_integral_le_integral_norm _

end

end RiemannGaussian
