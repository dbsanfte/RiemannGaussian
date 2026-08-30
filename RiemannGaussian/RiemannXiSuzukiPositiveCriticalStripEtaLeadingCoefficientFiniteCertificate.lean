import RiemannGaussian.RiemannXiSuzukiPositiveCriticalStripEtaCompletionReflectionQuantitativeRigidity
import RiemannGaussian.RiemannXiSuzukiPositiveCriticalStripEtaLeadingLogMomentFiniteLower

/-!
# Finite arithmetic certificates for complementary eta coefficients

The localized Gaussian leading coefficient is a positive universal
multiplicity factor times the squared norm of the first nonzero eta moment.
This module bounds its complementary-zero ratio using two eta-arithmetic
estimates which do not invoke completion symmetry:

* a phase-sensitive finite prefix minus its rigorous tail envelope gives a
  lower bound at `rho`; and
* the explicit first-gap envelope gives an upper bound at `1 - conj rho`.

Whenever the finite lower certificate is positive, their squared quotient is
therefore a certified upper bound for the complementary coefficient ratio.
At high ordinate and on the right of the critical line, quantitative
reflection rigidity turns this into an explicit upper bound on horizontal
zero displacement.

The certificate is not asserted to be close to one.  Establishing such a
uniform arithmetic estimate remains conjecture-strength work.
-/

open Complex Filter MeasureTheory Metric Set Topology
open scoped Classical ComplexConjugate ENNReal Interval Topology

namespace RiemannGaussian

noncomputable section

/-- The complementary leading-coefficient ratio is definitionally the square
of the corresponding raw eta-moment norm ratio.  This identity uses neither
the xi functional equation nor the completion multiplier. -/
theorem
    pairedEtaLocalizedGaussianLargeTimeLeadingCoefficient_conjugatePartner_div_eq_norm_defect_div_sq
    (rho : NontrivialZetaZero) :
    pairedEtaLocalizedGaussianLargeTimeLeadingCoefficient
          (NontrivialZetaZero.conjugatePartner rho) /
        pairedEtaLocalizedGaussianLargeTimeLeadingCoefficient rho =
      (‖pairedEtaLeadingLogGapMomentDefect
            (NontrivialZetaZero.conjugatePartner rho)‖ /
          ‖pairedEtaLeadingLogGapMomentDefect rho‖) ^ 2 := by
  rw [pairedEtaLeadingLogGapMomentDefect_eq_logLaplaceMoment,
    pairedEtaLeadingLogGapMomentDefect_eq_logLaplaceMoment]
  unfold pairedEtaLocalizedGaussianLargeTimeLeadingCoefficient
  simp only [analyticZetaZeroMultiplicity_conjugatePartner,
    Complex.normSq_eq_norm_sq]
  have hchoose :
      (((2 * analyticZetaZeroMultiplicity rho).choose
          (analyticZetaZeroMultiplicity rho) : ℕ) : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.choose_pos (by omega :
      analyticZetaZeroMultiplicity rho ≤
        2 * analyticZetaZeroMultiplicity rho)).ne'
  have hfactorial :
      ((analyticZetaZeroMultiplicity rho).factorial : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.factorial_pos
      (analyticZetaZeroMultiplicity rho)).ne'
  have hmoment :
      ‖pairedEtaLogLaplaceMoment
          (analyticZetaZeroMultiplicity rho) rho.1‖ ≠ 0 := by
    exact norm_ne_zero_iff.mpr
      (pairedEtaLogLaplaceMoment_multiplicity_ne_zero rho)
  field_simp [hchoose, hfactorial, hmoment]

/-- The explicit finite arithmetic upper certificate for the partner-to-
original leading-coefficient ratio. -/
def pairedEtaLeadingCoefficientRatioFiniteUpper
    (rho : NontrivialZetaZero) (theta : ℝ) (N : ℕ) : ℝ :=
  (pairedEtaLeadingLogGapMomentDefectUpper
        (analyticZetaZeroMultiplicity rho) (1 - rho.1.re) /
      pairedEtaLogLaplaceMomentFiniteLower
        (analyticZetaZeroMultiplicity rho) rho.1 theta N) ^ 2

/-- A positive phase-sensitive lower certificate at `rho` makes the finite
arithmetic quotient a valid upper bound for the exact complementary leading-
coefficient ratio. -/
theorem
    pairedEtaLocalizedGaussianLargeTimeLeadingCoefficient_conjugatePartner_div_le_finiteUpper
    (rho : NontrivialZetaZero) {theta : ℝ}
    (htheta : 0 < theta) (hthetaOne : theta < 1) (N : ℕ)
    (hlower : 0 < pairedEtaLogLaplaceMomentFiniteLower
      (analyticZetaZeroMultiplicity rho) rho.1 theta N) :
    pairedEtaLocalizedGaussianLargeTimeLeadingCoefficient
          (NontrivialZetaZero.conjugatePartner rho) /
        pairedEtaLocalizedGaussianLargeTimeLeadingCoefficient rho ≤
      pairedEtaLeadingCoefficientRatioFiniteUpper rho theta N := by
  rw [
    pairedEtaLocalizedGaussianLargeTimeLeadingCoefficient_conjugatePartner_div_eq_norm_defect_div_sq]
  have hlowerLe :
      pairedEtaLogLaplaceMomentFiniteLower
          (analyticZetaZeroMultiplicity rho) rho.1 theta N ≤
        ‖pairedEtaLeadingLogGapMomentDefect rho‖ :=
    pairedEtaLeadingLogGapMomentFiniteLower_le_norm_defect
      rho htheta hthetaOne N
  have hpartnerUpper :
      ‖pairedEtaLeadingLogGapMomentDefect
          (NontrivialZetaZero.conjugatePartner rho)‖ ≤
        pairedEtaLeadingLogGapMomentDefectUpper
          (analyticZetaZeroMultiplicity rho) (1 - rho.1.re) := by
    simpa [NontrivialZetaZero.conjugatePartner_coe] using
      norm_pairedEtaLeadingLogGapMomentDefect_le_upper
        (NontrivialZetaZero.conjugatePartner rho)
  have hpartnerUpperPos :
      0 < pairedEtaLeadingLogGapMomentDefectUpper
        (analyticZetaZeroMultiplicity rho) (1 - rho.1.re) := by
    simpa [NontrivialZetaZero.conjugatePartner_coe] using
      pairedEtaLeadingLogGapMomentDefectUpper_pos
        (NontrivialZetaZero.conjugatePartner rho)
  have hratio :
      ‖pairedEtaLeadingLogGapMomentDefect
            (NontrivialZetaZero.conjugatePartner rho)‖ /
          ‖pairedEtaLeadingLogGapMomentDefect rho‖ ≤
        pairedEtaLeadingLogGapMomentDefectUpper
              (analyticZetaZeroMultiplicity rho) (1 - rho.1.re) /
            pairedEtaLogLaplaceMomentFiniteLower
              (analyticZetaZeroMultiplicity rho) rho.1 theta N :=
    div_le_div₀ hpartnerUpperPos.le hpartnerUpper hlower hlowerLe
  have hratioNonneg :
      0 ≤ ‖pairedEtaLeadingLogGapMomentDefect
            (NontrivialZetaZero.conjugatePartner rho)‖ /
          ‖pairedEtaLeadingLogGapMomentDefect rho‖ := by positivity
  have hupperPos :
      0 < pairedEtaLeadingLogGapMomentDefectUpper
            (analyticZetaZeroMultiplicity rho) (1 - rho.1.re) /
          pairedEtaLogLaplaceMomentFiniteLower
            (analyticZetaZeroMultiplicity rho) rho.1 theta N := by
    exact div_pos hpartnerUpperPos hlower
  unfold pairedEtaLeadingCoefficientRatioFiniteUpper
  nlinarith

/-- For every admissible fixed tail split, the finite arithmetic ratio bounds
are eventually valid at every nontrivial zero.  Thus the positive-certificate
hypothesis in the pointwise theorem is not vacuous. -/
theorem
    eventually_pairedEtaLocalizedGaussianLargeTimeLeadingCoefficient_conjugatePartner_div_le_finiteUpper
    (rho : NontrivialZetaZero) {theta : ℝ}
    (htheta : 0 < theta) (hthetaOne : theta < 1) :
    ∀ᶠ N : ℕ in atTop,
      pairedEtaLocalizedGaussianLargeTimeLeadingCoefficient
            (NontrivialZetaZero.conjugatePartner rho) /
          pairedEtaLocalizedGaussianLargeTimeLeadingCoefficient rho ≤
        pairedEtaLeadingCoefficientRatioFiniteUpper rho theta N := by
  filter_upwards
    [eventually_pairedEtaLeadingLogGapMomentFiniteLower_pos
      rho htheta hthetaOne] with N hlower
  exact
    pairedEtaLocalizedGaussianLargeTimeLeadingCoefficient_conjugatePartner_div_le_finiteUpper
      rho htheta hthetaOne N hlower

/-- At high ordinate on or to the right of the critical line, any positive
finite eta certificate gives a fully explicit upper bound on horizontal zero
displacement through the logarithm of its ratio bound. -/
theorem re_sub_half_le_100_mul_realLog_finiteUpper_of_eight_le_abs_im
    (rho : NontrivialZetaZero) {theta : ℝ}
    (htheta : 0 < theta) (hthetaOne : theta < 1) (N : ℕ)
    (hlower : 0 < pairedEtaLogLaplaceMomentFiniteLower
      (analyticZetaZeroMultiplicity rho) rho.1 theta N)
    (hhalf : 1 / 2 ≤ rho.1.re) (hy : 8 ≤ |rho.1.im|) :
    rho.1.re - 1 / 2 ≤
      100 * Real.log (pairedEtaLeadingCoefficientRatioFiniteUpper rho theta N) := by
  have hcoercive :=
    one_over_100_mul_abs_re_sub_half_le_abs_realLog_leadingCoefficient_ratio_of_eight_le_abs_im
      rho hy
  have hratioPos :
      0 < pairedEtaLocalizedGaussianLargeTimeLeadingCoefficient
            (NontrivialZetaZero.conjugatePartner rho) /
          pairedEtaLocalizedGaussianLargeTimeLeadingCoefficient rho :=
    div_pos
      (pairedEtaLocalizedGaussianLargeTimeLeadingCoefficient_pos _)
      (pairedEtaLocalizedGaussianLargeTimeLeadingCoefficient_pos rho)
  have hratioUpper :=
    pairedEtaLocalizedGaussianLargeTimeLeadingCoefficient_conjugatePartner_div_le_finiteUpper
      rho htheta hthetaOne N hlower
  have hlogUpper :
      Real.log
          (pairedEtaLocalizedGaussianLargeTimeLeadingCoefficient
                (NontrivialZetaZero.conjugatePartner rho) /
              pairedEtaLocalizedGaussianLargeTimeLeadingCoefficient rho) ≤
        Real.log (pairedEtaLeadingCoefficientRatioFiniteUpper rho theta N) :=
    Real.log_le_log hratioPos hratioUpper
  have hlogNonneg :
      0 ≤ Real.log
        (pairedEtaLocalizedGaussianLargeTimeLeadingCoefficient
              (NontrivialZetaZero.conjugatePartner rho) /
            pairedEtaLocalizedGaussianLargeTimeLeadingCoefficient rho) := by
    rw [
      realLog_pairedEtaLocalizedGaussianLargeTimeLeadingCoefficient_conjugatePartner_div_eq_two_mul_reflectionLogNorm]
    rcases hhalf.eq_or_lt with hline | hright
    · rw [← hline, pairedEtaLaplaceReflectionLogNorm_half]
      norm_num
    · exact mul_nonneg (by norm_num)
        (pairedEtaLaplaceReflectionLogNorm_pos_of_half_lt_of_eight_le_abs
          hright (NontrivialZetaZero.re_lt_one rho) hy).le
  rw [abs_of_nonneg (sub_nonneg.mpr hhalf), abs_of_nonneg hlogNonneg] at hcoercive
  nlinarith

/-- Under the explicit high-ordinate and right-half-strip hypotheses, every
fixed admissible tail split eventually yields a certified arithmetic upper
bound on horizontal zero displacement. -/
theorem eventually_re_sub_half_le_100_mul_realLog_finiteUpper_of_eight_le_abs_im
    (rho : NontrivialZetaZero) {theta : ℝ}
    (htheta : 0 < theta) (hthetaOne : theta < 1)
    (hhalf : 1 / 2 ≤ rho.1.re) (hy : 8 ≤ |rho.1.im|) :
    ∀ᶠ N : ℕ in atTop,
      rho.1.re - 1 / 2 ≤
        100 * Real.log
          (pairedEtaLeadingCoefficientRatioFiniteUpper rho theta N) := by
  filter_upwards
    [eventually_pairedEtaLeadingLogGapMomentFiniteLower_pos
      rho htheta hthetaOne] with N hlower
  exact re_sub_half_le_100_mul_realLog_finiteUpper_of_eight_le_abs_im
    rho htheta hthetaOne N hlower hhalf hy

end
end RiemannGaussian
