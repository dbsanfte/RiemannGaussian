import RiemannGaussian.EtaCurrentHalfStepPairs

/-!
# Positive principal endpoint coefficients for the actual completed current

Both actual multiplicity branches have one common signed principal term:
the logarithmic step times the difference of two positive completion
coefficients with complementary horizontal decay rates. The original
current and linear-width Gaussian return differ from it by proved summable
odd-weighted errors. This does not bound the principal term itself.
-/

open Complex Filter MeasureTheory Set Topology
open scoped Classical ComplexConjugate ENNReal Interval Topology

namespace RiemannGaussian

noncomputable section

/-- The actual multiplicity chooses the positive coefficient of one
principal completed endpoint channel. -/
def pairedEtaCurrentPrincipalCoefficient (rho : NontrivialZetaZero) : ℝ :=
  if analyticZetaZeroMultiplicity rho = 1 then pairedEtaCurrentSimpleEndpointCoefficient rho
  else 2 * ((analyticZetaZeroMultiplicity rho - 1 : ℕ) : ℝ) *
    pairedEtaCurrentEulerAdjacentCoefficient rho (analyticZetaZeroMultiplicity rho - 2)

/-- Neither multiplicity branch loses the strictly positive actual
completion coefficient. -/
theorem pairedEtaCurrentPrincipalCoefficient_pos (rho : NontrivialZetaZero) :
    0 < pairedEtaCurrentPrincipalCoefficient rho := by
  unfold pairedEtaCurrentPrincipalCoefficient
  split
  · exact pairedEtaCurrentSimpleEndpointCoefficient_pos rho
  · rename_i hm
    have hm2 : 2 ≤ analyticZetaZeroMultiplicity rho := by
      have := analyticZetaZeroMultiplicity_positive rho
      omega
    have hsub : (0 : ℝ) < ((analyticZetaZeroMultiplicity rho - 1 : ℕ) : ℝ) := by
      exact_mod_cast (show 0 < analyticZetaZeroMultiplicity rho - 1 by omega)
    exact mul_pos (mul_pos (by norm_num) hsub) (pairedEtaCurrentEulerAdjacentCoefficient_pos rho _)

/-- The common principal endpoint expression, with the signed completion
channels, actual logarithmic step, and cutoff all retained. -/
def pairedEtaCurrentPrincipalEndpoint (rho : NontrivialZetaZero) (N : ℕ) : ℝ :=
  pairedEtaLogTailShiftIncrement (N + 1) *
    (pairedEtaCurrentPrincipalCoefficient (NontrivialZetaZero.conjugatePartner rho) *
        Real.exp (-2 * (NontrivialZetaZero.conjugatePartner rho).1.re * pairedEtaLogTailCutoff (N + 2)) -
      pairedEtaCurrentPrincipalCoefficient rho * Real.exp (-2 * rho.1.re * pairedEtaLogTailCutoff (N + 2)))

/-- The two principal rates are exactly the complementary actual zero
coordinates; there is no remaining cutoff Fourier phase in this expression. -/
theorem pairedEtaCurrentPrincipalEndpoint_eq_complementary (rho : NontrivialZetaZero) (N : ℕ) :
    pairedEtaCurrentPrincipalEndpoint rho N = pairedEtaLogTailShiftIncrement (N + 1) *
      (pairedEtaCurrentPrincipalCoefficient (NontrivialZetaZero.conjugatePartner rho) *
          Real.exp (-2 * (1 - rho.1.re) * pairedEtaLogTailCutoff (N + 2)) -
        pairedEtaCurrentPrincipalCoefficient rho * Real.exp (-2 * rho.1.re * pairedEtaLogTailCutoff (N + 2))) := by
  simp only [pairedEtaCurrentPrincipalEndpoint, NontrivialZetaZero.conjugatePartner_coe,
    Complex.sub_re, Complex.one_re, Complex.conj_re]

/-- At a simple zero the principal term is exactly the signed half-step
head pair whose complex defect was estimated upstream. -/
theorem pairedEtaCurrentPrincipalEndpoint_eq_halfStep (rho : NontrivialZetaZero)
    (hm : analyticZetaZeroMultiplicity rho = 1) (N : ℕ) :
    pairedEtaCurrentPrincipalEndpoint rho N = 2 * (pairedEtaCurrentHalfStepHeadPair rho N).re := by
  rw [pairedEtaCurrentHalfStepHeadPair_re]
  simp only [pairedEtaCurrentPrincipalEndpoint, pairedEtaCurrentPrincipalCoefficient,
    analyticZetaZeroMultiplicity_conjugatePartner, hm, if_true]

/-- At a repeated zero no further approximation is needed: the actual
Euler expression already equals the common principal endpoint term. -/
theorem pairedEtaCurrentEulerExpression_eq_principal_of_multiple (rho : NontrivialZetaZero)
    (hm : 2 ≤ analyticZetaZeroMultiplicity rho) (N : ℕ) :
    pairedEtaCurrentEulerExpression rho N = pairedEtaCurrentPrincipalEndpoint rho N := by
  have hm1 : analyticZetaZeroMultiplicity rho ≠ 1 := by omega
  rw [pairedEtaCurrentEulerExpression_eq_adjacent_endpoints rho hm N]
  simp only [pairedEtaCurrentPrincipalEndpoint, pairedEtaCurrentPrincipalCoefficient,
    analyticZetaZeroMultiplicity_conjugatePartner, if_neg hm1]
  ring

/-- The Euler expression has only the summable head correction left
before the common principal term, in both actual multiplicity branches. -/
theorem pairedEtaCurrentEulerExpression_weighted_principal_error_le (rho : NontrivialZetaZero) (N : ℕ) :
    (2 * N + 1 : ℝ) * |pairedEtaCurrentEulerExpression rho N - pairedEtaCurrentPrincipalEndpoint rho N| ≤
      4 * pairedEtaCurrentHalfStepErrorEnvelope rho N := by
  by_cases hm : analyticZetaZeroMultiplicity rho = 1
  · rw [pairedEtaCurrentEulerExpression, if_pos hm, pairedEtaCurrentPrincipalEndpoint_eq_halfStep rho hm N]
    exact pairedEtaCurrentEulerHeadPair_weighted_halfStep_error_le rho N
  · have hm2 : 2 ≤ analyticZetaZeroMultiplicity rho := by
      have := analyticZetaZeroMultiplicity_positive rho
      omega
    rw [pairedEtaCurrentEulerExpression_eq_principal_of_multiple rho hm2 N, sub_self, abs_zero, mul_zero]
    exact mul_nonneg (by norm_num) (pairedEtaCurrentHalfStepErrorEnvelope_nonneg rho N)

/-- The unchanged original real current has a summable weighted
arithmetic error from the positive-coefficient principal endpoint term. -/
theorem pairedEtaLeadingCurrent_weighted_principal_error_le (rho : NontrivialZetaZero) (N : ℕ) :
    (2 * N + 1 : ℝ) * |pairedEtaTopPrefixFiniteEnergyLeadingFlux rho N - pairedEtaCurrentPrincipalEndpoint rho N| ≤
      4 * pairedEtaCurrentEulerErrorEnvelope rho N + 4 * pairedEtaCurrentHalfStepErrorEnvelope rho N := by
  have h := mul_le_mul_of_nonneg_left
    (abs_sub_le (pairedEtaTopPrefixFiniteEnergyLeadingFlux rho N) (pairedEtaCurrentEulerExpression rho N)
      (pairedEtaCurrentPrincipalEndpoint rho N)) (by positivity : (0 : ℝ) ≤ 2 * N + 1)
  rw [mul_add] at h
  exact h.trans (add_le_add (pairedEtaLeadingCurrent_weighted_euler_error_le rho N)
    (pairedEtaCurrentEulerExpression_weighted_principal_error_le rho N))

/-- The original current's full weighted principal-term error is summable. -/
theorem summable_oddEndpoint_mul_abs_pairedEtaLeadingCurrent_principal_error (rho : NontrivialZetaZero) :
    Summable (fun N : ℕ ↦ (2 * N + 1 : ℝ) *
      |pairedEtaTopPrefixFiniteEnergyLeadingFlux rho N - pairedEtaCurrentPrincipalEndpoint rho N|) :=
  (((summable_pairedEtaCurrentEulerErrorEnvelope rho).mul_left 4).add
    ((summable_pairedEtaCurrentHalfStepErrorEnvelope rho).mul_left 4)).of_nonneg_of_le
      (fun N ↦ by positivity) (pairedEtaLeadingCurrent_weighted_principal_error_le rho)

/-- The explicit majorant includes all heat, Euler, and half-step errors
for the actual linear-width return. -/
def pairedEtaCurrentPrincipalErrorMajorant (rho : NontrivialZetaZero) (N : ℕ) : ℝ :=
  pairedEtaCurrentLinearHeatErrorMajorant rho N + 4 * pairedEtaCurrentEulerErrorEnvelope rho N +
    4 * pairedEtaCurrentHalfStepErrorEnvelope rho N

/-- The complete error majorant is nonnegative at every cutoff. -/
theorem pairedEtaCurrentPrincipalErrorMajorant_nonneg (rho : NontrivialZetaZero) (N : ℕ) :
    0 ≤ pairedEtaCurrentPrincipalErrorMajorant rho N :=
  add_nonneg (add_nonneg (pairedEtaCurrentLinearHeatErrorMajorant_nonneg rho N)
    (mul_nonneg (by norm_num) (pairedEtaCurrentEulerErrorEnvelope_nonneg rho N)))
      (mul_nonneg (by norm_num) (pairedEtaCurrentHalfStepErrorEnvelope_nonneg rho N))

/-- The majorant is genuinely summable, so its total is a finite error
budget rather than a totalized divergent series. -/
theorem summable_pairedEtaCurrentPrincipalErrorMajorant (rho : NontrivialZetaZero) :
    Summable (pairedEtaCurrentPrincipalErrorMajorant rho) :=
  ((summable_pairedEtaCurrentLinearHeatErrorMajorant rho).add
    ((summable_pairedEtaCurrentEulerErrorEnvelope rho).mul_left 4)).add
      ((summable_pairedEtaCurrentHalfStepErrorEnvelope rho).mul_left 4)

/-- The actual complex Gaussian return differs from the common signed
principal term by the explicit odd-weighted summable majorant. -/
theorem pairedEtaLeadingCurrentLinearHeatReturn_weighted_principal_error_le (rho : NontrivialZetaZero) (N : ℕ) :
    (2 * N + 1 : ℝ) * ‖pairedEtaLeadingCurrentLinearHeatReturn rho N - (pairedEtaCurrentPrincipalEndpoint rho N : ℂ)‖ ≤
      pairedEtaCurrentPrincipalErrorMajorant rho N := by
  have ht := norm_sub_le_norm_sub_add_norm_sub (pairedEtaLeadingCurrentLinearHeatReturn rho N)
    (pairedEtaCurrentEulerExpression rho N : ℂ) (pairedEtaCurrentPrincipalEndpoint rho N : ℂ)
  have h := mul_le_mul_of_nonneg_left ht (by positivity : (0 : ℝ) ≤ 2 * N + 1)
  rw [mul_add] at h
  simp only [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs] at h
  exact h.trans (add_le_add (pairedEtaLeadingCurrentLinearHeatReturn_weighted_euler_error_le rho N)
    (pairedEtaCurrentEulerExpression_weighted_principal_error_le rho N))

/-- The full weighted norm error of the original linear-width return
from its signed principal endpoint term is absolutely summable. -/
theorem summable_oddEndpoint_mul_norm_pairedEtaLeadingCurrentLinearHeatReturn_principal_error (rho : NontrivialZetaZero) :
    Summable (fun N : ℕ ↦ (2 * N + 1 : ℝ) *
      ‖pairedEtaLeadingCurrentLinearHeatReturn rho N - (pairedEtaCurrentPrincipalEndpoint rho N : ℂ)‖) :=
  (summable_pairedEtaCurrentPrincipalErrorMajorant rho).of_nonneg_of_le
    (fun N ↦ by positivity) (pairedEtaLeadingCurrentLinearHeatReturn_weighted_principal_error_le rho)

/-- One finite explicit budget bounds every partial weighted return error. -/
theorem pairedEtaLeadingCurrentLinearHeatReturn_principal_error_sum_le (rho : NontrivialZetaZero) (K : ℕ) :
    (∑ N ∈ Finset.range K, (2 * N + 1 : ℝ) *
      ‖pairedEtaLeadingCurrentLinearHeatReturn rho N - (pairedEtaCurrentPrincipalEndpoint rho N : ℂ)‖) ≤
        ∑' N : ℕ, pairedEtaCurrentPrincipalErrorMajorant rho N := by
  calc
    _ ≤ ∑ N ∈ Finset.range K, pairedEtaCurrentPrincipalErrorMajorant rho N :=
      Finset.sum_le_sum (fun N _ ↦ pairedEtaLeadingCurrentLinearHeatReturn_weighted_principal_error_le rho N)
    _ ≤ _ := (summable_pairedEtaCurrentPrincipalErrorMajorant rho).sum_le_tsum _
      (fun N _ ↦ pairedEtaCurrentPrincipalErrorMajorant_nonneg rho N)

/-- The actual return and the explicit positive-coefficient endpoint
expression have first absolute moments differing by a fixed finite budget.
Neither moment is asserted to be bounded independently of cutoff. -/
theorem pairedEtaLeadingCurrentLinearHeatReturn_principal_firstMoment_stability (rho : NontrivialZetaZero) (K : ℕ) :
    |(∑ N ∈ Finset.range K, (2 * N + 1 : ℝ) * ‖pairedEtaLeadingCurrentLinearHeatReturn rho N‖) -
      (∑ N ∈ Finset.range K, (2 * N + 1 : ℝ) * |pairedEtaCurrentPrincipalEndpoint rho N|)| ≤
        ∑' N : ℕ, pairedEtaCurrentPrincipalErrorMajorant rho N := by
  calc
    _ = |∑ N ∈ Finset.range K, ((2 * N + 1 : ℝ) * ‖pairedEtaLeadingCurrentLinearHeatReturn rho N‖ -
        (2 * N + 1 : ℝ) * |pairedEtaCurrentPrincipalEndpoint rho N|)| := by rw [Finset.sum_sub_distrib]
    _ ≤ ∑ N ∈ Finset.range K, |(2 * N + 1 : ℝ) * ‖pairedEtaLeadingCurrentLinearHeatReturn rho N‖ -
        (2 * N + 1 : ℝ) * (|pairedEtaCurrentPrincipalEndpoint rho N|)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ N ∈ Finset.range K, (2 * N + 1 : ℝ) * ‖pairedEtaLeadingCurrentLinearHeatReturn rho N -
        (pairedEtaCurrentPrincipalEndpoint rho N : ℂ)‖ := by
      apply Finset.sum_le_sum
      intro N _
      have hw : (0 : ℝ) ≤ 2 * N + 1 := by positivity
      rw [← mul_sub, abs_mul, abs_of_nonneg hw]
      apply mul_le_mul_of_nonneg_left _ hw
      simpa only [Complex.norm_real, Real.norm_eq_abs] using
        abs_norm_sub_norm_le (pairedEtaLeadingCurrentLinearHeatReturn rho N) (pairedEtaCurrentPrincipalEndpoint rho N : ℂ)
    _ ≤ _ := pairedEtaLeadingCurrentLinearHeatReturn_principal_error_sum_le rho K

end

end RiemannGaussian
