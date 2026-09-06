import RiemannGaussian.EtaMomentDivisorPhase

/-!
# Physical reduction of the original moment divisor terms

The original completed order-`k` term is compared with its explicit complex
multiple of the original zeroth-order term. Both individual endpoint powers
are removed through their exact common physical ratio. The error has one
divisor-over-cutoff factor throughout the full physical divisor range.
-/

open Complex
open scoped Classical ComplexConjugate

namespace RiemannGaussian

noncomputable section

/-- The exact moment-to-zeroth-order phase difference retains both
original parity errors before taking any norm. -/
theorem pairedEtaCompletedMomentEndpointPhase_sub_zero_eq
    (rho : NontrivialZetaZero) (k : ℕ) (a : ℝ) (M d : ℕ) :
    pairedEtaCompletedMomentEndpointPhase rho k a M d -
        pairedEtaMomentParityCoefficient rho k * pairedEtaCompletedMoebiusEndpointPhase rho M d =
      (pairedEtaCompletedMomentEndpointPhase rho k a M d -
        pairedEtaMomentParityCoefficient rho k * pairedEtaCompletedMoebiusParityPhase rho M d) -
      pairedEtaMomentParityCoefficient rho k *
        (pairedEtaCompletedMoebiusEndpointPhase rho M d - pairedEtaCompletedMoebiusParityPhase rho M d) := by
  ring

/-- The complete original term difference is the physical ratio times
the retained endpoint-phase difference, with its complex coefficient intact. -/
theorem pairedEtaCompletedMomentMoebiusTerm_physical_sub_zero
    (rho : NontrivialZetaZero) (k : ℕ) (a : ℝ) {M d : ℕ} (hd : d ∈ Finset.Icc 1 M) :
    (M : ℂ) ^ rho.1 * (pairedEtaCompletedMomentMoebiusTerm rho k a M d -
      pairedEtaMomentParityCoefficient rho k * pairedEtaCompletedMoebiusTerm rho M d) =
      pairedEtaMomentPhysicalRatio rho M d *
        (pairedEtaCompletedMomentEndpointPhase rho k a M d -
          pairedEtaMomentParityCoefficient rho k * pairedEtaCompletedMoebiusEndpointPhase rho M d) := by
  rw [← pairedEtaMomentPhysicalRatio_cancel rho hd]
  unfold pairedEtaCompletedMomentEndpointPhase pairedEtaCompletedMoebiusEndpointPhase
  ring

/-- The explicit common-physical-power error in the moment reduction. -/
def pairedEtaCompletedMomentPhysicalErrorConstant (rho : NontrivialZetaZero) (k : ℕ) : ℝ :=
  2 * (pairedEtaCompletedMomentPhaseErrorConstant rho k +
    2 * ‖pairedEtaMomentParityCoefficient rho k‖ * pairedEtaCompletedMoebiusPhaseErrorConstant rho)

/-- The complete moment reduction error coefficient is nonnegative. -/
theorem pairedEtaCompletedMomentPhysicalErrorConstant_nonneg (rho : NontrivialZetaZero) (k : ℕ) :
    0 ≤ pairedEtaCompletedMomentPhysicalErrorConstant rho k := by
  have hM := pairedEtaCompletedMomentPhaseErrorConstant_nonneg rho k
  have hZ := pairedEtaCompletedMoebiusPhaseErrorConstant_nonneg rho
  unfold pairedEtaCompletedMomentPhysicalErrorConstant
  positivity

/-- The original lower moment reduces to a full complex multiple of
the original zeroth-order term with an explicit physical `d/M` error,
uniform over the center interval containing every actual inverse center. -/
theorem norm_pairedEtaCompletedMomentMoebiusTerm_physical_sub_zero_le
    (rho : NontrivialZetaZero) {k M d : ℕ} (hk : k < analyticZetaZeroMultiplicity rho)
    (hd : d ∈ Finset.Icc 1 M) {a : ℝ}
    (ha : Real.log (M : ℝ) ≤ a ∧ a ≤ Real.log (M + 1 : ℝ)) :
    ‖(M : ℂ) ^ rho.1 * (pairedEtaCompletedMomentMoebiusTerm rho k a M d -
      pairedEtaMomentParityCoefficient rho k * pairedEtaCompletedMoebiusTerm rho M d)‖ ≤
      pairedEtaCompletedMomentPhysicalErrorConstant rho k * d / M := by
  have hdp := (Finset.mem_Icc.mp hd).1
  have hM : 1 ≤ M := hdp.trans (Finset.mem_Icc.mp hd).2
  have he : ‖pairedEtaCompletedMomentEndpointPhase rho k a M d -
      pairedEtaMomentParityCoefficient rho k * pairedEtaCompletedMoebiusEndpointPhase rho M d‖ ≤
      (pairedEtaCompletedMomentPhaseErrorConstant rho k +
        2 * ‖pairedEtaMomentParityCoefficient rho k‖ * pairedEtaCompletedMoebiusPhaseErrorConstant rho) *
          (d : ℝ) / M := by
    rw [pairedEtaCompletedMomentEndpointPhase_sub_zero_eq]
    apply (norm_sub_le _ _).trans
    rw [norm_mul]
    have hh := add_le_add (norm_pairedEtaCompletedMomentEndpointPhase_sub_parity_le rho hk hd ha)
      (mul_le_mul_of_nonneg_left
        (norm_pairedEtaCompletedMoebiusEndpointPhase_sub_parity_cutoff_le rho hM hdp)
        (norm_nonneg (pairedEtaMomentParityCoefficient rho k)))
    convert hh using 1
    ring
  rw [pairedEtaCompletedMomentMoebiusTerm_physical_sub_zero rho k a hd, norm_mul]
  have hh := mul_le_mul (norm_pairedEtaMomentPhysicalRatio_le rho hd) he (norm_nonneg _) (by norm_num)
  simpa only [pairedEtaCompletedMomentPhysicalErrorConstant, mul_div_assoc, mul_assoc] using hh

/-- The original nested inverse center discharges the center condition
for every physical inner divisor, without fixing it independently of the outer cutoff. -/
theorem norm_pairedEtaCompletedMomentMoebiusTerm_inverse_center_sub_zero_le
    (rho : NontrivialZetaZero) {k M d e : ℕ} (hk : k < analyticZetaZeroMultiplicity rho)
    (hd : d ∈ Finset.Icc 1 M) (he : e ∈ Finset.Icc 1 (M / d)) :
    ‖((M / d : ℕ) : ℂ) ^ rho.1 *
      (pairedEtaCompletedMomentMoebiusTerm rho k (Real.log (M + 1 : ℝ) - Real.log d) (M / d) e -
        pairedEtaMomentParityCoefficient rho k * pairedEtaCompletedMoebiusTerm rho (M / d) e)‖ ≤
      pairedEtaCompletedMomentPhysicalErrorConstant rho k * e / (M / d : ℕ) :=
  norm_pairedEtaCompletedMomentMoebiusTerm_physical_sub_zero_le rho hk he
    (pairedEtaMomentInverseCenter_mem_interval hd)

end

end RiemannGaussian
