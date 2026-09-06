import RiemannGaussian.EtaMomentParityApproximation
import RiemannGaussian.EtaMomentPhysicalGeometry

/-!
# Completed moment phases at the actual moving divisor centers

The original moment divisor term is normalized by its literal physical
endpoint. Below the analytic zero multiplicity its leading phase is the
already proved zeroth-order parity column times an explicit factorial
coefficient. The complete error is uniform on the center intervals that
contain the original inverse centers.
-/

open Complex
open scoped Classical ComplexConjugate ArithmeticFunction.Moebius

namespace RiemannGaussian

noncomputable section

/-- The exact factor taking a zeroth-order parity column to moment order `k`. -/
def pairedEtaMomentParityCoefficient (rho : NontrivialZetaZero) (k : ℕ) : ℂ :=
  rho.1 * pairedEtaMomentEndpointCentralValue k rho.1

/-- The actual moment factor is the factorial divided by the full complex zero power. -/
theorem pairedEtaMomentParityCoefficient_eq (rho : NontrivialZetaZero) (k : ℕ) :
    pairedEtaMomentParityCoefficient rho k = (k.factorial : ℂ) / rho.1 ^ k := by
  rw [pairedEtaMomentParityCoefficient,
    pairedEtaMomentEndpointCentralValue_eq k (NontrivialZetaZero.coe_ne_zero rho), pow_succ]
  field_simp [NontrivialZetaZero.coe_ne_zero rho]

/-- At order zero the actual parity coefficient is exactly one. -/
theorem pairedEtaMomentParityCoefficient_zero (rho : NontrivialZetaZero) :
    pairedEtaMomentParityCoefficient rho 0 = 1 := by
  simp [pairedEtaMomentParityCoefficient_eq]

/-- The original completed moment term with its individual physical endpoint power. -/
def pairedEtaCompletedMomentEndpointPhase (rho : NontrivialZetaZero) (k : ℕ)
    (a : ℝ) (M d : ℕ) : ℂ :=
  ((d * pairedEtaUnpairedOddEndpoint (M / d) : ℕ) : ℂ) ^ rho.1 *
    pairedEtaCompletedMomentMoebiusTerm rho k a M d

/-- The exact complex divisor power cancels against its matching
endpoint power while keeping the complete translated moment prefix. -/
theorem pairedEtaCompletedMomentEndpointPhase_eq_prefix (rho : NontrivialZetaZero)
    (k : ℕ) (a : ℝ) (M : ℕ) {d : ℕ} (hd : 1 ≤ d) :
    pairedEtaCompletedMomentEndpointPhase rho k a M d =
      (μ d : ℂ) * (pairedEtaXiCompletionFactor rho.1 * rho.1) *
        ((pairedEtaUnpairedOddEndpoint (M / d) : ℂ) ^ rho.1 *
          pairedEtaUnpairedCenteredMomentPrefix k rho.1 (a - Real.log d) (M / d)) := by
  have hdne : (d : ℂ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hd)
  have hc : (d : ℂ) ^ rho.1 * (d : ℂ) ^ (-rho.1) = 1 := by
    rw [← Complex.cpow_add _ _ hdne, add_neg_cancel, Complex.cpow_zero]
  rw [pairedEtaCompletedMomentEndpointPhase, pairedEtaCompletedMomentMoebiusTerm,
    Nat.cast_mul, Complex.natCast_mul_natCast_cpow]
  linear_combination ((μ d : ℂ) * (pairedEtaXiCompletionFactor rho.1 * rho.1) *
    ((pairedEtaUnpairedOddEndpoint (M / d) : ℂ) ^ rho.1 *
      pairedEtaUnpairedCenteredMomentPrefix k rho.1 (a - Real.log d) (M / d))) * hc

/-- The completed moment phase error is exactly the original unpaired
moment error, with both Möbius and completion factors retained. -/
theorem pairedEtaCompletedMomentEndpointPhase_sub_parity (rho : NontrivialZetaZero)
    (k : ℕ) (a : ℝ) (M : ℕ) {d : ℕ} (hd : 1 ≤ d) :
    pairedEtaCompletedMomentEndpointPhase rho k a M d -
        pairedEtaMomentParityCoefficient rho k * pairedEtaCompletedMoebiusParityPhase rho M d =
      ((μ d : ℂ) * (pairedEtaXiCompletionFactor rho.1 * rho.1)) *
        ((pairedEtaUnpairedOddEndpoint (M / d) : ℂ) ^ rho.1 *
            pairedEtaUnpairedCenteredMomentPrefix k rho.1 (a - Real.log d) (M / d) -
          (pairedEtaDirichletSign (M / d) : ℂ) * pairedEtaMomentEndpointCentralValue k rho.1 / 2) := by
  rw [pairedEtaCompletedMomentEndpointPhase_eq_prefix rho k a M hd]
  unfold pairedEtaMomentParityCoefficient pairedEtaCompletedMoebiusParityPhase
  ring

/-- The explicit completion-dependent moment-phase error coefficient. -/
def pairedEtaCompletedMomentPhaseErrorConstant (rho : NontrivialZetaZero) (k : ℕ) : ℝ :=
  ‖pairedEtaXiCompletionFactor rho.1 * rho.1‖ *
    (2 * pairedEtaCenteredTailQuantitativeAsymptoticConstant k rho.1 +
      4 * (pairedEtaMomentCenterLowerBound rho k 4 + pairedEtaMomentEndpointVariation rho.1 k 4))

/-- The actual completed moment-phase error coefficient is nonnegative. -/
theorem pairedEtaCompletedMomentPhaseErrorConstant_nonneg (rho : NontrivialZetaZero) (k : ℕ) :
    0 ≤ pairedEtaCompletedMomentPhaseErrorConstant rho k := by
  have hC := pairedEtaCenteredTailQuantitativeAsymptoticConstant_nonneg rho k
  have hL := pairedEtaMomentCenterLowerBound_nonneg rho k (by norm_num : (0 : ℝ) ≤ 4)
  have hV := pairedEtaMomentEndpointVariation_nonneg rho.1 k (by norm_num : (0 : ℝ) ≤ 4)
  unfold pairedEtaCompletedMomentPhaseErrorConstant
  positivity

/-- Every original lower-moment divisor phase has the same literal
parity column as its main term, with an explicit `d/M` error valid at
all centers occurring in the original inverse reconstruction. -/
theorem norm_pairedEtaCompletedMomentEndpointPhase_sub_parity_le
    (rho : NontrivialZetaZero) {k M d : ℕ} (hk : k < analyticZetaZeroMultiplicity rho)
    (hd : d ∈ Finset.Icc 1 M) {a : ℝ}
    (ha : Real.log (M : ℝ) ≤ a ∧ a ≤ Real.log (M + 1 : ℝ)) :
    ‖pairedEtaCompletedMomentEndpointPhase rho k a M d -
        pairedEtaMomentParityCoefficient rho k * pairedEtaCompletedMoebiusParityPhase rho M d‖ ≤
      pairedEtaCompletedMomentPhaseErrorConstant rho k * d / M := by
  have hdp := (Finset.mem_Icc.mp hd).1
  have hM : 1 ≤ M := hdp.trans (Finset.mem_Icc.mp hd).2
  have hMR : (0 : ℝ) < M := by exact_mod_cast hM
  have hδ := abs_log_divisor_endpoint_sub_center_le hd ha
  have hδ4 : |Real.log (pairedEtaUnpairedOddEndpoint (M / d) : ℝ) - (a - Real.log d)| ≤ 4 := by
    apply hδ.trans
    apply (div_le_iff₀ hMR).mpr
    have hh : (d : ℝ) ≤ M := by exact_mod_cast (Finset.mem_Icc.mp hd).2
    nlinarith
  have hC := pairedEtaCenteredTailQuantitativeAsymptoticConstant_nonneg rho k
  have hB : 0 ≤ pairedEtaMomentCenterLowerBound rho k 4 + pairedEtaMomentEndpointVariation rho.1 k 4 :=
    add_nonneg (pairedEtaMomentCenterLowerBound_nonneg rho k (by norm_num))
      (pairedEtaMomentEndpointVariation_nonneg rho.1 k (by norm_num))
  have hraw := norm_pairedEtaUnpairedMoment_endpoint_sub_parity_le rho hk
    (a - Real.log d) (M / d) hδ4
  have hfirst := mul_le_mul_of_nonneg_left (inv_pairedEtaUnpairedOddEndpoint_div_le hM hdp) hC
  have hsecond := mul_le_mul_of_nonneg_left hδ hB
  have herr : ‖(pairedEtaUnpairedOddEndpoint (M / d) : ℂ) ^ rho.1 *
        pairedEtaUnpairedCenteredMomentPrefix k rho.1 (a - Real.log d) (M / d) -
      (pairedEtaDirichletSign (M / d) : ℂ) * pairedEtaMomentEndpointCentralValue k rho.1 / 2‖ ≤
      (2 * pairedEtaCenteredTailQuantitativeAsymptoticConstant k rho.1 +
        4 * (pairedEtaMomentCenterLowerBound rho k 4 + pairedEtaMomentEndpointVariation rho.1 k 4)) *
          (d : ℝ) / M := by
    apply hraw.trans
    have h := add_le_add hfirst hsecond
    simp only [mul_one_div] at h
    convert h using 1
    ring
  have hmu : ‖(μ d : ℂ)‖ ≤ 1 := by
    simpa only [Complex.norm_intCast] using
      (show (|μ d| : ℝ) ≤ 1 by exact_mod_cast (ArithmeticFunction.abs_moebius_le_one (n := d)))
  rw [pairedEtaCompletedMomentEndpointPhase_sub_parity rho k a M hdp, norm_mul, norm_mul]
  have h := mul_le_mul (mul_le_mul_of_nonneg_right hmu
    (norm_nonneg (pairedEtaXiCompletionFactor rho.1 * rho.1))) herr
    (norm_nonneg _) (by positivity : 0 ≤ 1 * ‖pairedEtaXiCompletionFactor rho.1 * rho.1‖)
  simpa only [one_mul, pairedEtaCompletedMomentPhaseErrorConstant, mul_div_assoc, mul_assoc] using h

end

end RiemannGaussian
