import RiemannGaussian.EtaMoebiusQuadratic

/-!
# The exact endpoint phase of each completed Möbius eta term

The original divisor term is multiplied by its literal complex odd-endpoint
power. Its leading term is the original parity sign, with the completion
factor and Möbius coefficient retained. The error is the genuine Euler gap
error, and an explicit inverse-cutoff bound keeps the divisor dependence.
-/

open Complex Filter MeasureTheory Set Topology
open scoped Classical ComplexConjugate ENNReal Interval Topology ArithmeticFunction.Moebius

namespace RiemannGaussian

noncomputable section

/-- The first odd endpoint of the paired prefix inside an arbitrary
unpaired integer cutoff. -/
def pairedEtaUnpairedOddEndpoint (m : ℕ) : ℕ := 2 * (m / 2) + 1

/-- The odd endpoint is positive and lies at or one past the unpaired cutoff. -/
theorem pairedEtaUnpairedOddEndpoint_bounds (m : ℕ) :
    1 ≤ pairedEtaUnpairedOddEndpoint m ∧ m ≤ pairedEtaUnpairedOddEndpoint m ∧
      pairedEtaUnpairedOddEndpoint m ≤ m + 1 := by
  unfold pairedEtaUnpairedOddEndpoint
  omega

/-- The original eta coefficient always has unit absolute value. -/
theorem abs_pairedEtaDirichletSign (m : ℕ) : |pairedEtaDirichletSign m| = 1 := by
  unfold pairedEtaDirichletSign
  split_ifs <;> norm_num

/-- At an actual zero the complete complex phase error is exactly the
negative normalized Euler gap error. The odd unpaired term is included. -/
theorem pairedEtaUnpairedDirichletPrefix_endpoint_phase_error (rho : NontrivialZetaZero) (m : ℕ) :
    (pairedEtaUnpairedOddEndpoint m : ℂ) ^ rho.1 * pairedEtaUnpairedDirichletPrefix m rho.1 -
      (pairedEtaDirichletSign m : ℂ) / 2 =
        -(pairedEtaGapNormalizedFiniteError (m / 2) rho.1 + 1 / 2) := by
  have hq : (pairedEtaUnpairedOddEndpoint m : ℂ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt (pairedEtaUnpairedOddEndpoint_bounds m).1)
  have hcancel : (pairedEtaUnpairedOddEndpoint m : ℂ) ^ rho.1 *
      (pairedEtaUnpairedOddEndpoint m : ℂ) ^ (-rho.1) = 1 := by
    rw [← Complex.cpow_add _ _ hq, add_neg_cancel, Complex.cpow_zero]
  rw [pairedEtaUnpairedDirichletPrefix_eq_paired_add_endpoint]
  unfold pairedEtaGapNormalizedFiniteError
  rw [pairedEtaGapCore_eq_one_of_nontrivialZetaZero rho, pairedEtaGapCorePartialSum_sub_one_eq]
  change (pairedEtaUnpairedOddEndpoint m : ℂ) ^ rho.1 *
      (pairedEtaCorePartialSum (m / 2) rho.1 + if Odd m then (m : ℂ) ^ (-rho.1) else 0) -
        (pairedEtaDirichletSign m : ℂ) / 2 =
      -((pairedEtaUnpairedOddEndpoint m : ℂ) ^ rho.1 *
        (-pairedEtaCorePartialSum (m / 2) rho.1 - (pairedEtaUnpairedOddEndpoint m : ℂ) ^ (-rho.1)) + 1 / 2)
  by_cases hm : Odd m
  · have hqm : pairedEtaUnpairedOddEndpoint m = m := by
      have := Nat.odd_iff.mp hm
      unfold pairedEtaUnpairedOddEndpoint
      omega
    have he : ¬ Even m := by simpa only [Nat.not_even_iff_odd] using hm
    rw [if_pos hm, pairedEtaDirichletSign, if_neg he]
    have hmPow : (m : ℂ) ^ (-rho.1) = (pairedEtaUnpairedOddEndpoint m : ℂ) ^ (-rho.1) :=
      congrArg (fun n : ℕ ↦ (n : ℂ) ^ (-rho.1)) hqm.symm
    rw [hmPow]
    push_cast
    ring
  · have he : Even m := Nat.not_odd_iff_even.mp hm
    rw [if_neg hm, pairedEtaDirichletSign, if_pos he]
    push_cast
    linear_combination -hcancel

/-- The exact endpoint phase error has the original explicit Euler rate. -/
theorem norm_pairedEtaUnpairedDirichletPrefix_endpoint_phase_error_le
    (rho : NontrivialZetaZero) (m : ℕ) :
    ‖(pairedEtaUnpairedOddEndpoint m : ℂ) ^ rho.1 * pairedEtaUnpairedDirichletPrefix m rho.1 -
      (pairedEtaDirichletSign m : ℂ) / 2‖ ≤
        ‖rho.1‖ * ‖rho.1 + 1‖ / (pairedEtaUnpairedOddEndpoint m : ℝ) := by
  rw [pairedEtaUnpairedDirichletPrefix_endpoint_phase_error, norm_neg]
  simpa only [pairedEtaUnpairedOddEndpoint, Real.rpow_neg_one, div_eq_mul_inv] using
    norm_pairedEtaGapNormalizedFiniteError_add_half_le (NontrivialZetaZero.zero_lt_re rho) (m / 2)

/-- The actual completed Möbius term normalized by its own literal
divisor times odd endpoint, with the entire complex power retained. -/
def pairedEtaCompletedMoebiusEndpointPhase (rho : NontrivialZetaZero) (M d : ℕ) : ℂ :=
  ((d * pairedEtaUnpairedOddEndpoint (M / d) : ℕ) : ℂ) ^ rho.1 * pairedEtaCompletedMoebiusTerm rho M d

/-- The signed leading phase retains the original completion and both
arithmetic signs. -/
def pairedEtaCompletedMoebiusParityPhase (rho : NontrivialZetaZero) (M d : ℕ) : ℂ :=
  (μ d : ℂ) * pairedEtaXiCompletionFactor rho.1 * (pairedEtaDirichletSign (M / d) : ℂ) / 2

/-- The actual complex divisor power cancels only against the matching
part of its physical endpoint power. -/
theorem pairedEtaCompletedMoebiusEndpointPhase_eq_prefix (rho : NontrivialZetaZero)
    (M : ℕ) {d : ℕ} (hd : 1 ≤ d) :
    pairedEtaCompletedMoebiusEndpointPhase rho M d =
      (μ d : ℂ) * pairedEtaXiCompletionFactor rho.1 *
        ((pairedEtaUnpairedOddEndpoint (M / d) : ℂ) ^ rho.1 *
          pairedEtaUnpairedDirichletPrefix (M / d) rho.1) := by
  have hdne : (d : ℂ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hd)
  have hcancel : (d : ℂ) ^ rho.1 * (d : ℂ) ^ (-rho.1) = 1 := by
    rw [← Complex.cpow_add _ _ hdne, add_neg_cancel, Complex.cpow_zero]
  rw [pairedEtaCompletedMoebiusEndpointPhase, Nat.cast_mul, Complex.natCast_mul_natCast_cpow,
    pairedEtaCompletedMoebiusTerm_eq_completed_prefix]
  linear_combination (pairedEtaUnpairedOddEndpoint (M / d) : ℂ) ^ rho.1 *
    ((μ d : ℂ) * pairedEtaXiCompletionFactor rho.1 * pairedEtaUnpairedDirichletPrefix (M / d) rho.1) * hcancel

/-- The error coefficient includes the completion and the original Euler
constant, and is independent of both divisor and cutoff. -/
def pairedEtaCompletedMoebiusPhaseErrorConstant (rho : NontrivialZetaZero) : ℝ :=
  ‖pairedEtaXiCompletionFactor rho.1‖ * ‖rho.1‖ * ‖rho.1 + 1‖

/-- The actual phase-error coefficient is nonnegative. -/
theorem pairedEtaCompletedMoebiusPhaseErrorConstant_nonneg (rho : NontrivialZetaZero) :
    0 ≤ pairedEtaCompletedMoebiusPhaseErrorConstant rho := by
  unfold pairedEtaCompletedMoebiusPhaseErrorConstant
  positivity

/-- The retained complex normalization has one inverse odd-endpoint
error, with no loss of the actual completion or parity phase. -/
theorem norm_pairedEtaCompletedMoebiusEndpointPhase_sub_parity_le
    (rho : NontrivialZetaZero) (M : ℕ) {d : ℕ} (hd : 1 ≤ d) :
    ‖pairedEtaCompletedMoebiusEndpointPhase rho M d - pairedEtaCompletedMoebiusParityPhase rho M d‖ ≤
      pairedEtaCompletedMoebiusPhaseErrorConstant rho / (pairedEtaUnpairedOddEndpoint (M / d) : ℝ) := by
  have hmu : ‖(μ d : ℂ)‖ ≤ 1 := by
    simpa only [Complex.norm_intCast] using
      (show (|μ d| : ℝ) ≤ 1 by exact_mod_cast (ArithmeticFunction.abs_moebius_le_one (n := d)))
  rw [pairedEtaCompletedMoebiusEndpointPhase_eq_prefix rho M hd]
  unfold pairedEtaCompletedMoebiusParityPhase
  rw [show (μ d : ℂ) * pairedEtaXiCompletionFactor rho.1 *
      (pairedEtaDirichletSign (M / d) : ℂ) / 2 =
      ((μ d : ℂ) * pairedEtaXiCompletionFactor rho.1) * ((pairedEtaDirichletSign (M / d) : ℂ) / 2) by ring,
    ← mul_sub, norm_mul, norm_mul]
  calc
    _ ≤ (1 * ‖pairedEtaXiCompletionFactor rho.1‖) *
        (‖rho.1‖ * ‖rho.1 + 1‖ / (pairedEtaUnpairedOddEndpoint (M / d) : ℝ)) :=
      mul_le_mul (mul_le_mul_of_nonneg_right hmu (norm_nonneg _))
        (norm_pairedEtaUnpairedDirichletPrefix_endpoint_phase_error_le rho (M / d))
        (norm_nonneg _) (by positivity)
    _ = _ := by unfold pairedEtaCompletedMoebiusPhaseErrorConstant; ring

/-- The literal divided odd endpoint controls its inverse at the original
cutoff, with the divisor dependence explicit even when the divisor is large. -/
theorem inv_pairedEtaUnpairedOddEndpoint_div_le {M d : ℕ} (hM : 1 ≤ M) (hd : 1 ≤ d) :
    1 / (pairedEtaUnpairedOddEndpoint (M / d) : ℝ) ≤ 2 * (d : ℝ) / M := by
  have hq := pairedEtaUnpairedOddEndpoint_bounds (M / d)
  have hsplit := Nat.div_add_mod M d
  have hr := Nat.mod_lt M hd
  have hnat : M ≤ 2 * d * pairedEtaUnpairedOddEndpoint (M / d) := by nlinarith
  have hMR : (0 : ℝ) < M := by exact_mod_cast hM
  have hqR : (0 : ℝ) < pairedEtaUnpairedOddEndpoint (M / d) := by exact_mod_cast hq.1
  apply (div_le_div_iff₀ hqR hMR).2
  simpa only [one_mul] using (show (M : ℝ) ≤ 2 * (d : ℝ) * pairedEtaUnpairedOddEndpoint (M / d) by
    exact_mod_cast hnat)

/-- The completed phase approximation has an explicit bound at the
original cutoff. Its linear dependence on the divisor cannot be omitted
when a later argument allows the matrix dimension to grow. -/
theorem norm_pairedEtaCompletedMoebiusEndpointPhase_sub_parity_cutoff_le
    (rho : NontrivialZetaZero) {M d : ℕ} (hM : 1 ≤ M) (hd : 1 ≤ d) :
    ‖pairedEtaCompletedMoebiusEndpointPhase rho M d - pairedEtaCompletedMoebiusParityPhase rho M d‖ ≤
      2 * pairedEtaCompletedMoebiusPhaseErrorConstant rho * d / M := by
  apply (norm_pairedEtaCompletedMoebiusEndpointPhase_sub_parity_le rho M hd).trans
  have h := mul_le_mul_of_nonneg_left (inv_pairedEtaUnpairedOddEndpoint_div_le hM hd)
    (pairedEtaCompletedMoebiusPhaseErrorConstant_nonneg rho)
  convert h using 1 <;> ring

/-- Every retained leading parity phase has the fixed completion bound. -/
theorem norm_pairedEtaCompletedMoebiusParityPhase_le (rho : NontrivialZetaZero) (M d : ℕ) :
    ‖pairedEtaCompletedMoebiusParityPhase rho M d‖ ≤ ‖pairedEtaXiCompletionFactor rho.1‖ / 2 := by
  have hmu : ‖(μ d : ℂ)‖ ≤ 1 := by
    simpa only [Complex.norm_intCast] using
      (show (|μ d| : ℝ) ≤ 1 by exact_mod_cast (ArithmeticFunction.abs_moebius_le_one (n := d)))
  have hsign : ‖(pairedEtaDirichletSign (M / d) : ℂ)‖ = 1 := by
    have h : (|pairedEtaDirichletSign (M / d)| : ℝ) = 1 := by
      exact_mod_cast abs_pairedEtaDirichletSign (M / d)
    simpa only [Int.cast_abs, Complex.norm_intCast] using h
  unfold pairedEtaCompletedMoebiusParityPhase
  rw [norm_div, norm_mul, norm_mul, hsign, mul_one]
  norm_num only [norm_ofNat]
  exact div_le_div_of_nonneg_right
    (by simpa only [one_mul] using mul_le_mul_of_nonneg_right hmu (norm_nonneg (pairedEtaXiCompletionFactor rho.1)))
    (by norm_num)

end

end RiemannGaussian
