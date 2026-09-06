import RiemannGaussian.EtaMoebiusDivisorCorrelation

/-!
# Mean-square cancellation for a growing completed eta divisor family

The literal endpoint-normalized completed Möbius terms are summed before
taking a square. Their full complex Gram is the actual double divisor sum,
with both endpoint powers retained. The covariance bound has linear times
logarithmic cost; the physical cutoff and incomplete-window costs remain
explicit and do not establish the original uniform weighted current bound.
-/

open Complex Filter MeasureTheory Set Topology
open scoped Classical ComplexConjugate ENNReal Interval Topology ArithmeticFunction.Moebius

namespace RiemannGaussian

noncomputable section

/-- The actual completed endpoint phases in the first `D` divisor columns. -/
def pairedEtaCompletedMoebiusEndpointFamily (rho : NontrivialZetaZero) (M D : ℕ) : ℂ :=
  ∑ d ∈ Finset.Icc 1 D, pairedEtaCompletedMoebiusEndpointPhase rho M d

/-- The full complex family Gram is the double sum of the actual endpoint
pairs. Cross-column correlations are retained before taking any bound. -/
theorem pairedEtaCompletedMoebiusEndpointFamily_norm_sq_eq_pairs
    (rho : NontrivialZetaZero) (M D : ℕ) :
    (‖pairedEtaCompletedMoebiusEndpointFamily rho M D‖ : ℂ) ^ 2 =
      ∑ d ∈ Finset.Icc 1 D, ∑ e ∈ Finset.Icc 1 D,
        pairedEtaCompletedMoebiusEndpointPair rho M d e := by
  rw [← Complex.mul_conj']
  simp only [pairedEtaCompletedMoebiusEndpointFamily, map_sum, Finset.sum_mul,
    Finset.mul_sum, pairedEtaCompletedMoebiusEndpointPair]
  rw [Finset.sum_comm]

/-- The family Gram retains both literal complex endpoint powers on
every entry of the original completed Möbius pair kernel. -/
theorem pairedEtaCompletedMoebiusEndpointFamily_norm_sq_eq_physical_kernel
    (rho : NontrivialZetaZero) (M D : ℕ) :
    (‖pairedEtaCompletedMoebiusEndpointFamily rho M D‖ : ℂ) ^ 2 =
      ∑ d ∈ Finset.Icc 1 D, ∑ e ∈ Finset.Icc 1 D,
        ((((d * pairedEtaUnpairedOddEndpoint (M / d) : ℕ) : ℂ) ^ rho.1 *
          starRingEnd ℂ (((e * pairedEtaUnpairedOddEndpoint (M / e) : ℕ) : ℂ) ^ rho.1)) *
            pairedEtaCompletedMoebiusPairKernel rho M d e) := by
  rw [pairedEtaCompletedMoebiusEndpointFamily_norm_sq_eq_pairs]
  simp_rw [pairedEtaCompletedMoebiusEndpointPair_eq_physical_kernel]

/-- Mean square of the literal summed completed family on a finite
physical window, with its actual length in the denominator. -/
def pairedEtaCompletedMoebiusFamilyMeanSquare (rho : NontrivialZetaZero) (A L D : ℕ) : ℝ :=
  (∑ r ∈ Finset.range L, ‖pairedEtaCompletedMoebiusEndpointFamily rho (A + r) D‖ ^ 2) / L

/-- The actual averaged family square is nonnegative. -/
theorem pairedEtaCompletedMoebiusFamilyMeanSquare_nonneg
    (rho : NontrivialZetaZero) (A L D : ℕ) :
    0 ≤ pairedEtaCompletedMoebiusFamilyMeanSquare rho A L D := by
  unfold pairedEtaCompletedMoebiusFamilyMeanSquare
  positivity

/-- Averaging the complete family commutes exactly with the two finite
divisor sums; every actual complex pair is included. -/
theorem pairedEtaCompletedMoebiusFamilyMeanSquare_eq_correlations
    (rho : NontrivialZetaZero) (A L D : ℕ) :
    (pairedEtaCompletedMoebiusFamilyMeanSquare rho A L D : ℂ) =
      ∑ d ∈ Finset.Icc 1 D, ∑ e ∈ Finset.Icc 1 D,
        pairedEtaCompletedMoebiusDivisorCorrelation rho A L d e := by
  unfold pairedEtaCompletedMoebiusFamilyMeanSquare pairedEtaCompletedMoebiusDivisorCorrelation
  push_cast
  simp_rw [pairedEtaCompletedMoebiusEndpointFamily_norm_sq_eq_pairs, Finset.sum_div]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro d hd
  rw [Finset.sum_comm]

/-- Increasing either divisor only increases the explicit endpoint-error
majorant, without changing its physical starting cutoff. -/
theorem pairedEtaCompletedMoebiusPairPhaseError_le_diagonal
    (rho : NontrivialZetaZero) {d e D : ℕ} (hd : d ≤ D) (he : e ≤ D) (A : ℕ) :
    pairedEtaCompletedMoebiusPairPhaseError rho d e A ≤
      pairedEtaCompletedMoebiusPairPhaseError rho D D A := by
  have hdR : (d : ℝ) ≤ D := by exact_mod_cast hd
  have heR : (e : ℝ) ≤ D := by exact_mod_cast he
  have hH := pairedEtaCompletedMoebiusPhaseErrorConstant_nonneg rho
  unfold pairedEtaCompletedMoebiusPairPhaseError
  apply add_le_add
  · exact div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_left (add_le_add hdR heR) (by positivity)) (by positivity)
  · apply div_le_div_of_nonneg_right _ (by positivity)
    have hp := mul_le_mul hdR heR (Nat.cast_nonneg e) (Nat.cast_nonneg D)
    convert mul_le_mul_of_nonneg_left hp
      (by positivity : 0 ≤ 4 * pairedEtaCompletedMoebiusPhaseErrorConstant rho ^ 2) using 1 <;> ring

/-- All errors for a divisor family have a common explicit upper bound;
the averaging length and both physical endpoint errors remain visible. -/
theorem norm_pairedEtaCompletedMoebiusDivisorCorrelation_le_family
    (rho : NontrivialZetaZero) {A L D d e : ℕ}
    (hA : 1 ≤ A) (hL : 0 < L) (hd : d ∈ Finset.Icc 1 D) (he : e ∈ Finset.Icc 1 D) :
    ‖pairedEtaCompletedMoebiusDivisorCorrelation rho A L d e‖ ≤
      ‖pairedEtaXiCompletionFactor rho.1‖ ^ 2 / 4 * pairedEtaDivisorParityCovariance d e +
      (‖pairedEtaXiCompletionFactor rho.1‖ ^ 2 * (D : ℝ) ^ 2 / L +
        pairedEtaCompletedMoebiusPairPhaseError rho D D A) := by
  apply (norm_pairedEtaCompletedMoebiusDivisorCorrelation_le rho hA hL
    (Finset.mem_Icc.mp hd).1 (Finset.mem_Icc.mp he).1).trans
  apply add_le_add le_rfl
  apply add_le_add _ (pairedEtaCompletedMoebiusPairPhaseError_le_diagonal rho
    (Finset.mem_Icc.mp hd).2 (Finset.mem_Icc.mp he).2 A)
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg L)
  have hdR : (d : ℝ) ≤ D := by exact_mod_cast (Finset.mem_Icc.mp hd).2
  have heR : (e : ℝ) ≤ D := by exact_mod_cast (Finset.mem_Icc.mp he).2
  have hp := mul_le_mul hdR heR (Nat.cast_nonneg e) (Nat.cast_nonneg D)
  convert mul_le_mul_of_nonneg_left hp (sq_nonneg ‖pairedEtaXiCompletionFactor rho.1‖) using 1 <;> ring

/-- The whole actual completed family has a mean-square bound with a
linear logarithmic main cost and explicit growing-window and endpoint costs.
This theorem imposes no simplicity hypothesis on the actual zeta zero. -/
theorem pairedEtaCompletedMoebiusFamilyMeanSquare_le
    (rho : NontrivialZetaZero) {A L : ℕ} (hA : 1 ≤ A) (hL : 0 < L) (D : ℕ) :
    pairedEtaCompletedMoebiusFamilyMeanSquare rho A L D ≤
      ‖pairedEtaXiCompletionFactor rho.1‖ ^ 2 / 2 * D * (1 + Real.log D) +
      ‖pairedEtaXiCompletionFactor rho.1‖ ^ 2 * (D : ℝ) ^ 4 / L +
      2 * pairedEtaCompletedMoebiusPhaseErrorConstant rho * ‖pairedEtaXiCompletionFactor rho.1‖ *
        (D : ℝ) ^ 3 / A +
      4 * pairedEtaCompletedMoebiusPhaseErrorConstant rho ^ 2 * (D : ℝ) ^ 4 / (A : ℝ) ^ 2 := by
  let C := ‖pairedEtaXiCompletionFactor rho.1‖ ^ 2 / 4
  let E := ‖pairedEtaXiCompletionFactor rho.1‖ ^ 2 * (D : ℝ) ^ 2 / L +
    pairedEtaCompletedMoebiusPairPhaseError rho D D A
  have hC : 0 ≤ C := by dsimp [C]; positivity
  calc
    _ = ‖(pairedEtaCompletedMoebiusFamilyMeanSquare rho A L D : ℂ)‖ := by
      rw [Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (pairedEtaCompletedMoebiusFamilyMeanSquare_nonneg rho A L D)]
    _ = ‖∑ d ∈ Finset.Icc 1 D, ∑ e ∈ Finset.Icc 1 D,
          pairedEtaCompletedMoebiusDivisorCorrelation rho A L d e‖ := by
      rw [pairedEtaCompletedMoebiusFamilyMeanSquare_eq_correlations]
    _ ≤ ∑ d ∈ Finset.Icc 1 D, ∑ e ∈ Finset.Icc 1 D,
          ‖pairedEtaCompletedMoebiusDivisorCorrelation rho A L d e‖ := by
      apply (norm_sum_le _ _).trans
      apply Finset.sum_le_sum
      intro d hd
      exact norm_sum_le _ _
    _ ≤ ∑ d ∈ Finset.Icc 1 D, ∑ e ∈ Finset.Icc 1 D,
          (C * pairedEtaDivisorParityCovariance d e + E) := by
      apply Finset.sum_le_sum
      intro d hd
      apply Finset.sum_le_sum
      intro e he
      exact norm_pairedEtaCompletedMoebiusDivisorCorrelation_le_family rho hA hL hd he
    _ = C * (∑ d ∈ Finset.Icc 1 D, ∑ e ∈ Finset.Icc 1 D,
          pairedEtaDivisorParityCovariance d e) + (D : ℝ) ^ 2 * E := by
      simp only [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const,
        Nat.card_Icc, Nat.add_sub_cancel, nsmul_eq_mul]
      ring
    _ ≤ C * (2 * D * (1 + Real.log D)) + (D : ℝ) ^ 2 * E :=
      add_le_add (mul_le_mul_of_nonneg_left
        (sum_Icc_pairedEtaDivisorParityCovariance_le_log D) hC) le_rfl
    _ = _ := by dsimp [C, E, pairedEtaCompletedMoebiusPairPhaseError]; ring

end

end RiemannGaussian
