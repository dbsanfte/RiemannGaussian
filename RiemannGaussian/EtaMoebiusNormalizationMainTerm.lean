import RiemannGaussian.EtaMoebiusLogEulerCancellation
import RiemannGaussian.EtaMoebiusArithmeticGrowingHead

/-!
# The exact normalization main term and interior prime discrepancy

Cancellation of the complete Euler quotient correction identifies the
main term of the original normalization: `p_M log M → 1`. The actual
residual on every cell through `M` retains its exact signed prime
discrepancy plus one common normalization error. That error tends to
zero uniformly at the cell level; its growing square-sum cost is kept
explicit and is not asserted to vanish.
-/

open Filter
open scoped Topology

namespace RiemannGaussian

noncomputable section

/-- The original logarithmic Möbius normalization has the exact main term `1 / log M`, with its full signed Euler correction discharged. -/
theorem pairedEtaMoebiusLogHarmonic_mul_log_tendsto_one :
    Tendsto (fun M : ℕ ↦ pairedEtaMoebiusLogHarmonic M * Real.log M) atTop (𝓝 1) := by
  have hz : Tendsto (fun M : ℕ ↦ 1 - Real.eulerMascheroniConstant * moebiusHarmonicPrefix M -
      pairedEtaMoebiusLogEulerCorrection M) atTop (𝓝 1) := by
    simpa only [mul_zero, sub_zero] using
      ((tendsto_const_nhds (x := (1 : ℝ))).sub
        (moebiusHarmonicPrefix_tendsto_zero.const_mul Real.eulerMascheroniConstant)).sub
      pairedEtaMoebiusLogEulerCorrection_tendsto_zero
  apply hz.congr'
  filter_upwards [eventually_gt_atTop 1] with M hM
  exact (pairedEtaMoebiusLogHarmonic_mul_log_eq_euler hM).symm

/-- The exact normalization error after subtracting its now identified leading coefficient. -/
def pairedEtaMoebiusLogNormalizationError (M : ℕ) : ℝ :=
  pairedEtaMoebiusLogHarmonic M * Real.log M - 1

/-- The original normalized coefficient error tends to zero without any assumption about the full critical-square residual. -/
theorem pairedEtaMoebiusLogNormalizationError_tendsto_zero :
    Tendsto pairedEtaMoebiusLogNormalizationError atTop (𝓝 0) := by
  change Tendsto (fun M : ℕ ↦ pairedEtaMoebiusLogHarmonic M * Real.log M - 1) atTop (𝓝 0)
  simpa only [sub_self] using pairedEtaMoebiusLogHarmonic_mul_log_tendsto_one.sub_const 1

/-- At every physical cell through the coefficient cutoff, the actual logarithmically rescaled residual is exactly its original prime discrepancy plus the common normalization error. -/
theorem pairedEtaMoebiusArithmeticCellResidual_mul_log_eq_primeDiscrepancy {M L : ℕ}
    (hM : 1 < M) (hL : 1 ≤ L) (hLM : L ≤ M) :
    Real.log M * pairedEtaMoebiusArithmeticCellResidual M (pairedEtaMoebiusTrialLogWeight M) L =
      (pairedEtaArithmeticHarmonicPrefix L - pairedEtaPrimeHarmonicShell L) +
        pairedEtaMoebiusLogNormalizationError M * pairedEtaArithmeticHarmonicPrefix L := by
  rw [pairedEtaMoebiusArithmeticCellResidual_log_eq_primeShell hM hL hLM]
  have hl : Real.log (M : ℝ) ≠ 0 := (Real.log_pos (by exact_mod_cast hM)).ne'
  unfold pairedEtaMoebiusLogNormalizationError
  field_simp
  ring

/-- The entire growing interior has one uniform cell-level discrepancy allowance from the actual normalization error; no growing square sum is discarded. -/
theorem abs_pairedEtaMoebiusArithmeticCellResidual_mul_log_sub_primeDiscrepancy_le {M L : ℕ}
    (hM : 1 < M) (hL : 1 ≤ L) (hLM : L ≤ M) :
    |Real.log M * pairedEtaMoebiusArithmeticCellResidual M (pairedEtaMoebiusTrialLogWeight M) L -
      (pairedEtaArithmeticHarmonicPrefix L - pairedEtaPrimeHarmonicShell L)| ≤
        2 * |pairedEtaMoebiusLogNormalizationError M| := by
  rw [pairedEtaMoebiusArithmeticCellResidual_mul_log_eq_primeDiscrepancy hM hL hLM,
    add_sub_cancel_left, abs_mul]
  simpa only [mul_comm] using mul_le_mul_of_nonneg_left
    (abs_pairedEtaArithmeticHarmonicPrefix_le_two L) (abs_nonneg (pairedEtaMoebiusLogNormalizationError M))

/-- The approximation by the exact prime discrepancy is uniform over all original interior cells as the arithmetic cutoff grows. -/
theorem pairedEtaMoebiusArithmeticCellResidual_mul_log_uniform_primeDiscrepancy :
    ∀ eps : ℝ, 0 < eps → ∃ N : ℕ, ∀ M : ℕ, N ≤ M → ∀ L : ℕ, 1 ≤ L → L ≤ M →
      |Real.log M * pairedEtaMoebiusArithmeticCellResidual M (pairedEtaMoebiusTrialLogWeight M) L -
        (pairedEtaArithmeticHarmonicPrefix L - pairedEtaPrimeHarmonicShell L)| < eps := by
  intro eps heps
  have hz : Tendsto (fun M : ℕ ↦ 2 * |pairedEtaMoebiusLogNormalizationError M|) atTop (𝓝 0) := by
    simpa only [abs_zero, mul_zero] using pairedEtaMoebiusLogNormalizationError_tendsto_zero.abs.const_mul (2 : ℝ)
  obtain ⟨N, hN⟩ := eventually_atTop.mp (hz.eventually (gt_mem_nhds heps))
  refine ⟨max N 2, fun M hM L hL hLM ↦ ?_⟩
  have hM2 : 1 < M := by have := (le_max_right N 2).trans hM; omega
  exact (abs_pairedEtaMoebiusArithmeticCellResidual_mul_log_sub_primeDiscrepancy_le hM2 hL hLM).trans_lt
    (hN M ((le_max_left N 2).trans hM))

/-- The actual finite interior retains its complete signed square expansion around the prime discrepancy, including the cross moment and growing normalization mass. -/
theorem pairedEtaMoebiusArithmeticSquarePrefix_mul_log_sq_eq_discrepancy {M R : ℕ}
    (hM : 1 < M) (hRM : R ≤ M) :
    Real.log M ^ 2 * pairedEtaMoebiusArithmeticSquarePrefix M R (pairedEtaMoebiusTrialLogWeight M) =
      (∑ n ∈ Finset.range R, (pairedEtaArithmeticHarmonicPrefix (n + 1) - pairedEtaPrimeHarmonicShell (n + 1)) ^ 2) +
      2 * pairedEtaMoebiusLogNormalizationError M *
        (∑ n ∈ Finset.range R, pairedEtaArithmeticHarmonicPrefix (n + 1) *
          (pairedEtaArithmeticHarmonicPrefix (n + 1) - pairedEtaPrimeHarmonicShell (n + 1))) +
      pairedEtaMoebiusLogNormalizationError M ^ 2 *
        ∑ n ∈ Finset.range R, pairedEtaArithmeticHarmonicPrefix (n + 1) ^ 2 := by
  unfold pairedEtaMoebiusArithmeticSquarePrefix
  simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro n hn
  have he := pairedEtaMoebiusArithmeticCellResidual_mul_log_eq_primeDiscrepancy hM
    (show 1 ≤ n + 1 by omega) (show n + 1 ≤ M by have := Finset.mem_range.mp hn; omega)
  rw [← mul_pow, he]
  ring

/-- A square-sum estimate keeps the dimension cost of the vanishing cell-level normalization error explicit; its growing contribution is not assumed small. -/
theorem pairedEtaMoebiusArithmeticSquarePrefix_le_discrepancy {M R : ℕ}
    (hM : 1 < M) (hRM : R ≤ M) :
    pairedEtaMoebiusArithmeticSquarePrefix M R (pairedEtaMoebiusTrialLogWeight M) ≤
      (2 * (∑ n ∈ Finset.range R, (pairedEtaArithmeticHarmonicPrefix (n + 1) - pairedEtaPrimeHarmonicShell (n + 1)) ^ 2) +
        8 * R * pairedEtaMoebiusLogNormalizationError M ^ 2) / Real.log M ^ 2 := by
  have hl : Real.log (M : ℝ) ≠ 0 := (Real.log_pos (by exact_mod_cast hM)).ne'
  apply (le_div_iff₀ (sq_pos_of_ne_zero hl)).mpr
  rw [mul_comm, pairedEtaMoebiusArithmeticSquarePrefix, Finset.mul_sum]
  have hpoint (n : ℕ) (hn : n ∈ Finset.range R) :
      Real.log M ^ 2 * pairedEtaMoebiusArithmeticCellResidual M (pairedEtaMoebiusTrialLogWeight M) (n + 1) ^ 2 ≤
        2 * (pairedEtaArithmeticHarmonicPrefix (n + 1) - pairedEtaPrimeHarmonicShell (n + 1)) ^ 2 +
          8 * pairedEtaMoebiusLogNormalizationError M ^ 2 := by
    have he := pairedEtaMoebiusArithmeticCellResidual_mul_log_eq_primeDiscrepancy hM
      (show 1 ≤ n + 1 by omega) (show n + 1 ≤ M by have := Finset.mem_range.mp hn; omega)
    have hh := pow_le_pow_left₀ (abs_nonneg _) (abs_pairedEtaArithmeticHarmonicPrefix_le_two (n + 1)) 2
    rw [sq_abs] at hh
    have hs := mul_le_mul_of_nonneg_left hh (sq_nonneg (pairedEtaMoebiusLogNormalizationError M))
    rw [← mul_pow, he]
    nlinarith [sq_nonneg ((pairedEtaArithmeticHarmonicPrefix (n + 1) - pairedEtaPrimeHarmonicShell (n + 1)) -
      pairedEtaMoebiusLogNormalizationError M * pairedEtaArithmeticHarmonicPrefix (n + 1))]
  have h := Finset.sum_le_sum hpoint
  simpa only [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const, Finset.card_range, nsmul_eq_mul,
    mul_assoc, mul_left_comm, mul_comm] using h

end

end RiemannGaussian
