import RiemannGaussian.EtaWeightedDivisorFourier
import RiemannGaussian.EtaMoebiusParityEnergy
import RiemannGaussian.FiniteCircleDualSampling

/-!
# Fourier sampling with the full signed divisor coefficient energy

The actual quotient family keeps every mixed product in its exact square.
Its complete-period energy is the signed gcd covariance form. The proved
row estimate and separated Fourier sampling then control arbitrary
physical windows by the energy of the retained coefficients.
-/

open Complex
open scoped Classical

namespace RiemannGaussian

noncomputable section

/-- The literal weighted family square keeps every actual signed
divisor pair and its quotient-parity correlation. -/
theorem pairedEtaWeightedDivisorParityFamily_norm_sq_eq_pairs
    (w : ℕ → ℝ) (M T : ℕ) :
    ‖pairedEtaWeightedDivisorParityFamily w M T‖ ^ 2 =
      ∑ d ∈ Finset.Icc 1 T, ∑ e ∈ Finset.Icc 1 T,
        w d * w e * (pairedEtaDivisorParityProduct d e M : ℝ) := by
  rw [pairedEtaWeightedDivisorParityFamily_eq_real, Complex.norm_real, Real.norm_eq_abs, sq_abs]
  simp only [sq, Finset.sum_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro d hd
  apply Finset.sum_congr rfl
  intro e he
  rw [pairedEtaDivisorParityProduct, Int.cast_mul]
  ring

/-- The exact complete-period energy retains the full signed
coefficient covariance before applying an operator bound. -/
theorem pairedEtaWeightedDivisorParityFamily_period_energy_eq
    (w : ℕ → ℝ) (A T : ℕ) {Q : ℕ} (hQ : 0 < Q)
    (hperiod : ∀ d ∈ Finset.Icc 1 T, ∀ e ∈ Finset.Icc 1 T, 2 * d * e ∣ Q) :
    (∑ n ∈ Finset.range Q, ‖pairedEtaWeightedDivisorParityFamily w (A + n) T‖ ^ 2) / Q =
      ∑ d ∈ Finset.Icc 1 T, ∑ e ∈ Finset.Icc 1 T,
        w d * w e * pairedEtaDivisorParityCovariance d e := by
  have hQR : (Q : ℝ) ≠ 0 := by exact_mod_cast hQ.ne'
  have hp (d : ℕ) (hd : d ∈ Finset.Icc 1 T) (e : ℕ) (he : e ∈ Finset.Icc 1 T) :
      (∑ n ∈ Finset.range Q, w d * w e * (pairedEtaDivisorParityProduct d e (A + n) : ℝ)) =
        (Q : ℝ) * (w d * w e * pairedEtaDivisorParityCovariance d e) := by
    rw [← Finset.mul_sum, sum_range_pairedEtaDivisorParity_eq_mul_covariance_of_dvd A
      (Finset.mem_Icc.mp hd).1 (Finset.mem_Icc.mp he).1 (hperiod d hd e he)]
    ring
  simp_rw [pairedEtaWeightedDivisorParityFamily_norm_sq_eq_pairs]
  rw [Finset.sum_comm]
  conv_lhs =>
    arg 1
    arg 2
    ext d
    rw [Finset.sum_comm]
  have hs : (∑ d ∈ Finset.Icc 1 T, ∑ e ∈ Finset.Icc 1 T,
      ∑ n ∈ Finset.range Q, w d * w e * (pairedEtaDivisorParityProduct d e (A + n) : ℝ)) =
        (Q : ℝ) * ∑ d ∈ Finset.Icc 1 T, ∑ e ∈ Finset.Icc 1 T,
          w d * w e * pairedEtaDivisorParityCovariance d e := by
    simp only [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro d hd
    apply Finset.sum_congr rfl
    intro e he
    exact hp d hd e he
  rw [hs, mul_div_cancel_left₀ _ hQR]

/-- Every complete common-period energy is bounded by the actual
signed coefficient energy with a squared logarithmic operator cost. -/
theorem pairedEtaWeightedDivisorParityFamily_period_energy_le
    (w : ℕ → ℝ) (A T : ℕ) {Q : ℕ} (hQ : 0 < Q)
    (hperiod : ∀ d ∈ Finset.Icc 1 T, ∀ e ∈ Finset.Icc 1 T, 2 * d * e ∣ Q) :
    (∑ n ∈ Finset.range Q, ‖pairedEtaWeightedDivisorParityFamily w (A + n) T‖ ^ 2) / Q ≤
      (1 + Real.log T) ^ 2 * ∑ d ∈ Finset.Icc 1 T, w d ^ 2 := by
  rw [pairedEtaWeightedDivisorParityFamily_period_energy_eq w A T hQ hperiod]
  exact sum_Icc_weighted_pairedEtaDivisorParityCovariance_le_log_sq w T

/-- Proved divisor-frequency separation controls the actual window
energy of the whole signed weighted family. The auxiliary grid cancels. -/
theorem pairedEtaWeightedDivisorParityFamily_window_sq_le
    (w : ℕ → ℝ) (A : ℕ) {T L : ℕ} (hT : 1 ≤ T) (hL : 0 < L) :
    (∑ n ∈ Finset.range L, ‖pairedEtaWeightedDivisorParityFamily w (A + n) T‖ ^ 2) ≤
      finiteCircleSamplingConstant * (4 * (T : ℝ) ^ 2 + L) *
        ((1 + Real.log T) ^ 2 * ∑ d ∈ Finset.Icc 1 T, w d ^ 2) := by
  let Q := pairedEtaDivisorFourierGrid T L
  have hQpos : 0 < Q := pairedEtaDivisorFourierGrid_pos T hL
  let : NeZero Q := ⟨hQpos.ne'⟩
  have hperiod : ∀ d ∈ Finset.Icc 1 T, ∀ e ∈ Finset.Icc 1 T, 2 * d * e ∣ Q := by
    intro d hd e he
    exact (pairedEtaDivisorPairPeriod_dvd_block hd he).trans (dvd_mul_right _ _)
  have hsingle : ∀ d ∈ Finset.Icc 1 T, 2 * d ∣ Q := by
    intro d hd
    exact (pairedEtaDivisorPeriod_dvd_block hd).trans (dvd_mul_right _ _)
  have hscale : 4 * T ^ 2 * pairedEtaDivisorFourierBlock T ≤ Q := by
    dsimp [Q, pairedEtaDivisorFourierGrid, pairedEtaDivisorFourierBudget]
    nlinarith
  have hs := sum_range_finiteCircleSynthesis_separated_le
    (pairedEtaDivisorFourierSpectrum T Q)
    (finitePeriodicFourierCoefficient (fun n ↦ pairedEtaWeightedDivisorParityFamily w (A + n) T))
    (pairedEtaDivisorFourierBlock_pos T)
    (by unfold pairedEtaDivisorFourierBudget; omega : 0 < pairedEtaDivisorFourierBudget T L)
    (rfl : Q = pairedEtaDivisorFourierBlock T * pairedEtaDivisorFourierBudget T L)
    (by unfold pairedEtaDivisorFourierBudget; omega : L ≤ pairedEtaDivisorFourierBudget T L)
    (pairedEtaDivisorFourierSpectrum_separated hT hscale)
  simp_rw [pairedEtaWeightedDivisorParityFamily_eq_fourier w A T hsingle] at hs
  rw [pairedEtaWeightedDivisorParityFamily_fourier_energy w A T hsingle] at hs
  apply hs.trans
  have h := mul_le_mul_of_nonneg_left
    (pairedEtaWeightedDivisorParityFamily_period_energy_le w A T hQpos hperiod)
    (mul_nonneg finiteCircleSamplingConstant_pos.le
      (Nat.cast_nonneg (α := ℝ) (pairedEtaDivisorFourierBudget T L)))
  simpa only [pairedEtaDivisorFourierBudget, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat,
    Nat.cast_pow] using h

/-- Throughout the quadratic product range, the whole weighted
family has mean square bounded by its retained coefficient energy. -/
theorem pairedEtaWeightedDivisorParityFamily_meanSquare_le_quadratic
    (w : ℕ → ℝ) (A : ℕ) {T L : ℕ} (hT : 1 ≤ T) (hTL : T ^ 2 ≤ L) :
    (∑ n ∈ Finset.range L, ‖pairedEtaWeightedDivisorParityFamily w (A + n) T‖ ^ 2) / L ≤
      5 * finiteCircleSamplingConstant * (1 + Real.log T) ^ 2 *
        ∑ d ∈ Finset.Icc 1 T, w d ^ 2 := by
  have hL : 0 < L := (pow_pos hT 2).trans_le hTL
  have hLR : (0 : ℝ) < L := by exact_mod_cast hL
  have hTLR : (T : ℝ) ^ 2 ≤ L := by exact_mod_cast hTL
  have hbudget : 4 * (T : ℝ) ^ 2 + L ≤ 5 * L := by linarith
  apply (div_le_iff₀ hLR).mpr
  apply (pairedEtaWeightedDivisorParityFamily_window_sq_le w A hT hL).trans
  have h := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left hbudget finiteCircleSamplingConstant_pos.le)
    (show 0 ≤ (1 + Real.log T) ^ 2 * ∑ d ∈ Finset.Icc 1 T, w d ^ 2 from
      mul_nonneg (sq_nonneg _) (Finset.sum_nonneg (fun d _ ↦ sq_nonneg (w d))))
  convert h using 1
  ring

end

end RiemannGaussian
