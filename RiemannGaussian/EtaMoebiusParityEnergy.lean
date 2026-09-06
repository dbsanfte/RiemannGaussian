import RiemannGaussian.EtaMoebiusFourierSpectrum

/-!
# Exact complete-period energy of the literal eta parity family

The family square keeps the whole signed Möbius covariance, including every
off-diagonal term. The exact pair-period formula evaluates every complete
common period. Only then is the proved gcd-sum bound applied.
-/

open Complex
open scoped Classical ComplexConjugate

namespace RiemannGaussian

noncomputable section

/-- The literal leading family square retains all complex divisor pairs. -/
theorem pairedEtaCompletedMoebiusParityFamily_norm_sq_eq_pairs
    (rho : NontrivialZetaZero) (M D : ℕ) :
    (‖pairedEtaCompletedMoebiusParityFamily rho M D‖ : ℂ) ^ 2 =
      ∑ d ∈ Finset.Icc 1 D, ∑ e ∈ Finset.Icc 1 D,
        pairedEtaCompletedMoebiusParityPair rho M d e := by
  rw [← Complex.mul_conj']
  simp only [pairedEtaCompletedMoebiusParityFamily, map_sum, Finset.sum_mul,
    Finset.mul_sum, pairedEtaCompletedMoebiusParityPair]
  rw [Finset.sum_comm]

/-- Every complete multiple of the actual pair period has its exact
gcd covariance, at any starting cutoff. -/
theorem sum_range_pairedEtaDivisorParity_eq_mul_covariance_of_dvd
    (A : ℕ) {Q d e : ℕ} (hd : 0 < d) (he : 0 < e) (hQ : 2 * d * e ∣ Q) :
    (∑ n ∈ Finset.range Q, (pairedEtaDivisorParityProduct d e (A + n) : ℝ)) =
      (Q : ℝ) * pairedEtaDivisorParityCovariance d e := by
  have hp : Function.Periodic (fun n ↦ (pairedEtaDivisorParityProduct d e n : ℝ)) (2 * d * e) :=
    fun n ↦ congrArg (fun z : ℤ ↦ (z : ℝ)) (pairedEtaDivisorParityProduct_periodic hd he n)
  rw [sum_range_nat_periodic_shift (periodic_nat_of_dvd hp hQ)]
  obtain ⟨k, rfl⟩ := hQ
  rw [sum_range_nat_periodic_mul hp,
    sum_range_pairedEtaDivisorParity_eq_period_mul_covariance d e hd he]
  simp only [nsmul_eq_mul, Nat.cast_mul]
  ring

/-- The complete common-period family energy evaluates exactly to the
full signed Möbius gcd covariance, before any absolute-value estimate. -/
theorem pairedEtaCompletedMoebiusParityFamily_period_energy_eq
    (rho : NontrivialZetaZero) (A D : ℕ) {Q : ℕ} (hQ : 0 < Q)
    (hperiod : ∀ d ∈ Finset.Icc 1 D, ∀ e ∈ Finset.Icc 1 D, 2 * d * e ∣ Q) :
    (∑ n ∈ Finset.range Q, ‖pairedEtaCompletedMoebiusParityFamily rho (A + n) D‖ ^ 2) / Q =
      ∑ d ∈ Finset.Icc 1 D, ∑ e ∈ Finset.Icc 1 D,
        pairedEtaCompletedMoebiusDivisorCoefficient rho d e * pairedEtaDivisorParityCovariance d e := by
  have hQC : (Q : ℂ) ≠ 0 := by exact_mod_cast hQ.ne'
  have hp (d : ℕ) (hd : d ∈ Finset.Icc 1 D) (e : ℕ) (he : e ∈ Finset.Icc 1 D) :
      (∑ n ∈ Finset.range Q, pairedEtaCompletedMoebiusParityPair rho (A + n) d e) =
        (Q : ℂ) * ((pairedEtaCompletedMoebiusDivisorCoefficient rho d e *
          pairedEtaDivisorParityCovariance d e : ℝ) : ℂ) := by
    simp_rw [pairedEtaCompletedMoebiusParityPair_eq_divisorCoefficient]
    rw [← Finset.mul_sum]
    have hs := sum_range_pairedEtaDivisorParity_eq_mul_covariance_of_dvd A
      (Finset.mem_Icc.mp hd).1 (Finset.mem_Icc.mp he).1 (hperiod d hd e he)
    have hsC : (∑ n ∈ Finset.range Q, (pairedEtaDivisorParityProduct d e (A + n) : ℂ)) =
        (Q : ℂ) * (pairedEtaDivisorParityCovariance d e : ℂ) := by exact_mod_cast hs
    rw [hsC]
    push_cast
    ring
  have heq : ((∑ n ∈ Finset.range Q,
        ‖pairedEtaCompletedMoebiusParityFamily rho (A + n) D‖ ^ 2) / Q : ℝ) =
      ∑ d ∈ Finset.Icc 1 D, ∑ e ∈ Finset.Icc 1 D,
        pairedEtaCompletedMoebiusDivisorCoefficient rho d e * pairedEtaDivisorParityCovariance d e := by
    apply Complex.ofReal_injective
    push_cast
    simp_rw [pairedEtaCompletedMoebiusParityFamily_norm_sq_eq_pairs]
    rw [Finset.sum_comm]
    conv_lhs =>
      arg 1
      arg 2
      ext d
      rw [Finset.sum_comm]
    have hs : (∑ d ∈ Finset.Icc 1 D, ∑ e ∈ Finset.Icc 1 D,
        ∑ n ∈ Finset.range Q, pairedEtaCompletedMoebiusParityPair rho (A + n) d e) =
        (Q : ℂ) * ∑ d ∈ Finset.Icc 1 D, ∑ e ∈ Finset.Icc 1 D,
          ((pairedEtaCompletedMoebiusDivisorCoefficient rho d e *
            pairedEtaDivisorParityCovariance d e : ℝ) : ℂ) := by
      simp only [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro d hd
      apply Finset.sum_congr rfl
      intro e he
      exact hp d hd e he
    rw [hs, mul_div_cancel_left₀ _ hQC]
    push_cast
    rfl
  exact heq

/-- The complete leading-family energy has linear logarithmic divisor
cost, with the actual completion amplitude retained. -/
theorem pairedEtaCompletedMoebiusParityFamily_period_energy_le
    (rho : NontrivialZetaZero) (A D : ℕ) {Q : ℕ} (hQ : 0 < Q)
    (hperiod : ∀ d ∈ Finset.Icc 1 D, ∀ e ∈ Finset.Icc 1 D, 2 * d * e ∣ Q) :
    (∑ n ∈ Finset.range Q, ‖pairedEtaCompletedMoebiusParityFamily rho (A + n) D‖ ^ 2) / Q ≤
      ‖pairedEtaXiCompletionFactor rho.1‖ ^ 2 / 2 * D * (1 + Real.log D) := by
  rw [pairedEtaCompletedMoebiusParityFamily_period_energy_eq rho A D hQ hperiod]
  calc
    _ ≤ ∑ d ∈ Finset.Icc 1 D, ∑ e ∈ Finset.Icc 1 D,
        (‖pairedEtaXiCompletionFactor rho.1‖ ^ 2 / 4) * pairedEtaDivisorParityCovariance d e := by
      apply Finset.sum_le_sum
      intro d hd
      apply Finset.sum_le_sum
      intro e he
      exact mul_le_mul_of_nonneg_right
        ((le_abs_self _).trans (abs_pairedEtaCompletedMoebiusDivisorCoefficient_le rho d e))
        (pairedEtaDivisorParityCovariance_nonneg d e)
    _ = (‖pairedEtaXiCompletionFactor rho.1‖ ^ 2 / 4) *
        (∑ d ∈ Finset.Icc 1 D, ∑ e ∈ Finset.Icc 1 D, pairedEtaDivisorParityCovariance d e) := by
      simp only [← Finset.mul_sum]
    _ ≤ (‖pairedEtaXiCompletionFactor rho.1‖ ^ 2 / 4) * (2 * D * (1 + Real.log D)) :=
      mul_le_mul_of_nonneg_left (sum_Icc_pairedEtaDivisorParityCovariance_le_log D) (by positivity)
    _ = _ := by ring

end

end RiemannGaussian
