import RiemannGaussian.EtaMoebiusFourierSpectrum
import RiemannGaussian.EtaDivisorCovarianceOperator

/-!
# Exact Fourier support for signed divisor-product coefficients

The literal quotient-parity columns retain arbitrary real coefficients,
so the signed product fibers of the original inverse can be grouped
before estimating their energy. Actual divisor periodicity proves the
Fourier support; no support or independence premise is assumed.
-/

open Complex
open scoped Classical

namespace RiemannGaussian

noncomputable section

/-- The literal quotient-parity family with all signed divisor
coefficients retained inside the complex sum. -/
def pairedEtaWeightedDivisorParityFamily (w : ℕ → ℝ) (M T : ℕ) : ℂ :=
  ∑ d ∈ Finset.Icc 1 T, (w d : ℂ) * (pairedEtaDirichletSign (M / d) : ℂ)

/-- The complex family retains its exact signed real arithmetic value. -/
theorem pairedEtaWeightedDivisorParityFamily_eq_real (w : ℕ → ℝ) (M T : ℕ) :
    pairedEtaWeightedDivisorParityFamily w M T =
      ((∑ d ∈ Finset.Icc 1 T, w d * (pairedEtaDirichletSign (M / d) : ℝ)) : ℝ) := by
  simp only [pairedEtaWeightedDivisorParityFamily, Complex.ofReal_sum,
    Complex.ofReal_mul, Complex.ofReal_intCast]

/-- Every signed quotient column keeps its literal divisor period,
at every starting physical cutoff and every real coefficient. -/
theorem pairedEtaWeightedDivisorParityColumn_periodic (w : ℕ → ℝ) (A : ℕ)
    {d : ℕ} (hd : 0 < d) :
    Function.Periodic
      (fun n ↦ (w d : ℂ) * (pairedEtaDirichletSign ((A + n) / d) : ℂ)) (2 * d) := by
  intro n
  change (w d : ℂ) * (pairedEtaDirichletSign ((A + (n + 2 * d)) / d) : ℂ) = _
  rw [← Nat.add_assoc, show 2 * d = d * 2 by omega,
    Nat.add_mul_div_left (A + n) 2 hd,
    pairedEtaDirichletSign_add_even _ _ (by decide : Even 2)]

/-- A common multiple of the divisor periods is a period of the
entire weighted family, with every product coefficient unchanged. -/
theorem pairedEtaWeightedDivisorParityFamily_periodic (w : ℕ → ℝ) (A T Q : ℕ)
    (hQ : ∀ d ∈ Finset.Icc 1 T, 2 * d ∣ Q) :
    Function.Periodic (fun n ↦ pairedEtaWeightedDivisorParityFamily w (A + n) T) Q := by
  intro n
  unfold pairedEtaWeightedDivisorParityFamily
  apply Finset.sum_congr rfl
  intro d hd
  exact periodic_nat_of_dvd
    (pairedEtaWeightedDivisorParityColumn_periodic w A (Finset.mem_Icc.mp hd).1) (hQ d hd) n

variable {Q : ℕ} [NeZero Q]

/-- The actual weighted family has no coefficient outside its proved
arithmetic divisor spectrum. -/
theorem pairedEtaWeightedDivisorParityFamily_fourier_eq_zero (w : ℕ → ℝ) (A T : ℕ)
    (hQ : ∀ d ∈ Finset.Icc 1 T, 2 * d ∣ Q) (k : ZMod Q)
    (hk : k ∉ pairedEtaDivisorFourierSpectrum T Q) :
    finitePeriodicFourierCoefficient
      (fun n ↦ pairedEtaWeightedDivisorParityFamily w (A + n) T) k = 0 := by
  unfold pairedEtaWeightedDivisorParityFamily
  rw [finitePeriodicFourierCoefficient_sum]
  apply Finset.sum_eq_zero
  intro d hd
  have hp := pairedEtaWeightedDivisorParityColumn_periodic w A (Finset.mem_Icc.mp hd).1
  apply finitePeriodicFourierCoefficient_eq_zero_of_period _ (periodic_nat_of_dvd hp (hQ d hd)) hp
  intro hz
  exact hk ((mem_pairedEtaDivisorFourierSpectrum T k).mpr ⟨d, hd, hz⟩)

/-- Exact synthesis on the proved divisor spectrum reconstructs the
whole signed weighted family at every physical sample. -/
theorem pairedEtaWeightedDivisorParityFamily_eq_fourier (w : ℕ → ℝ)
    (A T : ℕ) (hQ : ∀ d ∈ Finset.Icc 1 T, 2 * d ∣ Q) (n : ℕ) :
    finiteCircleSynthesis (pairedEtaDivisorFourierSpectrum T Q) id
      (finitePeriodicFourierCoefficient
        (fun m ↦ pairedEtaWeightedDivisorParityFamily w (A + m) T)) n =
      pairedEtaWeightedDivisorParityFamily w (A + n) T := by
  rw [← finitePeriodicFourierCoefficient_synthesis _
    (pairedEtaWeightedDivisorParityFamily_periodic w A T Q hQ) n]
  unfold finiteCircleSynthesis
  apply Finset.sum_subset (Finset.subset_univ _)
  intro k hk hknot
  rw [pairedEtaWeightedDivisorParityFamily_fourier_eq_zero w A T hQ k hknot, zero_mul]

/-- The full coefficient energy on the proved arithmetic spectrum
equals the actual complete-period energy, with every signed fiber retained. -/
theorem pairedEtaWeightedDivisorParityFamily_fourier_energy (w : ℕ → ℝ)
    (A T : ℕ) (hQ : ∀ d ∈ Finset.Icc 1 T, 2 * d ∣ Q) :
    (∑ k ∈ pairedEtaDivisorFourierSpectrum T Q,
      ‖finitePeriodicFourierCoefficient
        (fun n ↦ pairedEtaWeightedDivisorParityFamily w (A + n) T) k‖ ^ 2) =
      (∑ n ∈ Finset.range Q, ‖pairedEtaWeightedDivisorParityFamily w (A + n) T‖ ^ 2) / Q := by
  rw [← sum_finitePeriodicFourierCoefficient_norm_sq _
    (pairedEtaWeightedDivisorParityFamily_periodic w A T Q hQ)]
  apply Finset.sum_subset (Finset.subset_univ _)
  intro k hk hknot
  rw [pairedEtaWeightedDivisorParityFamily_fourier_eq_zero w A T hQ k hknot,
    norm_zero, zero_pow (by decide)]

end

end RiemannGaussian
