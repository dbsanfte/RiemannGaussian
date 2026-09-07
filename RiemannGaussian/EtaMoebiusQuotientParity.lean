import RiemannGaussian.EtaAlternatingHarmonicRemainder
import RiemannGaussian.EtaMoebiusArithmeticCells

/-!
# Exact quotient-parity representation of the arithmetic residual

The complete truncated divisor sum is regrouped by its Möbius divisor.
The constant logarithmic part cancels against the original harmonic
correction. Every remaining term keeps its quotient parity and exact
positive remainder amplitude, before any mean-square estimate is used.
-/

open scoped ArithmeticFunction.Moebius

namespace RiemannGaussian

noncomputable section

/-- The full truncated divisor harmonic prefix equals the signed sum of the original alternating harmonic prefixes at every literal quotient endpoint. -/
theorem sum_pairedEtaMoebiusArithmeticDivisor_div_eq_quotients (M L : ℕ) (w : ℕ → ℝ) :
    (∑ l ∈ Finset.Icc 1 L, pairedEtaMoebiusArithmeticDivisor M w l / l) =
      ∑ n ∈ Finset.Icc 1 M, ((μ n : ℝ) * w n / n) * pairedEtaArithmeticHarmonicPrefix (L / n) := by
  rw [sum_pairedEtaMoebiusArithmeticDivisor_div_eq_rectangle]
  simp_rw [Finset.mul_sum, mul_ite, mul_zero]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro n hn
  have hnp : 0 < n := (Finset.mem_Icc.mp hn).1
  have hc (m : ℕ) : n * m ≤ L ↔ m ≤ L / n := by
    rw [Nat.le_div_iff_mul_le hnp, Nat.mul_comm]
  simp_rw [hc]
  rw [← Finset.sum_filter]
  have hf : (Finset.Icc 1 L).filter (fun m ↦ m ≤ L / n) = Finset.Icc 1 (L / n) := by
    ext m
    simp only [Finset.mem_filter, Finset.mem_Icc]
    constructor
    · rintro ⟨⟨hm, _⟩, hh⟩
      exact ⟨hm, hh⟩
    · rintro ⟨hm, hh⟩
      exact ⟨⟨hm, hh.trans (Nat.div_le_self L n)⟩, hh⟩
  rw [hf, ← Finset.sum_mul]
  unfold pairedEtaArithmeticHarmonicPrefix
  ring

/-- The actual signed arithmetic residual equals its complete quotient-harmonic sum and original endpoint correction, with no restriction placing the physical cell below the arithmetic cutoff. -/
theorem pairedEtaMoebiusArithmeticCellResidual_eq_quotients (M L : ℕ) (w : ℕ → ℝ) :
    pairedEtaMoebiusArithmeticCellResidual M w L = (if L = 1 then 1 else 0) -
      (∑ n ∈ Finset.Icc 1 M, ((μ n : ℝ) * w n / n) * pairedEtaArithmeticHarmonicPrefix (L / n)) +
      pairedEtaMoebiusArithmeticHarmonic M w * pairedEtaArithmeticHarmonicPrefix L := by
  unfold pairedEtaMoebiusArithmeticCellResidual pairedEtaMoebiusArithmeticCellValue
  rw [sum_pairedEtaMoebiusArithmeticDivisor_div_eq_quotients]
  ring

/-- The original logarithmic constants cancel exactly, leaving every Möbius sign, quotient parity, positive amplitude, and endpoint correction in the actual residual. -/
theorem pairedEtaMoebiusArithmeticCellResidual_eq_signed_quotient_amplitudes
    (M L : ℕ) (w : ℕ → ℝ) :
    pairedEtaMoebiusArithmeticCellResidual M w L = (if L = 1 then 1 else 0) +
      pairedEtaMoebiusArithmeticHarmonic M w * (pairedEtaDirichletSign L : ℝ) * etaAlternatingHarmonicAmplitude L -
      ∑ n ∈ Finset.Icc 1 M, ((μ n : ℝ) * w n / n) *
        (pairedEtaDirichletSign (L / n) : ℝ) * etaAlternatingHarmonicAmplitude (L / n) := by
  have hH (n : ℕ) : pairedEtaArithmeticHarmonicPrefix n = Real.log 2 +
      (pairedEtaDirichletSign n : ℝ) * etaAlternatingHarmonicAmplitude n := by
    linarith [pairedEtaArithmeticHarmonicPrefix_sub_log_two n]
  rw [pairedEtaMoebiusArithmeticCellResidual_eq_quotients]
  simp_rw [hH, mul_add, Finset.sum_add_distrib, ← Finset.sum_mul]
  unfold pairedEtaMoebiusArithmeticHarmonic
  simp_rw [mul_assoc]
  ring

end

end RiemannGaussian
