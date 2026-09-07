import RiemannGaussian.EtaMoebiusArithmeticEnergy

/-!
# Exact logarithmic Möbius cancellation inside the arithmetic cutoff

Before the cutoff, the full Möbius-eta divisor convolution cancels to its
two original source coefficients. The logarithmic taper leaves a signed
logarithmic divisor correction. Combining this with the actual cell
identity isolates the precise remaining arithmetic residual on that range.
The exterior cells beyond the cutoff are not removed from the full energy.
-/

open Complex
open scoped ArithmeticFunction.Moebius

namespace RiemannGaussian

noncomputable section

/-- The signed logarithmic divisor convolution, retaining both the Möbius sign and the actual eta parity of the complementary divisor. -/
def pairedEtaMoebiusLogDivisor (l : ℕ) : ℝ :=
  ∑ p ∈ l.divisorsAntidiagonal,
    (μ p.1 : ℝ) * Real.log p.1 * (pairedEtaDirichletSign p.2 : ℝ)

/-- The complete normalized signed logarithmic divisor correction on an original arithmetic cell. -/
def pairedEtaMoebiusLogCellCorrection (L : ℕ) : ℝ :=
  ∑ l ∈ Finset.Icc 1 L, pairedEtaMoebiusLogDivisor l / l

private theorem real_moebius_eta_source {l : ℕ} (hl : 1 ≤ l) :
    (∑ p ∈ l.divisorsAntidiagonal, (μ p.1 : ℝ) * (pairedEtaDirichletSign p.2 : ℝ)) =
      (if l = 1 then 1 else 0) - 2 * (if l = 2 then 1 else 0) := by
  have h := sum_moebius_mul_pairedEtaDirichletSign l hl
  unfold pairedEtaDyadicDirichletSource at h
  exact_mod_cast h

/-- Up to the original arithmetic cutoff, the exact logarithmic divisor coefficient is the two-term eta source minus its signed logarithmic correction. -/
theorem pairedEtaMoebiusArithmeticDivisor_log_eq {M l : ℕ} (hM : 1 < M)
    (hl : l ∈ Finset.Icc 1 M) :
    pairedEtaMoebiusArithmeticDivisor M (pairedEtaMoebiusTrialLogWeight M) l =
      ((if l = 1 then 1 else 0) - 2 * (if l = 2 then 1 else 0)) -
        pairedEtaMoebiusLogDivisor l / Real.log M := by
  calc
    _ = ∑ p ∈ l.divisorsAntidiagonal,
        ((μ p.1 : ℝ) * (pairedEtaDirichletSign p.2 : ℝ) -
          ((μ p.1 : ℝ) * Real.log p.1 * (pairedEtaDirichletSign p.2 : ℝ)) / Real.log M) := by
      apply Finset.sum_congr rfl
      intro p hp
      have hp1 : p.1 ≤ l := Nat.le_of_dvd (Finset.mem_Icc.mp hl).1
        ⟨p.2, (Nat.mem_divisorsAntidiagonal.mp hp).1.symm⟩
      rw [if_pos (hp1.trans (Finset.mem_Icc.mp hl).2)]
      simp only [pairedEtaMoebiusTrialLogWeight, if_pos hM]
      ring
    _ = _ := by
      rw [Finset.sum_sub_distrib, ← Finset.sum_div, real_moebius_eta_source (Finset.mem_Icc.mp hl).1]
      rfl

private theorem eta_source_harmonic_prefix {L : ℕ} (hL : 1 ≤ L) :
    (∑ l ∈ Finset.Icc 1 L,
      (((if l = 1 then 1 else 0) - 2 * (if l = 2 then 1 else 0)) : ℝ) / l) =
      if L = 1 then 1 else 0 := by
  by_cases hL1 : L = 1
  · subst L
    norm_num
  · have hL2 : 2 ≤ L := by omega
    simp only [sub_div, mul_div_assoc, ite_div, zero_div, Finset.sum_sub_distrib,
      ← Finset.mul_sum, Finset.sum_ite_eq']
    norm_num [Finset.mem_Icc, hL, hL2, hL1]

/-- The complete logarithmic divisor prefix cancels the original target source exactly, leaving its signed logarithmic arithmetic correction. -/
theorem sum_pairedEtaMoebiusArithmeticDivisor_log_div {M L : ℕ} (hM : 1 < M)
    (hL : 1 ≤ L) (hLM : L ≤ M) :
    (∑ l ∈ Finset.Icc 1 L,
      pairedEtaMoebiusArithmeticDivisor M (pairedEtaMoebiusTrialLogWeight M) l / l) =
      (if L = 1 then 1 else 0) - pairedEtaMoebiusLogCellCorrection L / Real.log M := by
  calc
    _ = ∑ l ∈ Finset.Icc 1 L,
        ((((if l = 1 then 1 else 0) - 2 * (if l = 2 then 1 else 0)) : ℝ) / l -
          (pairedEtaMoebiusLogDivisor l / l) / Real.log M) := by
      apply Finset.sum_congr rfl
      intro l hl
      rw [pairedEtaMoebiusArithmeticDivisor_log_eq hM
        (Finset.mem_Icc.mpr ⟨(Finset.mem_Icc.mp hl).1, (Finset.mem_Icc.mp hl).2.trans hLM⟩)]
      ring
    _ = _ := by
      rw [Finset.sum_sub_distrib, ← Finset.sum_div, eta_source_harmonic_prefix hL]
      rfl

/-- On every cell up to the arithmetic cutoff, the original signed residual is exactly its harmonic endpoint correction plus the logarithmic divisor correction, before squaring or taking absolute values. -/
theorem pairedEtaMoebiusArithmeticCellResidual_log_eq {M L : ℕ} (hM : 1 < M)
    (hL : 1 ≤ L) (hLM : L ≤ M) :
    pairedEtaMoebiusArithmeticCellResidual M (pairedEtaMoebiusTrialLogWeight M) L =
      pairedEtaMoebiusLogHarmonic M * pairedEtaArithmeticHarmonicPrefix L +
        pairedEtaMoebiusLogCellCorrection L / Real.log M := by
  unfold pairedEtaMoebiusArithmeticCellResidual pairedEtaMoebiusArithmeticCellValue
  rw [sum_pairedEtaMoebiusArithmeticDivisor_log_div hM hL hLM]
  change (if L = 1 then 1 else 0) -
    ((if L = 1 then 1 else 0) - pairedEtaMoebiusLogCellCorrection L / Real.log M -
      pairedEtaMoebiusLogHarmonic M * pairedEtaArithmeticHarmonicPrefix L) = _
  ring

end

end RiemannGaussian
