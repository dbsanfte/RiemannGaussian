import RiemannGaussian.EtaMoebiusBeurlingCells
import Mathlib.NumberTheory.Harmonic.EulerMascheroni

/-!
# An explicit inverse-logarithmic bound for the original normalization

Möbius inversion against the full unpaired harmonic prefix has value one.
Subtracting its logarithm and Euler constant retains an exact signed
quotient remainder. The elementary harmonic-number remainder then bounds
the actual logarithmic normalization by `5 / log M`. No cancellation
estimate at the critical exponent is assumed.
-/

open scoped ArithmeticFunction.Moebius

namespace RiemannGaussian

noncomputable section

/-- The original harmonic Möbius sum has a uniform elementary bound, including its empty prefix. -/
theorem abs_moebiusHarmonicPrefix_le_two (M : ℕ) : |moebiusHarmonicPrefix M| ≤ 2 := by
  rcases M.eq_zero_or_pos with rfl | hM
  · simp [moebiusHarmonicPrefix]
  have he := moebiusHarmonicPrefix_mul_cutoff M 1
  simp only [Nat.mul_one] at he
  rw [sum_moebius_mul_nat_div_eq_one hM] at he
  have hh : (M : ℝ) * |moebiusHarmonicPrefix M| ≤ 1 + M := by
    calc
      _ = |(M : ℝ) * moebiusHarmonicPrefix M| := by
        rw [abs_mul, show |(M : ℝ)| = M from abs_of_nonneg (Nat.cast_nonneg M)]
      _ = |1 + moebiusHarmonicRounding M 1| := congrArg abs he
      _ ≤ 1 + M := by
        have h := abs_add_le 1 (moebiusHarmonicRounding M 1)
        rw [abs_one] at h
        exact h.trans (add_le_add_right (abs_moebiusHarmonicRounding_le M 1) 1)
  have hMp : (1 : ℝ) ≤ M := by exact_mod_cast hM
  nlinarith

private theorem unpaired_eq_harmonic (L : ℕ) :
    etaUnpairedArithmeticHarmonicPrefix L = (harmonic L : ℝ) := by
  simp only [etaUnpairedArithmeticHarmonicPrefix, harmonic_eq_sum_Icc,
    Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast, one_div]

/-- The genuine finite Möbius convolution with the unpaired harmonic prefixes is exactly the unit coefficient. -/
theorem sum_moebius_div_mul_unpairedHarmonic_eq_one {M : ℕ} (hM : 0 < M) :
    (∑ n ∈ Finset.Icc 1 M, (μ n : ℝ) / n * etaUnpairedArithmeticHarmonicPrefix (M / n)) = 1 := by
  have he : (∑ l ∈ Finset.Icc 1 M, ∑ p ∈ l.divisorsAntidiagonal,
      (μ p.1 : ℝ) / p.1 * (1 / (p.2 : ℝ))) =
      ∑ d ∈ Finset.Icc 1 M, ∑ m ∈ Finset.Icc 1 (M / d), (μ d : ℝ) / d * (1 / (m : ℝ)) := by
    exact_mod_cast sum_Icc_divisorsAntidiagonal_eq_sum_divided_prefix M
      (fun d m ↦ ((μ d : ℝ) / d * (1 / (m : ℝ)) : ℂ))
  simp only [← Finset.mul_sum] at he
  change (∑ l ∈ Finset.Icc 1 M, ∑ p ∈ l.divisorsAntidiagonal,
    (μ p.1 : ℝ) / p.1 * (1 / (p.2 : ℝ))) =
    ∑ n ∈ Finset.Icc 1 M, (μ n : ℝ) / n * etaUnpairedArithmeticHarmonicPrefix (M / n) at he
  rw [← he]
  have hpoint (l : ℕ) :
      (∑ p ∈ l.divisorsAntidiagonal, (μ p.1 : ℝ) / p.1 * (1 / (p.2 : ℝ))) =
        if l = 1 then 1 else 0 := by
    calc
      _ = (∑ d ∈ l.divisors, (μ d : ℝ)) / l := by
        rw [← Nat.sum_divisorsAntidiagonal (fun d _ ↦ (μ d : ℝ)), Finset.sum_div]
        apply Finset.sum_congr rfl
        intro p hp
        have hprod : (p.1 : ℝ) * p.2 = l := by
          exact_mod_cast (Nat.mem_divisorsAntidiagonal.mp hp).1
        rw [div_mul_div_comm, mul_one, hprod]
      _ = _ := by
        have hm := ArithmeticFunction.coe_moebius_mul_coe_zeta (R := ℝ)
        have hv := congrArg (fun f : ArithmeticFunction ℝ ↦ f l) hm
        simp only [ArithmeticFunction.coe_mul_zeta_apply, ArithmeticFunction.intCoe_apply,
          ArithmeticFunction.one_apply] at hv
        rw [hv]
        split_ifs with h
        · subst l
          norm_num
        · simp
  simp_rw [hpoint]
  simp [Finset.sum_ite_eq', Finset.mem_Icc, hM.ne']

/-- The exact signed Euler remainder at each original divided cutoff. -/
def pairedEtaMoebiusLogEulerRemainder (M n : ℕ) : ℝ :=
  etaUnpairedArithmeticHarmonicPrefix (M / n) - Real.log ((M : ℝ) / n) - Real.eulerMascheroniConstant

/-- The full harmonic quotient remainder is bounded uniformly by its reciprocal physical scale. -/
theorem abs_pairedEtaMoebiusLogEulerRemainder_le {M n : ℕ} (hn : 0 < n) (hnM : n ≤ M) :
    |pairedEtaMoebiusLogEulerRemainder M n| ≤ 2 * n / (M : ℝ) := by
  have hM : 0 < M := hn.trans_le hnM
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hMR : (0 : ℝ) < M := by exact_mod_cast hM
  have hq : 1 ≤ M / n := (Nat.le_div_iff_mul_le hn).mpr (by simpa using hnM)
  have hqR : (1 : ℝ) ≤ (M / n : ℕ) := by exact_mod_cast hq
  have hqpos : (0 : ℝ) < (M / n : ℕ) := by linarith
  have hlo : ((M / n : ℕ) : ℝ) ≤ (M : ℝ) / n := by
    apply (le_div_iff₀ hnR).mpr
    exact_mod_cast Nat.div_mul_le_self M n
  have hhi : (M : ℝ) / n < (M / n : ℕ) + 1 := by
    apply (div_lt_iff₀ hnR).mpr
    simpa only [mul_comm] using (show (M : ℝ) < n * ((M / n : ℕ) + 1 : ℝ) by
      exact_mod_cast Nat.lt_mul_div_succ M hn)
  have hl := Real.log_le_log hqpos hlo
  have hu := Real.log_le_log (div_pos hMR hnR) hhi.le
  have hgamlo := (Real.eulerMascheroniSeq_lt_eulerMascheroniConstant (M / n)).le
  have hgamhi := (Real.eulerMascheroniConstant_lt_eulerMascheroniSeq' (M / n)).le
  simp only [Real.eulerMascheroniSeq, Real.eulerMascheroniSeq', if_neg (by omega : M / n ≠ 0)] at hgamlo hgamhi
  have hlogstep : Real.log ((M / n : ℕ) + 1 : ℝ) - Real.log (M / n : ℕ) ≤ 1 / ((M / n : ℕ) : ℝ) := by
    rw [← Real.log_div (by positivity) hqpos.ne']
    have h := Real.log_le_sub_one_of_pos
      (div_pos (by positivity : 0 < ((M / n : ℕ) + 1 : ℝ)) hqpos)
    calc
      _ ≤ (((M / n : ℕ) + 1 : ℝ) / (M / n : ℕ)) - 1 := h
      _ = _ := by field_simp; ring
  have herr : |pairedEtaMoebiusLogEulerRemainder M n| ≤ 1 / ((M / n : ℕ) : ℝ) := by
    rw [pairedEtaMoebiusLogEulerRemainder, unpaired_eq_harmonic, abs_le]
    constructor <;> linarith
  apply herr.trans
  apply (div_le_div_iff₀ hqpos hMR).mpr
  have hm : (M : ℝ) ≤ ((M / n : ℕ) + 1 : ℝ) * n := (div_le_iff₀ hnR).mp hhi.le
  nlinarith

/-- The actual logarithmic normalization is exactly its unit term, Euler correction, and complete signed quotient remainder. -/
theorem pairedEtaMoebiusLogHarmonic_mul_log_eq_euler {M : ℕ} (hM : 1 < M) :
    pairedEtaMoebiusLogHarmonic M * Real.log M = 1 - Real.eulerMascheroniConstant * moebiusHarmonicPrefix M -
      ∑ n ∈ Finset.Icc 1 M, (μ n : ℝ) / n * pairedEtaMoebiusLogEulerRemainder M n := by
  have he := sum_moebius_div_mul_unpairedHarmonic_eq_one (by omega : 0 < M)
  have hMR : (0 : ℝ) < M := by exact_mod_cast (by omega : 0 < M)
  have hl : Real.log (M : ℝ) ≠ 0 := (Real.log_pos (by exact_mod_cast hM)).ne'
  rw [← he, pairedEtaMoebiusLogHarmonic, moebiusHarmonicPrefix,
    Finset.sum_mul, Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro n hn
  have hnR : (0 : ℝ) < n := by exact_mod_cast (Finset.mem_Icc.mp hn).1
  simp only [pairedEtaMoebiusTrialLogWeight, if_pos hM, pairedEtaMoebiusLogEulerRemainder,
    Real.log_div hMR.ne' hnR.ne']
  field_simp
  ring

/-- The complete signed Euler correction has an explicit uniform absolute budget. -/
theorem abs_sum_moebius_logEulerRemainder_le {M : ℕ} (hM : 0 < M) :
    |∑ n ∈ Finset.Icc 1 M, (μ n : ℝ) / n * pairedEtaMoebiusLogEulerRemainder M n| ≤ 2 := by
  have hMR : (0 : ℝ) < M := by exact_mod_cast hM
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  calc
    _ ≤ ∑ _n ∈ Finset.Icc 1 M, 2 / (M : ℝ) := by
      apply Finset.sum_le_sum
      intro n hn
      have hnR : (0 : ℝ) < n := by exact_mod_cast (Finset.mem_Icc.mp hn).1
      rw [abs_mul, abs_div, abs_of_pos hnR]
      calc
        _ ≤ (1 / (n : ℝ)) * (2 * n / (M : ℝ)) := mul_le_mul
          (div_le_div_of_nonneg_right (abs_real_moebius_le_one n) hnR.le)
          (abs_pairedEtaMoebiusLogEulerRemainder_le (Finset.mem_Icc.mp hn).1 (Finset.mem_Icc.mp hn).2)
          (abs_nonneg _) (by positivity)
        _ = _ := by field_simp
    _ = _ := by simp; field_simp

/-- The exact logarithmic family has a uniform inverse-logarithmic normalization bound at every nondegenerate cutoff. -/
theorem abs_pairedEtaMoebiusLogHarmonic_le_five_div_log {M : ℕ} (hM : 1 < M) :
    |pairedEtaMoebiusLogHarmonic M| ≤ 5 / Real.log M := by
  have hl : 0 < Real.log (M : ℝ) := Real.log_pos (by exact_mod_cast hM)
  have hg : |Real.eulerMascheroniConstant| ≤ 1 := by
    rw [abs_le]
    constructor <;> linarith [Real.one_half_lt_eulerMascheroniConstant,
      Real.eulerMascheroniConstant_lt_two_thirds]
  have hp : |Real.eulerMascheroniConstant * moebiusHarmonicPrefix M| ≤ 2 := by
    rw [abs_mul]
    exact (mul_le_mul hg (abs_moebiusHarmonicPrefix_le_two M) (abs_nonneg _) (by norm_num)).trans_eq (by ring)
  apply (le_div_iff₀ hl).mpr
  calc
    _ = |pairedEtaMoebiusLogHarmonic M * Real.log M| := by rw [abs_mul, abs_of_pos hl]
    _ = _ := congrArg abs (pairedEtaMoebiusLogHarmonic_mul_log_eq_euler hM)
    _ ≤ |1 - Real.eulerMascheroniConstant * moebiusHarmonicPrefix M| +
        |∑ n ∈ Finset.Icc 1 M, (μ n : ℝ) / n * pairedEtaMoebiusLogEulerRemainder M n| := abs_sub _ _
    _ ≤ (1 + 2) + 2 := add_le_add
      ((abs_sub _ _).trans (by simpa only [abs_one] using add_le_add_right hp 1))
      (abs_sum_moebius_logEulerRemainder_le (by omega))
    _ = _ := by norm_num

end

end RiemannGaussian
