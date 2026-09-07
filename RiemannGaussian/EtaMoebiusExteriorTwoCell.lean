import RiemannGaussian.EtaMoebiusPrimeArithmetic
import RiemannGaussian.EtaMoebiusArithmeticEnergy

/-!
# A scale check for proposed exterior parity estimates

Two actual exterior cells already have a positive inverse-logarithmic
square cost for the specified logarithmic coefficient family, regardless
of the value of its scalar harmonic correction. This constrains possible
rates in the parity endgame; it does not obstruct convergence to zero.
-/

namespace RiemannGaussian

noncomputable section

private theorem harmonic_two : pairedEtaArithmeticHarmonicPrefix 2 = 1 / 2 := by
  norm_num [pairedEtaArithmeticHarmonicPrefix, pairedEtaDirichletSign, Finset.sum_Icc_succ_top]

private theorem harmonic_three : pairedEtaArithmeticHarmonicPrefix 3 = 5 / 6 := by
  norm_num [pairedEtaArithmeticHarmonicPrefix, pairedEtaDirichletSign, Finset.sum_Icc_succ_top, Nat.even_iff]

private theorem prime_shell_two : pairedEtaPrimeHarmonicShell 2 = Real.log 2 / 2 := by
  norm_num [pairedEtaPrimeHarmonicShell, Finset.sum_Icc_succ_top,
    ArithmeticFunction.vonMangoldt_apply_prime Nat.prime_two]

private theorem prime_shell_three : pairedEtaPrimeHarmonicShell 3 = Real.log 2 / 2 + Real.log 3 / 3 := by
  norm_num [pairedEtaPrimeHarmonicShell, Finset.sum_Icc_succ_top,
    ArithmeticFunction.vonMangoldt_apply_prime Nat.prime_two,
    ArithmeticFunction.vonMangoldt_apply_prime Nat.prime_three]

/-- The original exterior cells `(2,3]` and `(3,4]` have a strictly positive inverse-logarithmic lower rate; a scalar harmonic adjustment cannot cancel both. -/
theorem pairedEtaMoebiusArithmeticExterior_twoCell_lower {M : ℕ} (hM : 3 ≤ M) :
    (Real.log 3 - Real.log 2) ^ 2 / (34 * (Real.log M) ^ 2) ≤
      pairedEtaMoebiusArithmeticCellResidual M (pairedEtaMoebiusTrialLogWeight M) 2 ^ 2 +
      pairedEtaMoebiusArithmeticCellResidual M (pairedEtaMoebiusTrialLogWeight M) 3 ^ 2 := by
  have hl : Real.log (M : ℝ) ≠ 0 := (Real.log_pos (by exact_mod_cast (show 1 < M by omega))).ne'
  rw [pairedEtaMoebiusArithmeticCellResidual_log_eq_primeShell (by omega) (by norm_num) (by omega),
    pairedEtaMoebiusArithmeticCellResidual_log_eq_primeShell (by omega) (by norm_num) hM,
    harmonic_two, harmonic_three, prime_shell_two, prime_shell_three]
  have h := sq_nonneg (3 * (pairedEtaMoebiusLogHarmonic M / 2 - Real.log 2 / (2 * Real.log M)) +
    5 * (5 * pairedEtaMoebiusLogHarmonic M / 6 - (Real.log 2 / 2 + Real.log 3 / 3) / Real.log M))
  field_simp at h ⊢
  nlinarith

/-- The fixed coefficient in the original two-cell lower bound is strictly positive. -/
theorem pairedEtaMoebiusArithmeticExterior_twoCell_constant_pos :
    0 < (Real.log 3 - Real.log 2) ^ 2 / 34 := by
  have hl : Real.log 2 < Real.log 3 := Real.log_lt_log (by norm_num) (by norm_num)
  exact div_pos (sq_pos_of_pos (sub_pos.mpr hl)) (by norm_num)

end

end RiemannGaussian
