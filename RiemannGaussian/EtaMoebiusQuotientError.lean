import RiemannGaussian.EtaMoebiusQuotientParity
import RiemannGaussian.EtaWeightedDivisorSampling

/-!
# Uniform amplitude error for the actual signed quotient family

The signed arithmetic residual is approximated by the existing quotient
parity family with a common physical amplitude. The exact difference is
retained before bounding only the amplitude error. This is the bridge
needed to apply the already proved Fourier window estimate to the actual
residual in its valid quadratic range.
-/

open scoped ArithmeticFunction.Moebius

namespace RiemannGaussian

noncomputable section

/-- The common-amplitude part of the actual residual, retaining its signed quotient family and original harmonic endpoint. -/
def pairedEtaMoebiusQuotientLeadingTerm (M : ℕ) (w : ℕ → ℝ) (L : ℕ) : ℝ :=
  (pairedEtaMoebiusArithmeticHarmonic M w * (pairedEtaDirichletSign L : ℝ) -
    (pairedEtaWeightedDivisorParityFamily (fun n ↦ (μ n : ℝ) * w n) L M).re) / (2 * L)

private theorem abs_sign_real (L : ℕ) : |(pairedEtaDirichletSign L : ℝ)| = 1 := by
  exact_mod_cast abs_pairedEtaDirichletSign L

private theorem abs_weight_le {M : ℕ} {w : ℕ → ℝ}
    (hw : ∀ n ∈ Finset.Icc 1 M, |w n| ≤ 1) (n : ℕ) (hn : n ∈ Finset.Icc 1 M) :
    |(μ n : ℝ) * w n| ≤ 1 := by
  rw [abs_mul]
  exact (mul_le_mul (abs_real_moebius_le_one n) (hw n hn) (abs_nonneg _) (by norm_num)).trans_eq (by norm_num)

/-- Bounded original weights give a uniform bound on the literal harmonic endpoint correction. -/
theorem abs_pairedEtaMoebiusArithmeticHarmonic_le {M : ℕ} {w : ℕ → ℝ}
    (hw : ∀ n ∈ Finset.Icc 1 M, |w n| ≤ 1) :
    |pairedEtaMoebiusArithmeticHarmonic M w| ≤ M := by
  unfold pairedEtaMoebiusArithmeticHarmonic
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  calc
    _ ≤ ∑ _n ∈ Finset.Icc 1 M, (1 : ℝ) := by
      apply Finset.sum_le_sum
      intro n hn
      have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast (Finset.mem_Icc.mp hn).1
      rw [abs_div, show |(n : ℝ)| = n from abs_of_nonneg (Nat.cast_nonneg n)]
      exact (div_le_one (by linarith : (0 : ℝ) < n)).mpr ((abs_weight_le hw n hn).trans hn1)
    _ = _ := by simp

/-- The exact common-amplitude error retains every original arithmetic coefficient, quotient sign, and endpoint amplitude. -/
theorem pairedEtaMoebiusArithmeticCellResidual_sub_quotientLeading_eq (M L : ℕ) (w : ℕ → ℝ) :
    pairedEtaMoebiusArithmeticCellResidual M w L - pairedEtaMoebiusQuotientLeadingTerm M w L =
      (if L = 1 then 1 else 0) +
      pairedEtaMoebiusArithmeticHarmonic M w * (pairedEtaDirichletSign L : ℝ) *
        (etaAlternatingHarmonicAmplitude L - 1 / (2 * L)) -
      ∑ n ∈ Finset.Icc 1 M, (μ n : ℝ) * w n * (pairedEtaDirichletSign (L / n) : ℝ) *
        (etaAlternatingHarmonicAmplitude (L / n) / n - 1 / (2 * L)) := by
  rw [pairedEtaMoebiusArithmeticCellResidual_eq_signed_quotient_amplitudes,
    pairedEtaMoebiusQuotientLeadingTerm, pairedEtaWeightedDivisorParityFamily_eq_real]
  simp only [Complex.ofReal_re, mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul]
  have hs : (∑ n ∈ Finset.Icc 1 M, ((μ n : ℝ) * w n / n) *
      (pairedEtaDirichletSign (L / n) : ℝ) * etaAlternatingHarmonicAmplitude (L / n)) =
      ∑ n ∈ Finset.Icc 1 M, (μ n : ℝ) * w n * (pairedEtaDirichletSign (L / n) : ℝ) *
        (etaAlternatingHarmonicAmplitude (L / n) / n) := by
    apply Finset.sum_congr rfl
    intro n _
    ring
  rw [hs]
  ring

/-- The amplitude error for every exterior physical cell is uniformly inverse-square, without estimating the signed leading parity family by absolute values. -/
theorem abs_pairedEtaMoebiusArithmeticCellResidual_sub_quotientLeading_le
    {M L : ℕ} (hM : 1 ≤ M) (hL : 2 ≤ L) {w : ℕ → ℝ}
    (hw : ∀ n ∈ Finset.Icc 1 M, |w n| ≤ 1) :
    |pairedEtaMoebiusArithmeticCellResidual M w L - pairedEtaMoebiusQuotientLeadingTerm M w L| ≤
      (M : ℝ) ^ 2 / (L : ℝ) ^ 2 := by
  have hLp : (0 : ℝ) < L := by exact_mod_cast (show 0 < L by omega)
  have hMp : (1 : ℝ) ≤ M := by exact_mod_cast hM
  have hamp : |etaAlternatingHarmonicAmplitude L - 1 / (2 * (L : ℝ))| ≤ 1 / (2 * (L : ℝ) ^ 2) := by
    simpa using etaAlternatingHarmonicAmplitude_quotient_error_le (L := L) (n := 1) (by omega) (by decide)
  have hend : |pairedEtaMoebiusArithmeticHarmonic M w * (pairedEtaDirichletSign L : ℝ) *
      (etaAlternatingHarmonicAmplitude L - 1 / (2 * L))| ≤ M / (2 * (L : ℝ) ^ 2) := by
    rw [abs_mul, abs_mul, abs_sign_real, mul_one]
    calc
      _ ≤ (M : ℝ) * (1 / (2 * (L : ℝ) ^ 2)) :=
        mul_le_mul (abs_pairedEtaMoebiusArithmeticHarmonic_le hw) hamp (abs_nonneg _) (Nat.cast_nonneg M)
      _ = _ := by ring
  have hsum : |∑ n ∈ Finset.Icc 1 M, (μ n : ℝ) * w n * (pairedEtaDirichletSign (L / n) : ℝ) *
      (etaAlternatingHarmonicAmplitude (L / n) / n - 1 / (2 * L))| ≤
      (M : ℝ) ^ 2 / (2 * (L : ℝ) ^ 2) := by
    apply (Finset.abs_sum_le_sum_abs _ _).trans
    calc
      _ ≤ ∑ _n ∈ Finset.Icc 1 M, (M : ℝ) / (2 * (L : ℝ) ^ 2) := by
        apply Finset.sum_le_sum
        intro n hn
        have hnp : 0 < n := (Finset.mem_Icc.mp hn).1
        have hnM : (n : ℝ) ≤ M := by exact_mod_cast (Finset.mem_Icc.mp hn).2
        rw [abs_mul, abs_mul, abs_sign_real, mul_one]
        calc
          _ ≤ 1 * (n / (2 * (L : ℝ) ^ 2)) :=
            mul_le_mul (abs_weight_le hw n hn) (etaAlternatingHarmonicAmplitude_quotient_error_le (by omega) hnp)
              (abs_nonneg _) (by norm_num)
          _ ≤ _ := by simpa only [one_mul] using div_le_div_of_nonneg_right hnM (by positivity : 0 ≤ 2 * (L : ℝ) ^ 2)
      _ = _ := by simp; ring
  rw [pairedEtaMoebiusArithmeticCellResidual_sub_quotientLeading_eq, if_neg (by omega : L ≠ 1), zero_add]
  apply (abs_sub _ _).trans ((add_le_add hend hsum).trans _)
  calc
    _ = ((M : ℝ) + M ^ 2) / (2 * (L : ℝ) ^ 2) := by ring
    _ ≤ _ := by
      apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
      have hm : (M : ℝ) ≤ M ^ 2 := by nlinarith
      nlinarith [mul_le_mul_of_nonneg_right hm (sq_nonneg (L : ℝ))]

/-- The actual residual square is bounded by the original signed quotient-family square, the harmonic endpoint, and the proved amplitude error. -/
theorem pairedEtaMoebiusArithmeticCellResidual_sq_le_quotientFamily
    {M L : ℕ} (hM : 1 ≤ M) (hL : 2 ≤ L) {w : ℕ → ℝ}
    (hw : ∀ n ∈ Finset.Icc 1 M, |w n| ≤ 1) :
    pairedEtaMoebiusArithmeticCellResidual M w L ^ 2 ≤
      (pairedEtaMoebiusArithmeticHarmonic M w ^ 2 +
        ‖pairedEtaWeightedDivisorParityFamily (fun n ↦ (μ n : ℝ) * w n) L M‖ ^ 2) / (L : ℝ) ^ 2 +
      2 * (M : ℝ) ^ 4 / (L : ℝ) ^ 4 := by
  have hLp : (0 : ℝ) < L := by exact_mod_cast (show 0 < L by omega)
  let p := pairedEtaMoebiusArithmeticHarmonic M w
  let s := (pairedEtaWeightedDivisorParityFamily (fun n ↦ (μ n : ℝ) * w n) L M).re
  have hs : s ^ 2 = ‖pairedEtaWeightedDivisorParityFamily (fun n ↦ (μ n : ℝ) * w n) L M‖ ^ 2 := by
    dsimp only [s]
    rw [pairedEtaWeightedDivisorParityFamily_eq_real]
    simp only [Complex.ofReal_re, Complex.norm_real, Real.norm_eq_abs, sq_abs]
  have hp : (p * (pairedEtaDirichletSign L : ℝ)) ^ 2 = p ^ 2 := by
    rw [mul_pow, ← sq_abs (pairedEtaDirichletSign L : ℝ), abs_sign_real]
    ring
  have hlead : pairedEtaMoebiusQuotientLeadingTerm M w L ^ 2 ≤
      (p ^ 2 + ‖pairedEtaWeightedDivisorParityFamily (fun n ↦ (μ n : ℝ) * w n) L M‖ ^ 2) /
        (2 * (L : ℝ) ^ 2) := by
    calc
      _ = (p * (pairedEtaDirichletSign L : ℝ) - s) ^ 2 / (4 * (L : ℝ) ^ 2) := by
        unfold pairedEtaMoebiusQuotientLeadingTerm p s
        ring
      _ ≤ (2 * (p ^ 2 + s ^ 2)) / (4 * (L : ℝ) ^ 2) := by
        apply div_le_div_of_nonneg_right _ (by positivity)
        nlinarith [sq_nonneg (p * (pairedEtaDirichletSign L : ℝ) + s)]
      _ = _ := by rw [hs]; ring
  have herr := pow_le_pow_left₀ (abs_nonneg _)
    (abs_pairedEtaMoebiusArithmeticCellResidual_sub_quotientLeading_le hM hL hw) 2
  rw [sq_abs] at herr
  calc
    _ ≤ 2 * pairedEtaMoebiusQuotientLeadingTerm M w L ^ 2 +
        2 * (pairedEtaMoebiusArithmeticCellResidual M w L - pairedEtaMoebiusQuotientLeadingTerm M w L) ^ 2 := by
      nlinarith [sq_nonneg (pairedEtaMoebiusArithmeticCellResidual M w L - 2 * pairedEtaMoebiusQuotientLeadingTerm M w L)]
    _ ≤ 2 * ((p ^ 2 + ‖pairedEtaWeightedDivisorParityFamily (fun n ↦ (μ n : ℝ) * w n) L M‖ ^ 2) /
        (2 * (L : ℝ) ^ 2)) + 2 * ((M : ℝ) ^ 2 / (L : ℝ) ^ 2) ^ 2 := by linarith
    _ = _ := by dsimp [p]; ring

end

end RiemannGaussian
