import RiemannGaussian.EtaMoebiusPrimeArithmetic
import RiemannGaussian.EtaMoebiusArithmeticTail

/-!
# The exact prime variance and normalization cost inside the cutoff

Completing the square in the signed prime-shell formula isolates two
nonnegative contributions to the actual arithmetic residual. The first is
the least possible prime-shell variance under any scalar harmonic
correction; the second measures the actual Möbius correction's distance
from that optimum. The complete exterior sum remains an exact third term.
No decay of any of these growing terms is assumed or concluded here.
-/

namespace RiemannGaussian

noncomputable section

/-- The square mass of the actual alternating harmonic prefixes on the first `M` cells. -/
def pairedEtaArithmeticHarmonicSquareMass (M : ℕ) : ℝ :=
  ∑ n ∈ Finset.range M, pairedEtaArithmeticHarmonicPrefix (n + 1) ^ 2

/-- The signed cross moment between the actual harmonic prefixes and dyadic prime-power shells. -/
def pairedEtaPrimeHarmonicCrossMoment (M : ℕ) : ℝ :=
  ∑ n ∈ Finset.range M,
    pairedEtaArithmeticHarmonicPrefix (n + 1) * pairedEtaPrimeHarmonicShell (n + 1)

/-- The exact prime-shell variance after its optimal scalar harmonic correction. -/
def pairedEtaPrimeHarmonicVariance (M : ℕ) : ℝ :=
  (∑ n ∈ Finset.range M, pairedEtaPrimeHarmonicShell (n + 1) ^ 2) -
    pairedEtaPrimeHarmonicCrossMoment M ^ 2 / pairedEtaArithmeticHarmonicSquareMass M

/-- The precise scalar harmonic correction minimizing the residual squares inside the arithmetic cutoff. -/
def pairedEtaPrimeOptimalHarmonic (M : ℕ) : ℝ :=
  pairedEtaPrimeHarmonicCrossMoment M /
    (pairedEtaArithmeticHarmonicSquareMass M * Real.log M)

/-- The actual harmonic square mass is bounded below by its first physical cell, so its normalization is nonsingular. -/
theorem one_le_pairedEtaArithmeticHarmonicSquareMass {M : ℕ} (hM : 1 ≤ M) :
    1 ≤ pairedEtaArithmeticHarmonicSquareMass M := by
  have h := Finset.single_le_sum (fun n (_ : n ∈ Finset.range M) ↦
    sq_nonneg (pairedEtaArithmeticHarmonicPrefix (n + 1)))
    (show 0 ∈ Finset.range M by simp; omega)
  simpa [pairedEtaArithmeticHarmonicPrefix, pairedEtaDirichletSign,
    pairedEtaArithmeticHarmonicSquareMass] using h

/-- The prime variance is nonnegative by the actual finite harmonic-prime Cauchy-Schwarz inequality. -/
theorem pairedEtaPrimeHarmonicVariance_nonneg (M : ℕ) :
    0 ≤ pairedEtaPrimeHarmonicVariance M := by
  rcases M.eq_zero_or_pos with rfl | hM
  · simp [pairedEtaPrimeHarmonicVariance, pairedEtaPrimeHarmonicCrossMoment,
      pairedEtaArithmeticHarmonicSquareMass]
  · have hA : 0 < pairedEtaArithmeticHarmonicSquareMass M :=
      lt_of_lt_of_le (by norm_num) (one_le_pairedEtaArithmeticHarmonicSquareMass hM)
    apply sub_nonneg.mpr
    apply (div_le_iff₀ hA).mpr
    have h := Finset.sum_mul_sq_le_sq_mul_sq (Finset.range M)
      (fun n ↦ pairedEtaArithmeticHarmonicPrefix (n + 1))
      (fun n ↦ pairedEtaPrimeHarmonicShell (n + 1))
    simpa only [pairedEtaPrimeHarmonicCrossMoment, pairedEtaArithmeticHarmonicSquareMass,
      mul_comm] using h

private theorem sum_square_expansion {ι : Type*} (s : Finset ι) (u v : ι → ℝ) (p l : ℝ) :
    (∑ i ∈ s, (p * u i - v i / l) ^ 2) =
      p ^ 2 * (∑ i ∈ s, u i ^ 2) - (2 * p / l) * (∑ i ∈ s, u i * v i) +
        (∑ i ∈ s, v i ^ 2) / l ^ 2 := by
  calc
    _ = ∑ i ∈ s, (p ^ 2 * u i ^ 2 - (2 * p / l) * (u i * v i) + v i ^ 2 / l ^ 2) := by
      apply Finset.sum_congr rfl
      intro i _
      ring
    _ = _ := by rw [Finset.sum_add_distrib, Finset.sum_sub_distrib,
      ← Finset.mul_sum, ← Finset.mul_sum, ← Finset.sum_div]

/-- The actual logarithmic residual on all cells up to `M` is exactly its irreducible prime variance plus the square cost of its actual Möbius harmonic correction. -/
theorem pairedEtaMoebiusArithmeticSquarePrefix_eq_primeVariance {M : ℕ} (hM : 1 < M) :
    pairedEtaMoebiusArithmeticSquarePrefix M M (pairedEtaMoebiusTrialLogWeight M) =
      pairedEtaPrimeHarmonicVariance M / (Real.log M) ^ 2 +
        pairedEtaArithmeticHarmonicSquareMass M *
          (pairedEtaMoebiusLogHarmonic M - pairedEtaPrimeOptimalHarmonic M) ^ 2 := by
  have hA : pairedEtaArithmeticHarmonicSquareMass M ≠ 0 :=
    (lt_of_lt_of_le (by norm_num) (one_le_pairedEtaArithmeticHarmonicSquareMass (by omega : 1 ≤ M))).ne'
  have hl : Real.log (M : ℝ) ≠ 0 := (Real.log_pos (by exact_mod_cast hM)).ne'
  have he : pairedEtaMoebiusArithmeticSquarePrefix M M (pairedEtaMoebiusTrialLogWeight M) =
      ∑ n ∈ Finset.range M, (pairedEtaMoebiusLogHarmonic M *
        pairedEtaArithmeticHarmonicPrefix (n + 1) - pairedEtaPrimeHarmonicShell (n + 1) / Real.log M) ^ 2 := by
    apply Finset.sum_congr rfl
    intro n hn
    rw [pairedEtaMoebiusArithmeticCellResidual_log_eq_primeShell hM (by omega)
      (by have := Finset.mem_range.mp hn; omega)]
  rw [he, sum_square_expansion]
  change pairedEtaMoebiusLogHarmonic M ^ 2 * pairedEtaArithmeticHarmonicSquareMass M -
    (2 * pairedEtaMoebiusLogHarmonic M / Real.log M) * pairedEtaPrimeHarmonicCrossMoment M +
    (∑ n ∈ Finset.range M, pairedEtaPrimeHarmonicShell (n + 1) ^ 2) / Real.log M ^ 2 = _
  unfold pairedEtaPrimeHarmonicVariance pairedEtaPrimeOptimalHarmonic
  field_simp
  ring

/-- The full actual residual is exactly the prime variance, the actual normalization cost, and every exterior arithmetic square; no exterior estimate or decay hypothesis is discarded. -/
theorem pairedEtaMoebiusContinuumResidualEnergy_eq_primeVariance_add_exterior {M : ℕ}
    (hM : 1 < M) :
    pairedEtaMoebiusContinuumResidualEnergy M (pairedEtaMoebiusTrialLogWeight M) =
      pairedEtaPrimeHarmonicVariance M / (Real.log M) ^ 2 +
        pairedEtaArithmeticHarmonicSquareMass M *
          (pairedEtaMoebiusLogHarmonic M - pairedEtaPrimeOptimalHarmonic M) ^ 2 +
      pairedEtaMoebiusArithmeticSquareTail M M (pairedEtaMoebiusTrialLogWeight M) := by
  rw [pairedEtaMoebiusContinuumResidualEnergy_eq_prefix_add_tail M M
    (fun _ hn ↦ abs_pairedEtaMoebiusTrialLogWeight_le hn),
    pairedEtaMoebiusArithmeticSquarePrefix_eq_primeVariance hM]

/-- No scalar adjustment of the harmonic correction can remove the prime variance appearing in the actual full residual. -/
theorem pairedEtaPrimeHarmonicVariance_div_log_sq_le_residual {M : ℕ} (hM : 1 < M) :
    pairedEtaPrimeHarmonicVariance M / (Real.log M) ^ 2 ≤
      pairedEtaMoebiusContinuumResidualEnergy M (pairedEtaMoebiusTrialLogWeight M) := by
  rw [pairedEtaMoebiusContinuumResidualEnergy_eq_primeVariance_add_exterior hM]
  have hA : 0 ≤ pairedEtaArithmeticHarmonicSquareMass M := Finset.sum_nonneg (fun _ _ ↦ sq_nonneg _)
  have htail : 0 ≤ pairedEtaMoebiusArithmeticSquareTail M M (pairedEtaMoebiusTrialLogWeight M) :=
    tsum_nonneg (fun _ ↦ sq_nonneg _)
  linarith [mul_nonneg hA (sq_nonneg (pairedEtaMoebiusLogHarmonic M - pairedEtaPrimeOptimalHarmonic M))]

/-- The actual harmonic correction's weighted distance from the exact prime optimum is a nonnegative part of the full residual. -/
theorem pairedEtaPrimeNormalizationCost_le_residual {M : ℕ} (hM : 1 < M) :
    pairedEtaArithmeticHarmonicSquareMass M *
        (pairedEtaMoebiusLogHarmonic M - pairedEtaPrimeOptimalHarmonic M) ^ 2 ≤
      pairedEtaMoebiusContinuumResidualEnergy M (pairedEtaMoebiusTrialLogWeight M) := by
  rw [pairedEtaMoebiusContinuumResidualEnergy_eq_primeVariance_add_exterior hM]
  have hV := div_nonneg (pairedEtaPrimeHarmonicVariance_nonneg M) (sq_nonneg (Real.log M))
  have htail : 0 ≤ pairedEtaMoebiusArithmeticSquareTail M M (pairedEtaMoebiusTrialLogWeight M) :=
    tsum_nonneg (fun _ ↦ sq_nonneg _)
  linarith

end

end RiemannGaussian
