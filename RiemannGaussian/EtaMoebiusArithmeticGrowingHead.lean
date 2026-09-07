import RiemannGaussian.EtaMoebiusLogHarmonicBound
import RiemannGaussian.EtaMoebiusArithmeticSamplingTail
import RiemannGaussian.EtaMoebiusPrimeArithmetic
import Mathlib.NumberTheory.Chebyshev

/-!
# Uniform decay on a growing initial arithmetic range

The exact prime-shell residual and the original normalization satisfy a
uniform inverse-logarithmic bound on every cell through `M`. Summing its
squares bounds any prefix of length `R ≤ M` by `484 R / log(M)^2`.
Consequently the unchanged prefix through `floor(log M)` tends to zero.
Together with the complete quadratic-tail theorem, this leaves precisely
the intervening growing band; that band is not asserted to decay.
-/

open Filter
open scoped Topology ArithmeticFunction.vonMangoldt

namespace RiemannGaussian

noncomputable section

private theorem psi_le_six_mul (L : ℕ) : Chebyshev.psi L ≤ 6 * L := by
  have h := Chebyshev.psi_le_const_mul_self (Nat.cast_nonneg (α := ℝ) L)
  have hlog : Real.log (4 : ℝ) ≤ 2 := by
    have htwo := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
    have he : Real.log (4 : ℝ) = 2 * Real.log 2 := by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
      norm_num
    rw [he]
    linarith
  nlinarith [mul_nonneg (sub_nonneg.mpr hlog) (Nat.cast_nonneg (α := ℝ) L)]

/-- The original prime-power shell is precisely its open-closed dyadic physical interval. -/
theorem pairedEtaPrimeHarmonicShell_eq_sum_Ioc (L : ℕ) :
    pairedEtaPrimeHarmonicShell L = ∑ n ∈ Finset.Ioc (L / 2) L, Λ n / n := by
  have hs : Finset.Icc 1 (L / 2) ⊆ Finset.Icc 1 L :=
    Finset.Icc_subset_Icc le_rfl (Nat.div_le_self L 2)
  have he : Finset.Icc 1 L \ Finset.Icc 1 (L / 2) = Finset.Ioc (L / 2) L := by
    ext n
    simp only [Finset.mem_sdiff, Finset.mem_Icc, Finset.mem_Ioc]
    omega
  have h := Finset.sum_sdiff (f := fun n : ℕ ↦ Λ n / (n : ℝ)) hs
  rw [he] at h
  exact (eq_sub_iff_add_eq.mpr h).symm

/-- Chebyshev's proved linear bound controls every actual harmonic prime shell by a uniform constant. -/
theorem pairedEtaPrimeHarmonicShell_bounds (L : ℕ) :
    0 ≤ pairedEtaPrimeHarmonicShell L ∧ pairedEtaPrimeHarmonicShell L ≤ 12 := by
  rw [pairedEtaPrimeHarmonicShell_eq_sum_Ioc]
  constructor
  · exact Finset.sum_nonneg (fun _ _ ↦ div_nonneg (by simp) (Nat.cast_nonneg _))
  · rcases L.eq_zero_or_pos with rfl | hL
    · simp
    have hLR : (0 : ℝ) < L := by exact_mod_cast hL
    have hsum : (∑ n ∈ Finset.Ioc (L / 2) L, Λ n) ≤ Chebyshev.psi L := by
      rw [Chebyshev.psi, Nat.floor_natCast]
      exact Finset.sum_le_sum_of_subset_of_nonneg
        (Finset.Ioc_subset_Ioc (Nat.zero_le _) le_rfl) (fun _ _ _ ↦ by simp)
    calc
      _ ≤ ∑ n ∈ Finset.Ioc (L / 2) L, (2 / (L : ℝ)) * Λ n := by
        apply Finset.sum_le_sum
        intro n hn
        have hnpos : 0 < n := lt_of_le_of_lt (Nat.zero_le _) (Finset.mem_Ioc.mp hn).1
        have hnR : (0 : ℝ) < n := by exact_mod_cast hnpos
        have hLn : (L : ℝ) ≤ 2 * n := by
          have hh := (Finset.mem_Ioc.mp hn).1
          exact_mod_cast (show L ≤ 2 * n by omega)
        have hi : 1 / (n : ℝ) ≤ 2 / (L : ℝ) := by
          apply (div_le_div_iff₀ hnR hLR).mpr
          simpa only [one_mul] using hLn
        simpa only [div_eq_mul_inv, one_mul, mul_comm, mul_one] using
          mul_le_mul_of_nonneg_right hi (show 0 ≤ Λ n by simp)
      _ = (2 / (L : ℝ)) * ∑ n ∈ Finset.Ioc (L / 2) L, Λ n := by rw [Finset.mul_sum]
      _ ≤ (2 / (L : ℝ)) * Chebyshev.psi L := mul_le_mul_of_nonneg_left hsum (by positivity)
      _ ≤ (2 / (L : ℝ)) * (6 * L) := mul_le_mul_of_nonneg_left (psi_le_six_mul L) (by positivity)
      _ = _ := by field_simp; ring

/-- The actual signed harmonic prefixes are uniformly bounded, including their empty prefix. -/
theorem abs_pairedEtaArithmeticHarmonicPrefix_le_two (L : ℕ) :
    |pairedEtaArithmeticHarmonicPrefix L| ≤ 2 := by
  have ha := etaAlternatingHarmonicAmplitude_bounds L
  have ha0 : 0 ≤ etaAlternatingHarmonicAmplitude L := le_trans (by positivity) ha.1
  have haup : etaAlternatingHarmonicAmplitude L ≤ 1 := by
    apply ha.2.trans
    have h1 : 1 / (2 * (L + 1 : ℝ)) ≤ 1 / 2 :=
      one_div_le_one_div_of_le (by norm_num) (by nlinarith [Nat.cast_nonneg (α := ℝ) L])
    have h2 : 1 / (2 * (L + 1 : ℝ) * (L + 2 : ℝ)) ≤ 1 / 2 :=
      one_div_le_one_div_of_le (by norm_num) (by nlinarith [Nat.cast_nonneg (α := ℝ) L])
    linarith
  have hs : |(pairedEtaDirichletSign L : ℝ)| = 1 := by
    unfold pairedEtaDirichletSign
    split_ifs <;> norm_num
  have hlog : |Real.log (2 : ℝ)| ≤ 1 := by
    rw [abs_of_nonneg (Real.log_nonneg (by norm_num))]
    have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
    norm_num at h
    exact h
  have he := pairedEtaArithmeticHarmonicPrefix_sub_log_two L
  calc
    _ = |Real.log 2 + (pairedEtaDirichletSign L : ℝ) * etaAlternatingHarmonicAmplitude L| := by congr 1; linarith
    _ ≤ |Real.log 2| + |(pairedEtaDirichletSign L : ℝ) * etaAlternatingHarmonicAmplitude L| := abs_add_le _ _
    _ ≤ 1 + 1 := by rw [abs_mul, hs, one_mul, abs_of_nonneg ha0]; exact add_le_add hlog haup
    _ = _ := by norm_num

/-- Every original logarithmic arithmetic residual up to its coefficient cutoff has a uniform inverse-logarithmic bound. -/
theorem abs_pairedEtaMoebiusArithmeticCellResidual_log_le {M L : ℕ}
    (hM : 1 < M) (hL : 1 ≤ L) (hLM : L ≤ M) :
    |pairedEtaMoebiusArithmeticCellResidual M (pairedEtaMoebiusTrialLogWeight M) L| ≤ 22 / Real.log M := by
  rw [pairedEtaMoebiusArithmeticCellResidual_log_eq_primeShell hM hL hLM]
  have hl : 0 < Real.log (M : ℝ) := Real.log_pos (by exact_mod_cast hM)
  apply (abs_sub _ _).trans
  rw [abs_mul, abs_div, abs_of_pos hl,
    abs_of_nonneg (pairedEtaPrimeHarmonicShell_bounds L).1]
  calc
    _ ≤ (5 / Real.log M) * 2 + 12 / Real.log M := add_le_add
      (mul_le_mul (abs_pairedEtaMoebiusLogHarmonic_le_five_div_log hM)
        (abs_pairedEtaArithmeticHarmonicPrefix_le_two L) (abs_nonneg _) (by positivity))
      (div_le_div_of_nonneg_right (pairedEtaPrimeHarmonicShell_bounds L).2 hl.le)
    _ = _ := by ring

/-- The unchanged square prefix has an explicit joint bound in its length and the actual arithmetic cutoff. -/
theorem pairedEtaMoebiusArithmeticSquarePrefix_le_log_bound {M R : ℕ}
    (hM : 1 < M) (hRM : R ≤ M) :
    pairedEtaMoebiusArithmeticSquarePrefix M R (pairedEtaMoebiusTrialLogWeight M) ≤
      484 * R / Real.log M ^ 2 := by
  calc
    _ ≤ ∑ _n ∈ Finset.range R, (22 / Real.log M) ^ 2 := by
      apply Finset.sum_le_sum
      intro n hn
      have h := pow_le_pow_left₀ (abs_nonneg _)
        (abs_pairedEtaMoebiusArithmeticCellResidual_log_le (L := n + 1) hM (by omega)
          (by have := Finset.mem_range.mp hn; omega)) 2
      simpa only [sq_abs] using h
    _ = _ := by simp; ring

/-- The literal lower cutoff of the newly controlled growing arithmetic prefix. -/
def pairedEtaMoebiusLogarithmicHeadCutoff (M : ℕ) : ℕ := ⌊Real.log M⌋₊

private theorem log_head_le_cutoff (M : ℕ) : pairedEtaMoebiusLogarithmicHeadCutoff M ≤ M := by
  apply Nat.floor_le_of_le
  rcases M.eq_zero_or_pos with rfl | hM
  · simp
  have hMR : (0 : ℝ) < M := by exact_mod_cast hM
  have h := Real.log_le_sub_one_of_pos hMR
  linarith

/-- The complete initial square sum through the literal logarithmic physical cutoff has an explicit vanishing allowance. -/
theorem pairedEtaMoebiusArithmeticSquarePrefix_logarithmic_le {M : ℕ} (hM : 1 < M) :
    pairedEtaMoebiusArithmeticSquarePrefix M (pairedEtaMoebiusLogarithmicHeadCutoff M)
      (pairedEtaMoebiusTrialLogWeight M) ≤ 484 / Real.log M := by
  have hl : 0 < Real.log (M : ℝ) := Real.log_pos (by exact_mod_cast hM)
  have hc : (pairedEtaMoebiusLogarithmicHeadCutoff M : ℝ) ≤ Real.log M := Nat.floor_le hl.le
  apply (pairedEtaMoebiusArithmeticSquarePrefix_le_log_bound hM (log_head_le_cutoff M)).trans
  calc
    _ ≤ 484 * Real.log M / Real.log M ^ 2 := div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_left hc (by norm_num)) (sq_nonneg _)
    _ = _ := by field_simp

/-- The controlled initial interval really grows without bound along the original arithmetic cutoffs. -/
theorem pairedEtaMoebiusLogarithmicHeadCutoff_tendsto_atTop :
    Tendsto pairedEtaMoebiusLogarithmicHeadCutoff atTop atTop := by
  exact tendsto_nat_floor_atTop.comp (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)

/-- The actual arithmetic square sum on the complete growing logarithmic head tends to zero, with no change of coefficient family. -/
theorem pairedEtaMoebiusArithmeticSquarePrefix_logarithmic_tendsto_zero :
    Tendsto (fun M : ℕ ↦ pairedEtaMoebiusArithmeticSquarePrefix M
      (pairedEtaMoebiusLogarithmicHeadCutoff M) (pairedEtaMoebiusTrialLogWeight M)) atTop (𝓝 0) := by
  have hz : Tendsto (fun M : ℕ ↦ 484 / Real.log M) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)
  apply squeeze_zero' (Eventually.of_forall (fun _ ↦ Finset.sum_nonneg (fun _ _ ↦ sq_nonneg _))) _ hz
  filter_upwards [eventually_gt_atTop 1] with M hM
  exact pairedEtaMoebiusArithmeticSquarePrefix_logarithmic_le hM

private theorem square_prefix_eq_Icc (M R : ℕ) (w : ℕ → ℝ) :
    pairedEtaMoebiusArithmeticSquarePrefix M R w =
      ∑ L ∈ Finset.Icc 1 R, pairedEtaMoebiusArithmeticCellResidual M w L ^ 2 := by
  rw [← Finset.Ico_add_one_right_eq_Icc, Finset.sum_Ico_eq_sum_range]
  simp only [Nat.add_sub_cancel, add_comm 1, pairedEtaMoebiusArithmeticSquarePrefix]

/-- The complete unchanged arithmetic band between the proved growing head and quadratic tail. -/
def pairedEtaMoebiusArithmeticMiddleEnergy (M : ℕ) : ℝ :=
  ∑ L ∈ Finset.Ioc (pairedEtaMoebiusLogarithmicHeadCutoff M) (M ^ 2),
    pairedEtaMoebiusArithmeticCellResidual M (pairedEtaMoebiusTrialLogWeight M) L ^ 2

/-- The complete continuum residual is exactly its growing logarithmic head, intervening signed arithmetic square sum, and full quadratic tail. -/
theorem pairedEtaMoebiusContinuumResidualEnergy_eq_head_middle_tail {M : ℕ} (hM : 1 ≤ M) :
    pairedEtaMoebiusContinuumResidualEnergy M (pairedEtaMoebiusTrialLogWeight M) =
      pairedEtaMoebiusArithmeticSquarePrefix M (pairedEtaMoebiusLogarithmicHeadCutoff M)
        (pairedEtaMoebiusTrialLogWeight M) + pairedEtaMoebiusArithmeticMiddleEnergy M +
      pairedEtaMoebiusArithmeticSquareTail M (M ^ 2) (pairedEtaMoebiusTrialLogWeight M) := by
  have hcut : pairedEtaMoebiusLogarithmicHeadCutoff M ≤ M ^ 2 :=
    (log_head_le_cutoff M).trans (by nlinarith)
  have hs : Finset.Icc 1 (pairedEtaMoebiusLogarithmicHeadCutoff M) ⊆ Finset.Icc 1 (M ^ 2) :=
    Finset.Icc_subset_Icc le_rfl hcut
  have he : Finset.Icc 1 (M ^ 2) \ Finset.Icc 1 (pairedEtaMoebiusLogarithmicHeadCutoff M) =
      Finset.Ioc (pairedEtaMoebiusLogarithmicHeadCutoff M) (M ^ 2) := by
    ext L
    simp only [Finset.mem_sdiff, Finset.mem_Icc, Finset.mem_Ioc]
    omega
  have h := Finset.sum_sdiff
    (f := fun L ↦ pairedEtaMoebiusArithmeticCellResidual M (pairedEtaMoebiusTrialLogWeight M) L ^ 2) hs
  rw [he, ← square_prefix_eq_Icc, ← square_prefix_eq_Icc] at h
  rw [pairedEtaMoebiusContinuumResidualEnergy_eq_prefix_add_tail M (M ^ 2)
    (fun _ hn ↦ abs_pairedEtaMoebiusTrialLogWeight_le hn), ← h]
  unfold pairedEtaMoebiusArithmeticMiddleEnergy
  ring

/-- Both end contributions vanish in the exact full residual; only the original intervening growing band is left without a decay bound. -/
theorem pairedEtaMoebiusContinuumResidualEnergy_sub_middle_tendsto_zero :
    Tendsto (fun M : ℕ ↦ pairedEtaMoebiusContinuumResidualEnergy M (pairedEtaMoebiusTrialLogWeight M) -
      pairedEtaMoebiusArithmeticMiddleEnergy M) atTop (𝓝 0) := by
  have hz : Tendsto (fun M : ℕ ↦
      pairedEtaMoebiusArithmeticSquarePrefix M (pairedEtaMoebiusLogarithmicHeadCutoff M)
        (pairedEtaMoebiusTrialLogWeight M) +
      pairedEtaMoebiusArithmeticSquareTail M (M ^ 2) (pairedEtaMoebiusTrialLogWeight M)) atTop (𝓝 0) := by
    simpa only [add_zero] using pairedEtaMoebiusArithmeticSquarePrefix_logarithmic_tendsto_zero.add
      pairedEtaMoebiusArithmeticSquareTail_quadratic_tendsto_zero
  apply hz.congr'
  filter_upwards [eventually_ge_atTop 1] with M hM
  have h := pairedEtaMoebiusContinuumResidualEnergy_eq_head_middle_tail hM
  linarith

end

end RiemannGaussian
