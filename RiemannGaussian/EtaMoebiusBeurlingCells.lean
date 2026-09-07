import RiemannGaussian.EtaMoebiusQuotientParity
import RiemannGaussian.EtaMoebiusQuotientError

/-!
# The balanced fractional-part cells behind the actual eta residual

The original signed coefficients define the usual balanced floor residual
on each physical integer cell. Its unpaired harmonic primitive has the
actual eta residual as an exact dyadic difference. All arithmetic cutoffs,
harmonic corrections, and the empty cell are retained. This identifies
the carrier before comparing its full norm with the classical geometry.
-/

open scoped ArithmeticFunction.Moebius

namespace RiemannGaussian

noncomputable section

/-- The unpaired harmonic prefix on the original positive integer endpoints. -/
def etaUnpairedArithmeticHarmonicPrefix (L : ℕ) : ℝ :=
  ∑ n ∈ Finset.Icc 1 L, 1 / (n : ℝ)

/-- The balanced fractional-part residual on an integer cell, with its original signed Möbius coefficients and harmonic correction. -/
def pairedEtaMoebiusBeurlingCell (M : ℕ) (w : ℕ → ℝ) (L : ℕ) : ℝ :=
  (if L = 0 then 0 else 1) - ∑ n ∈ Finset.Icc 1 M, (μ n : ℝ) * w n * (L / n : ℕ) +
    pairedEtaMoebiusArithmeticHarmonic M w * L

/-- The unpaired harmonic primitive of the original balanced arithmetic coefficients, including the empty cell. -/
def pairedEtaMoebiusBeurlingHarmonicPrefix (M : ℕ) (w : ℕ → ℝ) (L : ℕ) : ℝ :=
  (if L = 0 then 0 else 1) - ∑ n ∈ Finset.Icc 1 M,
    ((μ n : ℝ) * w n / n) * etaUnpairedArithmeticHarmonicPrefix (L / n) +
    pairedEtaMoebiusArithmeticHarmonic M w * etaUnpairedArithmeticHarmonicPrefix L

private theorem sum_even_prefix (L : ℕ) (f : ℕ → ℝ) :
    (∑ l ∈ Finset.Icc 1 L, if Even l then f l else 0) =
      ∑ n ∈ Finset.Icc 1 (L / 2), f (2 * n) := by
  rw [← Finset.sum_filter]
  symm
  apply Finset.sum_bij (fun n _ ↦ 2 * n)
  · intro n hn
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_Icc.mpr ⟨by have := (Finset.mem_Icc.mp hn).1; omega, ?_⟩,
      even_iff_two_dvd.mpr ⟨n, rfl⟩⟩
    have h := (Nat.le_div_iff_mul_le (by decide : 0 < 2)).mp (Finset.mem_Icc.mp hn).2
    omega
  · intro n _ m _ h
    omega
  · intro l hl
    obtain ⟨hl, he⟩ := Finset.mem_filter.mp hl
    obtain ⟨n, rfl⟩ := even_iff_two_dvd.mp he
    refine ⟨n, Finset.mem_Icc.mpr ⟨?_, ?_⟩, rfl⟩
    · have := (Finset.mem_Icc.mp hl).1
      omega
    · apply (Nat.le_div_iff_mul_le (by decide : 0 < 2)).mpr
      have := (Finset.mem_Icc.mp hl).2
      omega
  · intro n _
    rfl

/-- The actual alternating harmonic prefix is exactly the difference of the unpaired prefix and its halved integer prefix. -/
theorem pairedEtaArithmeticHarmonicPrefix_eq_dyadic_difference (L : ℕ) :
    pairedEtaArithmeticHarmonicPrefix L =
      etaUnpairedArithmeticHarmonicPrefix L - etaUnpairedArithmeticHarmonicPrefix (L / 2) := by
  have hs : (∑ l ∈ Finset.Icc 1 L, if Even l then (2 : ℝ) / l else 0) =
      etaUnpairedArithmeticHarmonicPrefix (L / 2) := by
    rw [sum_even_prefix]
    apply Finset.sum_congr rfl
    intro n _
    rw [Nat.cast_mul, Nat.cast_ofNat]
    ring
  calc
    _ = (∑ l ∈ Finset.Icc 1 L, (1 : ℝ) / l) -
        ∑ l ∈ Finset.Icc 1 L, if Even l then (2 : ℝ) / l else 0 := by
      rw [← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro l _
      by_cases hl : Even l
      · simp [pairedEtaDirichletSign, hl]
        ring
      · simp [pairedEtaDirichletSign, hl]
    _ = _ := by rw [hs]; rfl

/-- Every original signed eta cell residual is the literal dyadic difference of the balanced unpaired harmonic primitive, with no restriction to cells below the cutoff. -/
theorem pairedEtaMoebiusArithmeticCellResidual_eq_beurling_dyadic (M L : ℕ) (w : ℕ → ℝ) :
    pairedEtaMoebiusArithmeticCellResidual M w L =
      pairedEtaMoebiusBeurlingHarmonicPrefix M w L -
        pairedEtaMoebiusBeurlingHarmonicPrefix M w (L / 2) := by
  have hdiv (n : ℕ) : L / n / 2 = L / 2 / n := by
    rw [Nat.div_div_eq_div_mul, Nat.div_div_eq_div_mul, Nat.mul_comm n 2]
  have hstep : (if L = 1 then (1 : ℝ) else 0) =
      (if L = 0 then 0 else 1) - (if L / 2 = 0 then 0 else 1) := by
    by_cases h0 : L = 0
    · subst L
      norm_num
    · by_cases h1 : L = 1
      · subst L
        norm_num
      · have hd : L / 2 ≠ 0 := by omega
        simp [h0, h1, hd]
  rw [pairedEtaMoebiusArithmeticCellResidual_eq_quotients]
  simp_rw [pairedEtaArithmeticHarmonicPrefix_eq_dyadic_difference, hdiv]
  unfold pairedEtaMoebiusBeurlingHarmonicPrefix
  rw [hstep]
  simp_rw [mul_sub, Finset.sum_sub_distrib]
  ring

/-- The literal balanced cell equals the original signed sum of fractional remainders at its integer endpoint. -/
theorem pairedEtaMoebiusBeurlingCell_eq_remainders (M L : ℕ) (w : ℕ → ℝ) :
    pairedEtaMoebiusBeurlingCell M w L = (if L = 0 then 0 else 1) +
      ∑ n ∈ Finset.Icc 1 M, (μ n : ℝ) * w n * ((L % n : ℕ) / (n : ℝ)) := by
  unfold pairedEtaMoebiusBeurlingCell pairedEtaMoebiusArithmeticHarmonic
  rw [Finset.sum_mul]
  have hs : (∑ n ∈ Finset.Icc 1 M, (μ n : ℝ) * w n / n * L) -
      (∑ n ∈ Finset.Icc 1 M, (μ n : ℝ) * w n * (L / n : ℕ)) =
      ∑ n ∈ Finset.Icc 1 M, (μ n : ℝ) * w n * ((L % n : ℕ) / (n : ℝ)) := by
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro n hn
    have hnp : (0 : ℝ) < n := by exact_mod_cast (Finset.mem_Icc.mp hn).1
    have he : (n : ℝ) * (L / n : ℕ) + (L % n : ℕ) = L := by exact_mod_cast Nat.div_add_mod L n
    calc
      _ = (μ n : ℝ) * w n * ((L : ℝ) - (n : ℝ) * (L / n : ℕ)) / n := by field_simp
      _ = _ := by rw [show (L : ℝ) - (n : ℝ) * (L / n : ℕ) = (L % n : ℕ) by linarith]; ring
  linarith

/-- The balanced fractional-part cells are uniformly bounded at every physical index for the original bounded arithmetic weights. -/
theorem abs_pairedEtaMoebiusBeurlingCell_le {M : ℕ} {w : ℕ → ℝ}
    (hw : ∀ n ∈ Finset.Icc 1 M, |w n| ≤ 1) (L : ℕ) :
    |pairedEtaMoebiusBeurlingCell M w L| ≤ 1 + M := by
  rw [pairedEtaMoebiusBeurlingCell_eq_remainders]
  apply (abs_add_le _ _).trans
  have hhead : |(if L = 0 then (0 : ℝ) else 1)| ≤ 1 := by split_ifs <;> norm_num
  apply (add_le_add hhead (Finset.abs_sum_le_sum_abs _ _)).trans
  apply add_le_add_right
  calc
    _ ≤ ∑ _n ∈ Finset.Icc 1 M, (1 : ℝ) := by
      apply Finset.sum_le_sum
      intro n hn
      have hnp : 0 < n := (Finset.mem_Icc.mp hn).1
      have hnR : (0 : ℝ) < n := by exact_mod_cast hnp
      have hrem : ((L % n : ℕ) : ℝ) ≤ n := by exact_mod_cast (Nat.mod_lt L hnp).le
      have ha : |(μ n : ℝ) * w n| ≤ 1 := by
        rw [abs_mul]
        exact (mul_le_mul (abs_real_moebius_le_one n) (hw n hn) (abs_nonneg _) (by norm_num)).trans_eq (by norm_num)
      rw [abs_mul, abs_of_nonneg (div_nonneg (Nat.cast_nonneg (L % n)) hnR.le)]
      exact (mul_le_mul ha ((div_le_one hnR).mpr hrem) (by positivity) (by norm_num)).trans_eq (by norm_num)
    _ = _ := by simp

private theorem unpaired_harmonic_succ (L : ℕ) :
    etaUnpairedArithmeticHarmonicPrefix (L + 1) = etaUnpairedArithmeticHarmonicPrefix L + 1 / (L + 1 : ℝ) := by
  simp only [etaUnpairedArithmeticHarmonicPrefix, Finset.sum_Icc_succ_top (by omega : 1 ≤ L + 1),
    Nat.cast_add, Nat.cast_one]

private theorem harmonic_quotient_step (L n : ℕ) :
    etaUnpairedArithmeticHarmonicPrefix ((L + 1) / n) - etaUnpairedArithmeticHarmonicPrefix (L / n) =
      (n : ℝ) / (L + 1 : ℝ) * (((L + 1) / n : ℕ) - (L / n : ℕ) : ℝ) := by
  by_cases hd : n ∣ L + 1
  · have he : n * (L / n + 1) = L + 1 := by
      have hh := Nat.mul_div_cancel' hd
      rw [Nat.succ_div_of_dvd hd] at hh
      exact hh
    have heR : (n : ℝ) * ((L / n : ℕ) + 1 : ℝ) = L + 1 := by exact_mod_cast he
    rw [Nat.succ_div_of_dvd hd, unpaired_harmonic_succ]
    push_cast
    field_simp
    nlinarith
  · rw [Nat.succ_div_of_not_dvd hd]
    simp

/-- The unpaired harmonic primitive has exactly the balanced fractional-part cell increment divided by the original physical endpoint. -/
theorem pairedEtaMoebiusBeurlingHarmonicPrefix_succ_sub (M L : ℕ) (w : ℕ → ℝ) :
    pairedEtaMoebiusBeurlingHarmonicPrefix M w (L + 1) - pairedEtaMoebiusBeurlingHarmonicPrefix M w L =
      (pairedEtaMoebiusBeurlingCell M w (L + 1) - pairedEtaMoebiusBeurlingCell M w L) / (L + 1 : ℝ) := by
  have hS : ((∑ n ∈ Finset.Icc 1 M, ((μ n : ℝ) * w n / n) * etaUnpairedArithmeticHarmonicPrefix ((L + 1) / n)) -
      (∑ n ∈ Finset.Icc 1 M, ((μ n : ℝ) * w n / n) * etaUnpairedArithmeticHarmonicPrefix (L / n))) * (L + 1 : ℝ) =
      (∑ n ∈ Finset.Icc 1 M, (μ n : ℝ) * w n * ((L + 1) / n : ℕ)) -
      (∑ n ∈ Finset.Icc 1 M, (μ n : ℝ) * w n * (L / n : ℕ)) := by
    rw [← Finset.sum_sub_distrib, Finset.sum_mul, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro n hn
    have hnp : 0 < n := (Finset.mem_Icc.mp hn).1
    have hnR : (0 : ℝ) < n := by exact_mod_cast hnp
    rw [← mul_sub, harmonic_quotient_step L n]
    field_simp
  have hhead : (1 - (if L = 0 then (0 : ℝ) else 1)) * L = 0 := by
    by_cases hL : L = 0 <;> simp [hL]
  unfold pairedEtaMoebiusBeurlingHarmonicPrefix pairedEtaMoebiusBeurlingCell
  rw [if_neg (by omega : L + 1 ≠ 0), unpaired_harmonic_succ]
  push_cast
  apply (eq_div_iff (by positivity : (L + 1 : ℝ) ≠ 0)).mpr
  have hrecip : (1 / (L + 1 : ℝ)) * (L + 1 : ℝ) = 1 := by field_simp
  have hp := congrArg (fun x : ℝ ↦ pairedEtaMoebiusArithmeticHarmonic M w * x) hrecip
  nlinarith [hp]

end

end RiemannGaussian
