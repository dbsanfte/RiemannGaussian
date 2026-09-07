import RiemannGaussian.EtaMoebiusTrialAtoms
import Mathlib.Algebra.Order.BigOperators.Ring.Finset

/-!
# Exact balanced Möbius coefficients and their complete size bound

Finite differences of the signed arithmetic primitive define trial
coefficients at the original scales `(j+1)/d`. The entire coefficient
sum vanishes when the arithmetic cutoff fits the grid, and its absolute
sum is at most `2M` for bounded weights. Logarithmic weights provide a
fully specified arithmetic choice, with their bounds proved here.
No approximation or critical square-integral limit is assumed.
-/

open scoped ArithmeticFunction.Moebius

namespace RiemannGaussian

noncomputable section

/-- The full signed finite Möbius primitive, retaining the exact harmonic correction in every atom. -/
def pairedEtaMoebiusTrialPrimitive (M : ℕ) (w : ℕ → ℝ) (x : ℝ) : ℝ :=
  ∑ n ∈ Finset.Icc 1 M, (μ n : ℝ) * w n * pairedEtaMoebiusTrialAtom n x

/-- The signed primitive is exactly the finite weighted harmonic prefix minus its complete endpoint value, multiplied by the physical coordinate. -/
theorem pairedEtaMoebiusTrialPrimitive_eq_harmonic_difference (M : ℕ) (w : ℕ → ℝ)
    {x : ℝ} (hx : 1 ≤ x) :
    pairedEtaMoebiusTrialPrimitive M w x = x *
      ((∑ n ∈ Finset.Icc 1 M, if (n : ℝ) ≤ x then (μ n : ℝ) * w n / n else 0) -
        ∑ n ∈ Finset.Icc 1 M, (μ n : ℝ) * w n / n) := by
  rw [pairedEtaMoebiusTrialPrimitive, mul_sub, Finset.mul_sum, Finset.mul_sum,
    ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro n hn
  by_cases hnx : (n : ℝ) ≤ x
  · rw [if_pos hnx, pairedEtaMoebiusTrialAtom_eq_zero_of_le (Finset.mem_Icc.mp hn).1 hnx]
    ring
  · rw [if_neg hnx, pairedEtaMoebiusTrialAtom_eq_neg_div hx (lt_of_not_ge hnx)]
    ring

/-- Exact arithmetic trial coefficients at the original uniform physical scales. -/
def pairedEtaMoebiusTrialCoefficient (d M : ℕ) (w : ℕ → ℝ) (j : Fin d) : ℝ :=
  pairedEtaMoebiusTrialPrimitive M w ((d : ℝ) / (j.1 + 1 : ℝ)) -
    pairedEtaMoebiusTrialPrimitive M w ((d : ℝ) / (j.1 + 2 : ℝ))

/-- Every coefficient retains its original signed Möbius sum of two-channel atom differences. -/
theorem pairedEtaMoebiusTrialCoefficient_eq_sum (d M : ℕ) (w : ℕ → ℝ) (j : Fin d) :
    pairedEtaMoebiusTrialCoefficient d M w j =
      ∑ n ∈ Finset.Icc 1 M, (μ n : ℝ) * w n *
        (pairedEtaMoebiusTrialAtom n ((d : ℝ) / (j.1 + 1 : ℝ)) -
          pairedEtaMoebiusTrialAtom n ((d : ℝ) / (j.1 + 2 : ℝ))) := by
  simp only [pairedEtaMoebiusTrialCoefficient, pairedEtaMoebiusTrialPrimitive,
    mul_sub, Finset.sum_sub_distrib]

/-- The entire signed primitive vanishes below the unit endpoint. -/
theorem pairedEtaMoebiusTrialPrimitive_eq_zero_of_lt_one (M : ℕ) (w : ℕ → ℝ) {x : ℝ} (hx : x < 1) :
    pairedEtaMoebiusTrialPrimitive M w x = 0 := by
  apply Finset.sum_eq_zero
  intro n hn
  rw [pairedEtaMoebiusTrialAtom_eq_zero_of_lt_one (Finset.mem_Icc.mp hn).1 hx, mul_zero]

/-- At and beyond the arithmetic cutoff, the harmonic correction cancels the entire signed primitive. -/
theorem pairedEtaMoebiusTrialPrimitive_eq_zero_of_cutoff_le (M : ℕ) (w : ℕ → ℝ) {x : ℝ} (hx : (M : ℝ) ≤ x) :
    pairedEtaMoebiusTrialPrimitive M w x = 0 := by
  apply Finset.sum_eq_zero
  intro n hn
  have hnx : (n : ℝ) ≤ x := (show (n : ℝ) ≤ M by exact_mod_cast (Finset.mem_Icc.mp hn).2).trans hx
  rw [pairedEtaMoebiusTrialAtom_eq_zero_of_le (Finset.mem_Icc.mp hn).1 hnx, mul_zero]

/-- The full coefficient vector has exact zero total mass when every arithmetic endpoint fits the grid. -/
theorem sum_pairedEtaMoebiusTrialCoefficient_eq_zero {d M : ℕ} (hMd : M ≤ d) (w : ℕ → ℝ) :
    (∑ j : Fin d, pairedEtaMoebiusTrialCoefficient d M w j) = 0 := by
  have htel := Finset.sum_range_sub'
    (fun j : ℕ ↦ pairedEtaMoebiusTrialPrimitive M w ((d : ℝ) / (j + 1 : ℝ))) d
  rw [← Fin.sum_univ_eq_sum_range] at htel
  have h : (∑ j : Fin d, pairedEtaMoebiusTrialCoefficient d M w j) =
      pairedEtaMoebiusTrialPrimitive M w d -
        pairedEtaMoebiusTrialPrimitive M w ((d : ℝ) / (d + 1 : ℝ)) := by
    simpa only [pairedEtaMoebiusTrialCoefficient, Nat.cast_add, Nat.cast_one,
      Nat.cast_zero, zero_add, div_one, add_assoc, one_add_one_eq_two] using htel
  rw [h, pairedEtaMoebiusTrialPrimitive_eq_zero_of_cutoff_le M w (by exact_mod_cast hMd),
    pairedEtaMoebiusTrialPrimitive_eq_zero_of_lt_one M w
      ((div_lt_one (by positivity : (0 : ℝ) < d + 1)).mpr (by linarith)), sub_self]

/-- Bounded arithmetic weights give a complete coefficient absolute-sum bound independent of grid dimension. -/
theorem pairedEtaMoebiusTrialCoefficient_sum_abs_le (d M : ℕ) {w : ℕ → ℝ}
    (hw : ∀ n ∈ Finset.Icc 1 M, |w n| ≤ 1) :
    (∑ j : Fin d, |pairedEtaMoebiusTrialCoefficient d M w j|) ≤ 2 * M := by
  have hweight (n : ℕ) (hn : n ∈ Finset.Icc 1 M) : |(μ n : ℝ) * w n| ≤ 1 := by
    rw [abs_mul]
    exact (mul_le_mul (abs_real_moebius_le_one n) (hw n hn) (abs_nonneg _) (by norm_num)).trans_eq (by norm_num)
  calc
    _ ≤ ∑ j : Fin d, ∑ n ∈ Finset.Icc 1 M,
        |pairedEtaMoebiusTrialAtom n ((d : ℝ) / (j.1 + 1 : ℝ)) -
          pairedEtaMoebiusTrialAtom n ((d : ℝ) / (j.1 + 2 : ℝ))| := by
      apply Finset.sum_le_sum
      intro j _
      rw [pairedEtaMoebiusTrialCoefficient_eq_sum]
      apply (Finset.abs_sum_le_sum_abs _ _).trans
      apply Finset.sum_le_sum
      intro n hn
      rw [abs_mul]
      simpa only [one_mul] using mul_le_mul_of_nonneg_right (hweight n hn) (abs_nonneg
        (pairedEtaMoebiusTrialAtom n ((d : ℝ) / (j.1 + 1 : ℝ)) -
          pairedEtaMoebiusTrialAtom n ((d : ℝ) / (j.1 + 2 : ℝ))))
    _ = ∑ n ∈ Finset.Icc 1 M, ∑ j : Fin d,
        |pairedEtaMoebiusTrialAtom n ((d : ℝ) / (j.1 + 1 : ℝ)) -
          pairedEtaMoebiusTrialAtom n ((d : ℝ) / (j.1 + 2 : ℝ))| := Finset.sum_comm
    _ ≤ ∑ _n ∈ Finset.Icc 1 M, (2 : ℝ) :=
      Finset.sum_le_sum (fun n hn ↦ pairedEtaMoebiusTrialAtom_grid_variation_le d (Finset.mem_Icc.mp hn).1)
    _ = _ := by simp; ring

/-- The entire coefficient square sum has a proved arithmetic cutoff bound, with no dimension factor. -/
theorem pairedEtaMoebiusTrialCoefficient_sum_sq_le (d M : ℕ) {w : ℕ → ℝ}
    (hw : ∀ n ∈ Finset.Icc 1 M, |w n| ≤ 1) :
    (∑ j : Fin d, pairedEtaMoebiusTrialCoefficient d M w j ^ 2) ≤ 4 * (M : ℝ) ^ 2 := by
  have hsq := Finset.sum_sq_le_sq_sum_of_nonneg (s := Finset.univ)
    (fun j _ ↦ abs_nonneg (pairedEtaMoebiusTrialCoefficient d M w j))
  simp only [sq_abs] at hsq
  calc
    _ ≤ (∑ j : Fin d, |pairedEtaMoebiusTrialCoefficient d M w j|) ^ 2 := hsq
    _ ≤ (2 * (M : ℝ)) ^ 2 := by gcongr; exact pairedEtaMoebiusTrialCoefficient_sum_abs_le d M hw
    _ = _ := by ring

/-- A completely specified logarithmic Möbius taper, with the singular unit cutoff handled separately. -/
def pairedEtaMoebiusTrialLogWeight (M n : ℕ) : ℝ :=
  if 1 < M then 1 - Real.log (n : ℝ) / Real.log (M : ℝ) else 0

/-- Every active logarithmic arithmetic weight lies between zero and one. -/
theorem pairedEtaMoebiusTrialLogWeight_bounds {M n : ℕ} (hn : n ∈ Finset.Icc 1 M) :
    0 ≤ pairedEtaMoebiusTrialLogWeight M n ∧ pairedEtaMoebiusTrialLogWeight M n ≤ 1 := by
  by_cases hM : 1 < M
  · have hMp : 0 < Real.log (M : ℝ) := Real.log_pos (by exact_mod_cast hM)
    have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast (Finset.mem_Icc.mp hn).1
    have hnM : (n : ℝ) ≤ M := by exact_mod_cast (Finset.mem_Icc.mp hn).2
    have hn0 : 0 ≤ Real.log (n : ℝ) := Real.log_nonneg hn1
    have hle : Real.log (n : ℝ) / Real.log (M : ℝ) ≤ 1 :=
      (div_le_one hMp).mpr (Real.log_le_log (by linarith) hnM)
    have hge := div_nonneg hn0 hMp.le
    simp only [pairedEtaMoebiusTrialLogWeight, if_pos hM]
    constructor <;> linarith
  · simp [pairedEtaMoebiusTrialLogWeight, hM]

/-- The specified logarithmic weights satisfy the complete coefficient norm hypothesis. -/
theorem abs_pairedEtaMoebiusTrialLogWeight_le {M n : ℕ} (hn : n ∈ Finset.Icc 1 M) :
    |pairedEtaMoebiusTrialLogWeight M n| ≤ 1 := by
  rw [abs_of_nonneg (pairedEtaMoebiusTrialLogWeight_bounds hn).1]
  exact (pairedEtaMoebiusTrialLogWeight_bounds hn).2

end

end RiemannGaussian
