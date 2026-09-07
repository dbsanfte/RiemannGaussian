import RiemannGaussian.MoebiusFiniteMellinCancellation

/-!
# Cancellation inside the original divided arithmetic cutoffs

Each set of divisors with a common divided cutoff is retained exactly.
Its full complex Möbius weight equals the difference of two genuine finite
prefixes. The finite cancellation bound supplies one remainder valid over
all original cutoffs and all positive quotient blocks.
-/

open Complex
open scoped ArithmeticFunction.Moebius

namespace RiemannGaussian

noncomputable section

/-- The original complex Möbius coefficients grouped at one literal divided cutoff. -/
def complexMoebiusDividedCutoffBlock (s : ℂ) (M q : ℕ) : ℂ :=
  ∑ d ∈ (Finset.Icc 1 M).filter (fun d ↦ M / d = q), ((μ d : ℤ) : ℂ) * (d : ℂ) ^ (-s)

/-- The positive-integer finite weighted prefix agrees exactly with the literal closed arithmetic interval. -/
theorem complexMoebiusFinitePrefix_eq_sum_Icc (s : ℂ) (M : ℕ) :
    complexMoebiusFinitePrefix s M =
      ∑ d ∈ Finset.Icc 1 M, ((μ d : ℤ) : ℂ) * (d : ℂ) ^ (-s) := by
  rw [← Finset.Ico_add_one_right_eq_Icc, Finset.sum_Ico_eq_sum_range]
  simp only [Nat.add_sub_cancel, Nat.cast_add, Nat.cast_one, add_comm 1, complexMoebiusFinitePrefix]

/-- The actual divided-cutoff condition is exactly the reciprocal interval between two integer quotient endpoints. -/
theorem moebius_dividedCutoff_eq_iff {M q d : ℕ} (hq : 0 < q) (hd : 0 < d) :
    M / d = q ↔ M / (q + 1) < d ∧ d ≤ M / q := by
  rw [Nat.div_lt_iff_lt_mul (by omega : 0 < q + 1), Nat.le_div_iff_mul_le hq]
  constructor
  · intro h
    have hle : q ≤ M / d := by omega
    have hlt : M / d < q + 1 := by omega
    rw [Nat.le_div_iff_mul_le hd] at hle
    rw [Nat.div_lt_iff_lt_mul hd] at hlt
    constructor <;> nlinarith
  · rintro ⟨hlt, hle⟩
    have hle' : q ≤ M / d := (Nat.le_div_iff_mul_le hd).mpr (by nlinarith)
    have hlt' : M / d < q + 1 := (Nat.div_lt_iff_lt_mul hd).mpr (by nlinarith)
    omega

/-- The complete finite divisor block retains its exact interval, including both floor cutoffs. -/
theorem moebiusDividedCutoff_filter_eq_Icc (M : ℕ) {q : ℕ} (hq : 0 < q) :
    (Finset.Icc 1 M).filter (fun d ↦ M / d = q) =
      Finset.Icc (M / (q + 1) + 1) (M / q) := by
  ext d
  simp only [Finset.mem_filter, Finset.mem_Icc]
  constructor
  · rintro ⟨⟨hd, _⟩, h⟩
    have hb := (moebius_dividedCutoff_eq_iff hq hd).mp h
    omega
  · rintro ⟨hl, hu⟩
    have hd : 0 < d := lt_of_lt_of_le (Nat.succ_pos _) hl
    refine ⟨⟨hd, hu.trans (Nat.div_le_self M q)⟩, ?_⟩
    exact (moebius_dividedCutoff_eq_iff hq hd).mpr ⟨by omega, hu⟩

/-- The exact complex arithmetic block is the difference of its two genuine weighted prefixes. -/
theorem complexMoebiusDividedCutoffBlock_eq_prefix_sub (s : ℂ) (M : ℕ) {q : ℕ} (hq : 0 < q) :
    complexMoebiusDividedCutoffBlock s M q =
      complexMoebiusFinitePrefix s (M / q) - complexMoebiusFinitePrefix s (M / (q + 1)) := by
  have hLU : M / (q + 1) ≤ M / q := Nat.div_le_div_left (by omega) hq
  have hsub : Finset.Icc 1 (M / (q + 1)) ⊆ Finset.Icc 1 (M / q) :=
    Finset.Icc_subset_Icc le_rfl hLU
  have hsets : Finset.Icc 1 (M / q) \ Finset.Icc 1 (M / (q + 1)) =
      Finset.Icc (M / (q + 1) + 1) (M / q) := by
    ext d
    simp only [Finset.mem_sdiff, Finset.mem_Icc]
    have hL0 : 0 ≤ M / (q + 1) := Nat.zero_le _
    omega
  apply eq_sub_iff_add_eq.mpr
  rw [complexMoebiusDividedCutoffBlock, moebiusDividedCutoff_filter_eq_Icc M hq,
    complexMoebiusFinitePrefix_eq_sum_Icc, complexMoebiusFinitePrefix_eq_sum_Icc, ← hsets]
  exact Finset.sum_sdiff hsub

/-- One finite remainder controls every original complex-weighted quotient block, with arbitrarily small coefficient on its natural power scale. -/
theorem exists_complexMoebiusDividedCutoffBlock_power_remainder {s : ℂ}
    (hs : 0 < s.re) (hsone : s.re < 1) {eps : ℝ} (heps : 0 < eps) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (M q : ℕ), 0 < q →
      ‖complexMoebiusDividedCutoffBlock s M q‖ ≤ eps * ((M / q : ℕ) + 1 : ℝ) ^ (1 - s.re) + C := by
  obtain ⟨B, hB, hprefix⟩ := exists_complexMoebiusFinitePrefix_power_remainder hs hsone
    (by linarith : 0 < eps / 2)
  refine ⟨2 * B, by positivity, fun M q hq ↦ ?_⟩
  have hLU : M / (q + 1) ≤ M / q := Nat.div_le_div_left (by omega) hq
  have hpow : ((M / (q + 1) : ℕ) + 1 : ℝ) ^ (1 - s.re) ≤
      ((M / q : ℕ) + 1 : ℝ) ^ (1 - s.re) :=
    Real.rpow_le_rpow (by positivity) (by exact_mod_cast Nat.add_le_add_right hLU 1) (by linarith)
  rw [complexMoebiusDividedCutoffBlock_eq_prefix_sub s M hq]
  have h1 := hprefix (M / q)
  have h2 := hprefix (M / (q + 1))
  have hp := mul_le_mul_of_nonneg_left hpow (by linarith : 0 ≤ eps / 2)
  have ht := norm_sub_le (complexMoebiusFinitePrefix s (M / q))
    (complexMoebiusFinitePrefix s (M / (q + 1)))
  linarith

end

end RiemannGaussian
