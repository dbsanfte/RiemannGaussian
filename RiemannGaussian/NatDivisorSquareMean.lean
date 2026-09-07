import RiemannGaussian.NatDivisorCommonGcd

/-!
# Complete second moment of positive factorization counts

All coincident factorizations in a hyperbolic product region are counted
through common multiples of two divisors. The exact lcm count and the
complete gcd kernel give a cubic logarithmic mean bound.
-/

open scoped Classical

namespace RiemannGaussian

noncomputable section

/-- A positive integer's divisors are exactly its positive bounded multiples test. -/
theorem filter_Icc_dvd_eq_divisors {n T : ℕ} (hn : 1 ≤ n) (hnT : n ≤ T) :
    (Finset.Icc 1 T).filter (fun d ↦ d ∣ n) = n.divisors := by
  ext d
  simp only [Finset.mem_filter, Finset.mem_Icc, Nat.mem_divisors]
  constructor
  · intro h
    exact ⟨h.2, by omega⟩
  · rintro ⟨hd, _⟩
    exact ⟨⟨Nat.pos_of_dvd_of_pos hd hn, (Nat.le_of_dvd hn hd).trans hnT⟩, hd⟩

/-- The divisor square retains every pair of divisors before common-multiple counting. -/
theorem card_divisors_sq_eq_sum_common {n T : ℕ} (hn : 1 ≤ n) (hnT : n ≤ T) :
    (n.divisors.card : ℝ) ^ 2 =
      ∑ d ∈ Finset.Icc 1 T, ∑ e ∈ Finset.Icc 1 T,
        if d ∣ n ∧ e ∣ n then (1 : ℝ) else 0 := by
  rw [← filter_Icc_dvd_eq_divisors hn hnT, sq]
  simp only [Finset.card_eq_sum_ones, Nat.cast_sum, Finset.sum_filter,
    Finset.sum_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro d hd
  apply Finset.sum_congr rfl
  intro e he
  split_ifs <;> simp_all

/-- Each common-multiple count is bounded with its exact positive gcd weight. -/
theorem card_Icc_common_dvd_le_gcd {d e : ℕ} (hd : 1 ≤ d) (he : 1 ≤ e) (T : ℕ) :
    (((Finset.Icc 1 T).filter (fun n ↦ d ∣ n ∧ e ∣ n)).card : ℝ) ≤
      (T : ℝ) * Nat.gcd d e / ((d : ℝ) * e) := by
  have hl : 0 < Nat.lcm d e := Nat.lcm_pos hd he
  have hlR : (0 : ℝ) < Nat.lcm d e := by exact_mod_cast hl
  have hg : 0 < Nat.gcd d e := Nat.gcd_pos_of_pos_left e hd
  have hgR : (0 : ℝ) < Nat.gcd d e := by exact_mod_cast hg
  simp only [← Nat.lcm_dvd_iff]
  rw [card_Icc_dvd_eq hl]
  calc
    _ ≤ (T : ℝ) / Nat.lcm d e := by
      apply (le_div_iff₀ hlR).mpr
      exact_mod_cast Nat.div_mul_le_self T (Nat.lcm d e)
    _ = _ := by
      rw [show (d : ℝ) * e = (Nat.gcd d e : ℝ) * Nat.lcm d e by
        exact_mod_cast (Nat.gcd_mul_lcm d e).symm]
      field_simp

/-- The full second divisor moment has a cubic harmonic bound. -/
theorem sum_Icc_card_divisors_sq_le_harmonic_cube (T : ℕ) :
    (∑ n ∈ Finset.Icc 1 T, (n.divisors.card : ℝ) ^ 2) ≤
      (T : ℝ) * (∑ d ∈ Finset.Icc 1 T, 1 / (d : ℝ)) ^ 3 := by
  calc
    _ = ∑ d ∈ Finset.Icc 1 T, ∑ e ∈ Finset.Icc 1 T,
        (((Finset.Icc 1 T).filter (fun n ↦ d ∣ n ∧ e ∣ n)).card : ℝ) := by
      simp_rw [Finset.card_eq_sum_ones, Nat.cast_sum, Nat.cast_one, Finset.sum_filter]
      calc
        _ = ∑ n ∈ Finset.Icc 1 T, ∑ d ∈ Finset.Icc 1 T, ∑ e ∈ Finset.Icc 1 T,
            if d ∣ n ∧ e ∣ n then (1 : ℝ) else 0 := by
          apply Finset.sum_congr rfl
          intro n hn
          simpa only [Finset.sum_const, nsmul_eq_mul, mul_one] using
            card_divisors_sq_eq_sum_common (Finset.mem_Icc.mp hn).1 (Finset.mem_Icc.mp hn).2
        _ = _ := by rw [Finset.sum_comm]; apply Finset.sum_congr rfl; intro d hd; rw [Finset.sum_comm]
    _ ≤ ∑ d ∈ Finset.Icc 1 T, ∑ e ∈ Finset.Icc 1 T,
        (T : ℝ) * Nat.gcd d e / ((d : ℝ) * e) := by
      apply Finset.sum_le_sum
      intro d hd
      apply Finset.sum_le_sum
      intro e he
      exact card_Icc_common_dvd_le_gcd (Finset.mem_Icc.mp hd).1 (Finset.mem_Icc.mp he).1 T
    _ = (T : ℝ) * (∑ d ∈ Finset.Icc 1 T, ∑ e ∈ Finset.Icc 1 T,
        (Nat.gcd d e : ℝ) / ((d : ℝ) * e)) := by simp only [mul_div_assoc, Finset.mul_sum]
    _ ≤ _ := mul_le_mul_of_nonneg_left (sum_Icc_gcd_div_mul_le_harmonic_cube T) (Nat.cast_nonneg T)

/-- The full factorization second moment is at most product budget times a cubic logarithm. -/
theorem sum_Icc_card_divisors_sq_le_log_cube (T : ℕ) :
    (∑ n ∈ Finset.Icc 1 T, (n.divisors.card : ℝ) ^ 2) ≤
      (T : ℝ) * (1 + Real.log T) ^ 3 := by
  apply (sum_Icc_card_divisors_sq_le_harmonic_cube T).trans
  apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg T)
  apply pow_le_pow_left₀ (Finset.sum_nonneg (fun d _ ↦ by positivity))
  simpa only [harmonic_eq_sum_Icc, Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast, one_div]
    using harmonic_le_one_add_log T

end

end RiemannGaussian
