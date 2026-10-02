/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.NatDivisorSquareMean

/-!
# A finite reciprocal second divisor moment

Expand both divisor incidences before summing common multiples. Their
reciprocal mass is bounded with the exact lcm, giving a fourth harmonic
power. No auxiliary Dirichlet exponent or exponential cutoff loss enters.
-/

set_option autoImplicit false
noncomputable section
open scoped BigOperators Classical
namespace RiemannGaussian

/-- Common multiples retain their lcm reciprocal after harmonic summation. -/
theorem sum_Icc_common_dvd_inv_le {d e : ℕ} (hd : 0 < d) (he : 0 < e) (X : ℕ) :
    (∑ n ∈ Finset.Icc 1 X, if d ∣ n ∧ e ∣ n then 1/(n : ℝ) else 0) ≤
      (Nat.gcd d e : ℝ)/((d : ℝ)*e) *
        (∑ n ∈ Finset.Icc 1 X, 1/(n : ℝ)) := by
  have hl : 0 < Nat.lcm d e := Nat.lcm_pos hd he
  have hlR : (0 : ℝ) < Nat.lcm d e := by exact_mod_cast hl
  have hH : (∑ n ∈ Finset.Icc 1 (X/Nat.lcm d e),1/(n : ℝ)) ≤
      ∑ n ∈ Finset.Icc 1 X,1/(n : ℝ) :=
    Finset.sum_le_sum_of_subset_of_nonneg
      (Finset.Icc_subset_Icc le_rfl (Nat.div_le_self X _)) (fun _ _ _ => by positivity)
  simp only [← Nat.lcm_dvd_iff]
  rw [sum_Icc_dvd_inv_eq hl X]
  calc
    _ ≤ (1/(Nat.lcm d e : ℝ))*∑ n ∈ Finset.Icc 1 X,1/(n : ℝ) :=
      mul_le_mul_of_nonneg_left hH (by positivity)
    _ = _ := by
      have hgR : (0 : ℝ) < Nat.gcd d e := by
        exact_mod_cast Nat.gcd_pos_of_pos_left e hd
      rw [show (d : ℝ)*e=(Nat.gcd d e : ℝ)*Nat.lcm d e by
        exact_mod_cast (Nat.gcd_mul_lcm d e).symm]
      field_simp

/-- The complete finite reciprocal divisor-square mass has no exponential loss. -/
theorem sum_Icc_card_divisors_sq_div_le_harmonic_four (X : ℕ) :
    (∑ n ∈ Finset.Icc 1 X,(n.divisors.card : ℝ)^2/(n : ℝ)) ≤
      (∑ n ∈ Finset.Icc 1 X,1/(n : ℝ))^4 := by
  let H := ∑ n ∈ Finset.Icc 1 X,1/(n : ℝ)
  have hH : 0 ≤ H := Finset.sum_nonneg (fun _ _ => by positivity)
  calc
    _ = ∑ d ∈ Finset.Icc 1 X,∑ e ∈ Finset.Icc 1 X,
        ∑ n ∈ Finset.Icc 1 X,if d ∣ n ∧ e ∣ n then 1/(n : ℝ) else 0 := by
      calc
        _ = ∑ n ∈ Finset.Icc 1 X,∑ d ∈ Finset.Icc 1 X,∑ e ∈ Finset.Icc 1 X,
            if d ∣ n ∧ e ∣ n then 1/(n : ℝ) else 0 := by
          apply Finset.sum_congr rfl
          intro n hn
          rw [card_divisors_sq_eq_sum_common
            (Finset.mem_Icc.mp hn).1 (Finset.mem_Icc.mp hn).2]
          simp only [Finset.sum_div]
          apply Finset.sum_congr rfl
          intro d _
          apply Finset.sum_congr rfl
          intro e _
          split_ifs <;> simp
        _ = _ := by
          rw [Finset.sum_comm]
          apply Finset.sum_congr rfl
          intro d _
          rw [Finset.sum_comm]
    _ ≤ ∑ d ∈ Finset.Icc 1 X,∑ e ∈ Finset.Icc 1 X,
        ((Nat.gcd d e : ℝ)/((d : ℝ)*e))*H := by
      apply Finset.sum_le_sum
      intro d hd
      apply Finset.sum_le_sum
      intro e he
      exact sum_Icc_common_dvd_inv_le (Finset.mem_Icc.mp hd).1
        (Finset.mem_Icc.mp he).1 X
    _ = (∑ d ∈ Finset.Icc 1 X,∑ e ∈ Finset.Icc 1 X,
        (Nat.gcd d e : ℝ)/((d : ℝ)*e))*H := by rw [Finset.sum_mul]; simp only [Finset.sum_mul]
    _ ≤ H^3*H := mul_le_mul_of_nonneg_right
      (sum_Icc_gcd_div_mul_le_harmonic_cube X) hH
    _ = _ := by dsimp [H]; ring

/-- The logarithmic bound also applies to every literal masked subpopulation. -/
theorem sum_card_divisors_sq_div_le_log_four (X : ℕ) (S : Finset ℕ)
    (hS : S ⊆ Finset.Icc 1 X) :
    (∑ n ∈ S,(n.divisors.card : ℝ)^2/(n : ℝ)) ≤ (1+Real.log X)^4 := by
  apply (Finset.sum_le_sum_of_subset_of_nonneg hS (fun _ _ _ => by positivity)).trans
  apply (sum_Icc_card_divisors_sq_div_le_harmonic_four X).trans
  apply pow_le_pow_left₀ (Finset.sum_nonneg (fun _ _ => by positivity))
  simpa only [harmonic_eq_sum_Icc,Rat.cast_sum,Rat.cast_inv,Rat.cast_natCast,one_div]
    using harmonic_le_one_add_log X

end RiemannGaussian
