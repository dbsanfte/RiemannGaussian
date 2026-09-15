/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaRieszSmoothHead
import RiemannGaussian.ZetaRieszGeneralCofactorTilt
import Mathlib.NumberTheory.Harmonic.Bounds

/-!
# Complete divisor-weighted prefixes

An exact hyperbola identity retains every real arithmetic weight. The full
positive real-power prefix costs only one logarithm, including every
squarefree family without restricting its number of prime factors.
-/

namespace RiemannGaussian.ZetaRieszDivisorPrefix
noncomputable section
open Filter Topology
open scoped BigOperators Classical

/-- The complete divisor-weighted prefix is the exact ordered
hyperbola sum, for every real arithmetic weight and integer endpoint. -/
theorem divisor_prefix_eq_hyperbola (f : ℕ → ℝ) (X : ℕ) :
    (∑ n ∈ Finset.Icc 1 X, (n.divisors.card : ℝ) * f n) =
      ∑ a ∈ Finset.Icc 1 X, ∑ b ∈ Finset.Icc 1 (X / a), f (a * b) := by
  let H : Finset (ℕ × ℕ) := ((Finset.Icc 1 X) ×ˢ (Finset.Icc 1 X)).filter
    (fun ab => ab.1 * ab.2 ≤ X)
  have hset : (Finset.Icc 1 X).biUnion Nat.divisorsAntidiagonal = H := by
    ext ⟨a, b⟩
    simp only [Finset.mem_biUnion, Nat.mem_divisorsAntidiagonal, Finset.mem_filter,
      Finset.mem_product, Finset.mem_Icc, H]
    constructor
    · rintro ⟨n, ⟨hn1, hnX⟩, he, hn0⟩
      have hab0 : a * b ≠ 0 := by rwa [he]
      have ha : 0 < a := Nat.pos_of_ne_zero (left_ne_zero_of_mul hab0)
      have hb : 0 < b := Nat.pos_of_ne_zero (right_ne_zero_of_mul hab0)
      refine ⟨⟨⟨ha, ?_⟩, ⟨hb, ?_⟩⟩, by omega⟩ <;> nlinarith
    · rintro ⟨⟨⟨ha, _haX⟩, ⟨hb, _hbX⟩⟩, hab⟩
      exact ⟨a * b, ⟨by nlinarith, hab⟩, rfl, by positivity⟩
  have hdis : (Finset.Icc 1 X : Set ℕ).PairwiseDisjoint Nat.divisorsAntidiagonal := by
    intro n _hn m _hm hne
    apply Finset.disjoint_left.mpr
    intro ab ha hb
    exact hne ((Nat.mem_divisorsAntidiagonal.mp ha).1.symm.trans
      (Nat.mem_divisorsAntidiagonal.mp hb).1)
  have hc (n : ℕ) : n.divisorsAntidiagonal.card = n.divisors.card := by
    rw [← Nat.map_div_right_divisors, Finset.card_map]
  have hi (n : ℕ) : (n.divisors.card : ℝ) * f n =
      ∑ ab ∈ n.divisorsAntidiagonal, f (ab.1 * ab.2) := by
    calc
      _ = ∑ _ab ∈ n.divisorsAntidiagonal, f n := by simp [hc]
      _ = _ := Finset.sum_congr rfl (fun ab hab => by rw [(Nat.mem_divisorsAntidiagonal.mp hab).1])
  have hf (a : ℕ) (ha : a ∈ Finset.Icc 1 X) :
      (Finset.Icc 1 X).filter (fun b => a * b ≤ X) = Finset.Icc 1 (X / a) := by
    have ha0 : 0 < a := (Finset.mem_Icc.mp ha).1
    ext b
    simp only [Finset.mem_filter, Finset.mem_Icc]
    constructor
    · rintro ⟨⟨hb, _hbX⟩, hab⟩
      exact ⟨hb, (Nat.le_div_iff_mul_le ha0).mpr (by simpa [mul_comm] using hab)⟩
    · rintro ⟨hb, hab⟩
      exact ⟨⟨hb, hab.trans (Nat.div_le_self X a)⟩,
        by simpa [mul_comm] using (Nat.le_div_iff_mul_le ha0).mp hab⟩
  calc
    _ = ∑ n ∈ Finset.Icc 1 X, ∑ ab ∈ n.divisorsAntidiagonal, f (ab.1 * ab.2) :=
      Finset.sum_congr rfl (fun n _ => hi n)
    _ = ∑ ab ∈ H, f (ab.1 * ab.2) := by rw [← hset, Finset.sum_biUnion hdis]
    _ = ∑ a ∈ Finset.Icc 1 X, ∑ b ∈ Finset.Icc 1 X,
        if a * b ≤ X then f (a * b) else 0 := by
      simp only [H, Finset.sum_filter, Finset.sum_product]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro a ha
      rw [← Finset.sum_filter, hf a ha]

/-- All positive real powers have a complete divisor-weighted prefix
bound with only one logarithmic cost, retaining every integer endpoint. -/
theorem divisor_rpow_prefix_le {alpha : ℝ} (halpha : 0 < alpha) (X : ℕ) :
    (∑ n ∈ Finset.Icc 1 X, (n.divisors.card : ℝ) * (n : ℝ) ^ (alpha - 1)) ≤
      (1 + 1 / alpha) * (X : ℝ) ^ alpha * (1 + Real.log X) := by
  by_cases hX : X = 0
  · simp [hX, Real.zero_rpow halpha.ne']
  have hXR : (0 : ℝ) < X := by exact_mod_cast Nat.pos_of_ne_zero hX
  have hi a (ha : a ∈ Finset.Icc 1 X) :
      (∑ b ∈ Finset.Icc 1 (X / a), ((a * b : ℕ) : ℝ) ^ (alpha - 1)) ≤
        (1 + 1 / alpha) * (X : ℝ) ^ alpha / a := by
    have ha0 : 0 < a := (Finset.mem_Icc.mp ha).1
    have haR : (0 : ℝ) < a := by exact_mod_cast ha0
    have hdiv : ((X / a : ℕ) : ℝ) ≤ (X : ℝ) / a := by
      apply (le_div_iff₀ haR).mpr
      exact_mod_cast Nat.div_mul_le_self X a
    calc
      _ = (a : ℝ) ^ (alpha - 1) * ∑ b ∈ Finset.Icc 1 (X / a), (b : ℝ) ^ (alpha - 1) := by
        simp only [Nat.cast_mul, Real.mul_rpow (Nat.cast_nonneg a) (Nat.cast_nonneg _), Finset.mul_sum]
      _ ≤ (a : ℝ) ^ (alpha - 1) * ((1 + 1 / alpha) * ((X / a : ℕ) : ℝ) ^ alpha) :=
        mul_le_mul_of_nonneg_left (ZetaRieszGeneralCofactorTilt.sum_rpow_prefix_le halpha (X / a))
          (Real.rpow_nonneg (Nat.cast_nonneg a) _)
      _ ≤ (a : ℝ) ^ (alpha - 1) * ((1 + 1 / alpha) * ((X : ℝ) / a) ^ alpha) := by gcongr
      _ = _ := by
        rw [Real.div_rpow hXR.le haR.le, Real.rpow_sub_one haR.ne']
        have hp : (a : ℝ) ^ alpha ≠ 0 := (Real.rpow_pos_of_pos haR alpha).ne'
        field_simp
  have hh : (∑ a ∈ Finset.Icc 1 X, (a : ℝ)⁻¹) ≤ 1 + Real.log X := by
    simpa only [harmonic_eq_sum_Icc, Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast] using
      harmonic_le_one_add_log X
  calc
    _ = ∑ a ∈ Finset.Icc 1 X, ∑ b ∈ Finset.Icc 1 (X / a), ((a * b : ℕ) : ℝ) ^ (alpha - 1) :=
      divisor_prefix_eq_hyperbola _ X
    _ ≤ ∑ a ∈ Finset.Icc 1 X, (1 + 1 / alpha) * (X : ℝ) ^ alpha / a := Finset.sum_le_sum hi
    _ = (1 + 1 / alpha) * (X : ℝ) ^ alpha * ∑ a ∈ Finset.Icc 1 X, (a : ℝ)⁻¹ := by
      simp only [div_eq_mul_inv, Finset.mul_sum]
    _ ≤ _ := mul_le_mul_of_nonneg_left hh (by positivity)

/-- Any squarefree integer family, including arbitrary rough kernels,
has a complete divisor-choice prefix bound without fixing its prime count. -/
theorem squarefree_rpow_prefix_le (D : Finset ℕ) (X : ℕ)
    (hD : ∀ n ∈ D, Squarefree n ∧ n ≤ X) {alpha : ℝ} (halpha : 0 < alpha) :
    (∑ n ∈ D, (2 : ℝ) ^ n.primeFactors.card * (n : ℝ) ^ (alpha - 1)) ≤
      (1 + 1 / alpha) * (X : ℝ) ^ alpha * (1 + Real.log X) := by
  calc
    _ = ∑ n ∈ D, (n.divisors.card : ℝ) * (n : ℝ) ^ (alpha - 1) := by
      apply Finset.sum_congr rfl
      intro n hn
      rw [ZetaRieszSmoothHead.card_divisors_of_squarefree (hD n hn).1, Nat.cast_pow, Nat.cast_ofNat]
    _ ≤ ∑ n ∈ Finset.Icc 1 X, (n.divisors.card : ℝ) * (n : ℝ) ^ (alpha - 1) := by
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · intro n hn
        exact Finset.mem_Icc.mpr ⟨Nat.pos_of_ne_zero (hD n hn).1.ne_zero, (hD n hn).2⟩
      · intro n _ _
        positivity
    _ ≤ _ := divisor_rpow_prefix_le halpha X

end
end RiemannGaussian.ZetaRieszDivisorPrefix
