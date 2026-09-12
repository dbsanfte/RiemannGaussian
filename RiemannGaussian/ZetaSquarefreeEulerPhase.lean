/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaSquarefreeEulerDecay
import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds
import Mathlib.Analysis.PSeries

/-!
# Retained prime phases and a uniformly bounded Euler remainder

The reciprocal squarefree Euler factors have an exact exponential
representation. The first `J` prime harmonics are retained as a complex
sum, and only the logarithmic Taylor remainder is bounded. If
`(J+1)*sigma > 1`, that remainder is uniformly bounded over every finite
prime set and every point in `Re(s) >= sigma`. Squarefree marks have their
own uniform cost. In particular two harmonics suffice throughout
`Re(s) >= 3/8`, including the existing squarefree Cauchy discs.

The signed harmonic sum is not assumed bounded. These estimates control
the higher-order part of the actual multiplier, not the surviving prime
source in the RH argument.
-/

namespace RiemannGaussian.SquarefreeEulerPhase
noncomputable section
open Complex Filter Topology
open scoped Classical

/-- The retained first `J` harmonics of the excluded prime factors. -/
def phase (J : ℕ) (S : Finset ℕ) (s : ℂ) : ℂ :=
  ∑ a ∈ S, Complex.logTaylor (J + 1) (zetaPrimeFeature s a)

/-- The exact complex remainder after retaining the first `J` harmonics. -/
def remainder (J : ℕ) (S : Finset ℕ) (s : ℂ) : ℂ :=
  ∑ a ∈ S, (Complex.logTaylor (J + 1) (zetaPrimeFeature s a) -
    Complex.log (1 + zetaPrimeFeature s a))

private theorem weight_antitone {σ τ : ℝ} (h : σ ≤ τ) (a : ℕ) :
    zetaPrimeExpWeight τ a ≤ zetaPrimeExpWeight σ a := by
  apply Real.exp_le_exp.mpr
  nlinarith [Real.log_natCast_nonneg a]

private theorem weight_le_two {σ : ℝ} (hσ : 0 < σ) {a : ℕ} (ha : a.Prime) :
    zetaPrimeExpWeight σ a ≤ zetaPrimeExpWeight σ 2 := by
  apply Real.exp_le_exp.mpr
  have h := Real.log_le_log (by norm_num : (0 : ℝ) < 2)
    (show (2 : ℝ) ≤ a by exact_mod_cast ha.two_le)
  norm_num only [Nat.cast_ofNat]
  nlinarith

private theorem weight_two_lt_one {σ : ℝ} (hσ : 0 < σ) :
    zetaPrimeExpWeight σ 2 < 1 := by
  apply Real.exp_lt_one_iff.mpr
  have h := Real.log_pos (by norm_num : (1 : ℝ) < 2)
  norm_num only [Nat.cast_ofNat]
  nlinarith

private theorem feature_norm_lt_one {s : ℂ} (hs : 0 < s.re)
    {a : ℕ} (ha : a.Prime) : ‖zetaPrimeFeature s a‖ < 1 := by
  rw [norm_zetaPrimeFeature]
  exact (weight_le_two hs ha).trans_lt (weight_two_lt_one hs)

private theorem factor_ne_zero {s : ℂ} (hs : 0 < s.re)
    {a : ℕ} (ha : a.Prime) : 1 + zetaPrimeFeature s a ≠ 0 := by
  have h := feature_norm_lt_one hs ha
  intro he
  have he' : zetaPrimeFeature s a = -1 := by linear_combination he
  simp [he'] at h

/-- The finite product retains every complex prime phase exactly;
no choice of a logarithm of the whole product is required. -/
theorem inverse_product_eq_exp (J : ℕ) (S : Finset ℕ)
    (hS : ∀ a ∈ S, a.Prime) {s : ℂ} (hs : 0 < s.re) :
    (∏ a ∈ S, (1 + zetaPrimeFeature s a)⁻¹) =
      Complex.exp (-phase J S s + remainder J S s) := by
  have he : -phase J S s + remainder J S s =
      ∑ a ∈ S, -Complex.log (1 + zetaPrimeFeature s a) := by
    simp only [phase, remainder, Finset.sum_sub_distrib, Finset.sum_neg_distrib]
    ring
  rw [he, Complex.exp_sum]
  exact Finset.prod_congr rfl (fun a ha ↦ by
    rw [Complex.exp_neg, Complex.exp_log (factor_ne_zero hs (hS a ha))])

/-- The actual marked multiplier splits into its exact mark factor,
the retained prime harmonics, and the complete complex remainder. -/
theorem multiplier_eq (J : ℕ) (S : Finset ℕ) (hS : ∀ a ∈ S, a.Prime)
    (P : ℕ) (hPS : ∀ a ∈ P.primeFactors, a ∉ S)
    {s : ℂ} (hs : 0 < s.re) :
    squarefreeEulerMultiplier S P s = squarefreeEulerMultiplier ∅ P s *
      Complex.exp (-phase J S s + remainder J S s) := by
  have hd : Disjoint S P.primeFactors := Finset.disjoint_left.mpr
    (fun a haS haP ↦ hPS a haP haS)
  rw [← inverse_product_eq_exp J S hS hs]
  simp only [squarefreeEulerMultiplier, Finset.empty_union, Finset.prod_union hd]
  ring

/-- Before taking any uniform envelope, the error keeps the exact
prime support and the full local Taylor remainder bound. -/
theorem norm_remainder_le (J : ℕ) (S : Finset ℕ)
    (hS : ∀ a ∈ S, a.Prime) {s : ℂ} (hs : 0 < s.re) :
    ‖remainder J S s‖ ≤ ∑ a ∈ S,
      ‖zetaPrimeFeature s a‖ ^ (J + 1) *
        (1 - ‖zetaPrimeFeature s a‖)⁻¹ / (J + 1) := by
  unfold remainder
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro a ha
  rw [norm_sub_rev]
  exact Complex.norm_log_sub_logTaylor_le J (feature_norm_lt_one hs (hS a ha))

private theorem summable_weight {σ : ℝ} (hσ : 1 < σ) :
    Summable (zetaPrimeExpWeight σ) := by
  rw [← summable_nat_add_iff 1]
  have h := (Real.summable_nat_rpow.mpr (show -σ < -1 by linarith))
  have ht := (summable_nat_add_iff 1).mpr h
  apply ht.congr
  intro n
  rw [Real.rpow_def_of_pos (by positivity : (0 : ℝ) < (n + 1 : ℕ))]
  dsimp [zetaPrimeExpWeight]
  congr 1
  ring

/-- Whenever the first omitted harmonic is absolutely summable, one
constant controls the complete remainder for every finite prime set,
every ordinate and every point of the indicated closed half-plane. -/
theorem exists_uniform_remainder_bound (J : ℕ) {σ : ℝ}
    (hσ : 0 < σ) (hJ : 1 < (J + 1 : ℝ) * σ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (S : Finset ℕ), (∀ a ∈ S, a.Prime) →
      ∀ s : ℂ, σ ≤ s.re → ‖remainder J S s‖ ≤ C := by
  let K := (1 - zetaPrimeExpWeight σ 2)⁻¹
  let f := zetaPrimeExpWeight ((J + 1 : ℝ) * σ)
  have hden : 0 < 1 - zetaPrimeExpWeight σ 2 := sub_pos.mpr (weight_two_lt_one hσ)
  have hK : 0 < K := inv_pos.mpr hden
  have hf : Summable f := summable_weight hJ
  have hf0 (a : ℕ) : 0 ≤ f a := (Real.exp_pos _).le
  have hsum : 0 ≤ ∑' a : ℕ, f a := tsum_nonneg hf0
  refine ⟨K * (∑' a : ℕ, f a) + 1, by positivity, ?_⟩
  intro S hS s hs
  have hb (a : ℕ) (ha : a ∈ S) :
      ‖zetaPrimeFeature s a‖ ^ (J + 1) *
        (1 - ‖zetaPrimeFeature s a‖)⁻¹ / (J + 1) ≤ K * f a := by
    have hwa : ‖zetaPrimeFeature s a‖ ≤ zetaPrimeExpWeight σ a := by
      rw [norm_zetaPrimeFeature]
      exact weight_antitone hs a
    have hw2 := hwa.trans (weight_le_two hσ (hS a ha))
    have hi : (1 - ‖zetaPrimeFeature s a‖)⁻¹ ≤ K :=
      inv_anti₀ hden (by linarith)
    have hinv : 0 ≤ (1 - ‖zetaPrimeFeature s a‖)⁻¹ :=
      inv_nonneg.mpr (by linarith [weight_two_lt_one hσ])
    have he : zetaPrimeExpWeight σ a ^ (J + 1) = f a := by
      rw [zetaPrimeExpWeight, ← Real.exp_nat_mul]
      dsimp [f, zetaPrimeExpWeight]
      congr 1
      push_cast
      ring
    calc
      _ ≤ ‖zetaPrimeFeature s a‖ ^ (J + 1) *
          (1 - ‖zetaPrimeFeature s a‖)⁻¹ :=
        div_le_self (mul_nonneg (pow_nonneg (norm_nonneg _) _) hinv)
          (by have h : (0 : ℝ) ≤ J := Nat.cast_nonneg J; linarith)
      _ ≤ zetaPrimeExpWeight σ a ^ (J + 1) * K :=
        mul_le_mul (pow_le_pow_left₀ (norm_nonneg _) hwa _) hi hinv
          (pow_nonneg (Real.exp_pos _).le _)
      _ = K * f a := by rw [he, mul_comm]
  calc
    _ ≤ ∑ a ∈ S, K * f a :=
      (norm_remainder_le J S hS (hσ.trans_le hs)).trans (Finset.sum_le_sum hb)
    _ = K * ∑ a ∈ S, f a := (Finset.mul_sum _ _ _).symm
    _ ≤ K * ∑' a : ℕ, f a :=
      mul_le_mul_of_nonneg_left (hf.sum_le_tsum S (fun a _ ↦ hf0 a)) hK.le
    _ ≤ _ := by linarith

/-- Removing the retained harmonics bounds the reciprocal product
both above and away from zero, uniformly in the entire finite prime set. -/
theorem exists_compensated_product_bounds (J : ℕ) {σ : ℝ}
    (hσ : 0 < σ) (hJ : 1 < (J + 1 : ℝ) * σ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (S : Finset ℕ), (∀ a ∈ S, a.Prime) →
      ∀ s : ℂ, σ ≤ s.re →
        Real.exp (-C) ≤ ‖Complex.exp (phase J S s) *
          ∏ a ∈ S, (1 + zetaPrimeFeature s a)⁻¹‖ ∧
        ‖Complex.exp (phase J S s) *
          ∏ a ∈ S, (1 + zetaPrimeFeature s a)⁻¹‖ ≤ Real.exp C := by
  obtain ⟨C, hC, hb⟩ := exists_uniform_remainder_bound J hσ hJ
  refine ⟨C, hC, ?_⟩
  intro S hS s hs
  rw [inverse_product_eq_exp J S hS (hσ.trans_le hs), ← Complex.exp_add]
  have he : phase J S s + (-phase J S s + remainder J S s) = remainder J S s := by ring
  rw [he, Complex.norm_exp]
  have h := (Complex.abs_re_le_norm (remainder J S s)).trans (hb S hS s hs)
  exact ⟨Real.exp_le_exp.mpr (abs_le.mp h).1, Real.exp_le_exp.mpr (abs_le.mp h).2⟩

/-- Every squarefree mark has a common bounded cost. All remaining
growth of the true multiplier is exposed in the signed prime harmonics. -/
theorem exists_uniform_mark_bound (J : ℕ) {σ : ℝ}
    (hσ : 0 < σ) (hJ : 1 < (J + 1 : ℝ) * σ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (S : Finset ℕ), (∀ a ∈ S, a.Prime) →
      ∀ P : ℕ, Squarefree P → (∀ a ∈ P.primeFactors, a ∉ S) →
      ∀ s : ℂ, σ ≤ s.re →
        ‖squarefreeEulerMultiplier S P s‖ ≤ C * Real.exp (-(phase J S s).re) := by
  obtain ⟨K, _, A, hA, hm⟩ := exists_squarefreeEulerBudget_card_bound hσ
  obtain ⟨B, _, hb⟩ := exists_uniform_remainder_bound J hσ hJ
  refine ⟨A * Real.exp B, mul_pos hA (Real.exp_pos _), ?_⟩
  intro S hS P hP hPS s hs
  have hmark : ‖squarefreeEulerMultiplier ∅ P s‖ ≤ A := by
    apply (norm_squarefreeEulerMultiplier_le ∅ (by simp) P hσ hs).trans
    simpa using hm ∅ (by simp) P hP (by simp)
  have hrem : (remainder J S s).re ≤ B :=
    (Complex.re_le_norm _).trans (hb S hS s hs)
  rw [multiplier_eq J S hS P hPS (hσ.trans_le hs), norm_mul,
    Complex.norm_exp, Complex.add_re, Complex.neg_re]
  calc
    _ ≤ A * Real.exp (-(phase J S s).re + B) :=
      mul_le_mul hmark (Real.exp_le_exp.mpr (by linarith)) (Real.exp_pos _).le hA.le
    _ = _ := by rw [Real.exp_add]; ring

/-- With two retained harmonics, the second channel is literally the
same prime phase at the doubled complex argument, with coefficient `-1/2`. -/
theorem phase_two (S : Finset ℕ) (s : ℂ) :
    phase 2 S s = (∑ a ∈ S, zetaPrimeFeature s a) -
      (1 / 2 : ℂ) * ∑ a ∈ S, zetaPrimeFeature (2 * s) a := by
  have hp (a : ℕ) : zetaPrimeFeature s a ^ 2 = zetaPrimeFeature (2 * s) a := by
    rw [zetaPrimeFeature, ← Complex.exp_nat_mul]
    dsimp [zetaPrimeFeature]
    congr 1
    ring
  have ht (z : ℂ) : Complex.logTaylor 3 z = z - z ^ 2 / 2 := by
    norm_num [Complex.logTaylor, Finset.sum_range_succ]
    ring
  rw [phase, Finset.mul_sum, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro a _
  rw [ht, hp]
  ring

end
end RiemannGaussian.SquarefreeEulerPhase
