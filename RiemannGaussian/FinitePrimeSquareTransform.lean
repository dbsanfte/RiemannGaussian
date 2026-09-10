/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.FinitePrimeSquareSieve

/-!
# Uniform signed transforms for the complete square deletion

The finite transforms keep the exact square inclusion-exclusion and the
full surviving first-power pattern. Their independent norm bounds are
uniform over every selected square family. Only the first-power prime
cutoff enters the square-root exponential cost.
-/

open Complex
open scoped Classical

namespace RiemannGaussian
noncomputable section

/-- The exact signed response of all selected squares inside one
first-power prime multiple, acting on the genuine factor responses. -/
def primeSquareMultipleTransform (F : ℕ → ℂ) (W Q : Finset ℕ) : ℂ :=
  F (∏ p ∈ W, p) - ∑ V ∈ Q.powerset, (-1 : ℂ) ^ V.card * F (primeSquareIntersection W V)

/-- The complete selected-square deletion within the at-most-one
first-power prime pattern, with every signed intersection present. -/
def primeSquareSurvivorTransform (F : ℕ → ℂ) (S Q : Finset ℕ) : ℂ :=
  primeSquareMultipleTransform F ∅ Q -
    ∑ T ∈ S.powerset.filter (fun T ↦ 2 ≤ T.card), ∑ U ∈ (S \ T).powerset,
      (-1 : ℂ) ^ U.card * primeSquareMultipleTransform F (T ∪ U) Q

/-- The transform is the actual repeated-prime mask coefficientwise,
for every complex physical weight. It does not introduce a model carrier. -/
theorem primeSquareSurvivorTransform_indicator (S Q : Finset ℕ)
    (hS : ∀ p ∈ S, p.Prime) (hQ : ∀ p ∈ Q, p.Prime) (F : ℕ → ℂ) (n : ℕ) :
    primeSquareSurvivorTransform (fun P ↦ if P ∣ n then F n else 0) S Q =
      primeSquareSurvivorMask S Q n * F n := by
  rw [primeSquareSurvivorMask_mul_eq S Q hS F n]
  have he (W : Finset ℕ) (hW : ∀ p ∈ W, p.Prime) :
      primeSquareMultipleTransform (fun P ↦ if P ∣ n then F n else 0) W Q =
        primeSquareMultipleMask W Q n * F n :=
    (primeSquareMultipleMask_mul_eq W Q hW hQ F n).symm
  unfold primeSquareSurvivorTransform
  rw [he ∅ (by simp)]
  congr 1
  apply Finset.sum_congr rfl
  intro T hT
  apply Finset.sum_congr rfl
  intro U hU
  rw [he (T ∪ U) (fun p hp ↦ hS p (by
    rcases Finset.mem_union.mp hp with hp | hp
    · exact Finset.mem_powerset.mp (Finset.mem_filter.mp hT).1 hp
    · exact (Finset.mem_sdiff.mp (Finset.mem_powerset.mp hU hp)).1))]

/-- Both signed zeta channels commute exactly with each square
transform. This identity precedes the companion norm bound. -/
theorem primeSquareMultipleTransform_add_mul (F G : ℕ → ℂ) (W Q : Finset ℕ) (a b : ℂ) :
    primeSquareMultipleTransform (fun P ↦ F P * a + G P * b) W Q =
      primeSquareMultipleTransform F W Q * a + primeSquareMultipleTransform G W Q * b := by
  unfold primeSquareMultipleTransform
  simp_rw [mul_add, Finset.sum_add_distrib, ← mul_assoc, ← Finset.sum_mul]
  ring

/-- The full surviving-pattern transform keeps both complex response
channels coupled through every prime and square intersection. -/
theorem primeSquareSurvivorTransform_add_mul (F G : ℕ → ℂ) (S Q : Finset ℕ) (a b : ℂ) :
    primeSquareSurvivorTransform (fun P ↦ F P * a + G P * b) S Q =
      primeSquareSurvivorTransform F S Q * a + primeSquareSurvivorTransform G S Q * b := by
  unfold primeSquareSurvivorTransform
  simp_rw [primeSquareMultipleTransform_add_mul, mul_add, Finset.sum_add_distrib,
    ← mul_assoc, ← Finset.sum_mul]
  ring

/-- A full physical kernel factor commutes with the exact transform. -/
theorem primeSquareSurvivorTransform_mul_right (F : ℕ → ℂ) (S Q : Finset ℕ) (a : ℂ) :
    primeSquareSurvivorTransform (fun P ↦ F P * a) S Q = primeSquareSurvivorTransform F S Q * a := by
  simpa only [mul_zero, add_zero] using primeSquareSurvivorTransform_add_mul F (fun _ ↦ 0) S Q a 0

/-- Genuine summation commutes with every square intersection and
its original inclusion-exclusion sign. All factors used are positive. -/
theorem hasSum_primeSquareMultipleTransform (f : ℕ → ℕ → ℂ) (F : ℕ → ℂ) (W Q : Finset ℕ)
    (hW : ∀ p ∈ W, p.Prime) (hQ : ∀ p ∈ Q, p.Prime)
    (h : ∀ P : ℕ, 0 < P → HasSum (f P) (F P)) :
    HasSum (fun n ↦ primeSquareMultipleTransform (fun P ↦ f P n) W Q)
      (primeSquareMultipleTransform F W Q) := by
  exact (h _ (Finset.prod_pos (fun p hp ↦ (hW p hp).pos))).sub
    (hasSum_sum (s := Q.powerset) (fun V hV ↦
      (h _ (primeSquareIntersection_pos W V hW
        (fun p hp ↦ hQ p (Finset.mem_powerset.mp hV hp)))).mul_left ((-1 : ℂ) ^ V.card)))

/-- The complete signed survivor transform commutes with genuine
summation, with every first-power and square intersection included. -/
theorem hasSum_primeSquareSurvivorTransform (f : ℕ → ℕ → ℂ) (F : ℕ → ℂ) (S Q : Finset ℕ)
    (hS : ∀ p ∈ S, p.Prime) (hQ : ∀ p ∈ Q, p.Prime)
    (h : ∀ P : ℕ, 0 < P → HasSum (f P) (F P)) :
    HasSum (fun n ↦ primeSquareSurvivorTransform (fun P ↦ f P n) S Q)
      (primeSquareSurvivorTransform F S Q) := by
  have hb (W : Finset ℕ) (hW : ∀ p ∈ W, p.Prime) := hasSum_primeSquareMultipleTransform f F W Q hW hQ h
  apply (hb ∅ (by simp)).sub
  apply hasSum_sum
  intro T hT
  apply hasSum_sum
  intro U hU
  apply (hb (T ∪ U) ?_).mul_left
  intro p hp
  apply hS p
  rcases Finset.mem_union.mp hp with hp | hp
  · exact Finset.mem_powerset.mp (Finset.mem_filter.mp hT).1 hp
  · exact (Finset.mem_sdiff.mp (Finset.mem_powerset.mp hU hp)).1

/-- The first square transform has a uniform bound over every square
selection, retaining the complete shared-prime correction on `W`. -/
theorem norm_primeSquareMultipleTransform_le (F : ℕ → ℂ) (W Q : Finset ℕ)
    (hW : ∀ p ∈ W, p.Prime) (hQ : ∀ p ∈ Q, p.Prime)
    {σ A : ℝ} (hσ : 1 / 2 < σ) (hA : 0 ≤ A)
    (hF : ∀ P : ℕ, 0 < P → ‖F P‖ ≤ A * zetaPrimeExpWeight σ P) :
    ‖primeSquareMultipleTransform F W Q‖ ≤
      A * (1 + Real.exp (primeSquareWeightMass σ)) * ∏ p ∈ W, primeSquareCorrectedWeight σ p := by
  have hW0 := Finset.prod_pos (fun p hp ↦ (hW p hp).pos)
  have hp : zetaPrimeExpWeight σ (∏ p ∈ W, p) ≤ ∏ p ∈ W, primeSquareCorrectedWeight σ p := by
    rw [zetaPrimeExpWeight_prod W (fun p hp ↦ (hW p hp).pos)]
    apply Finset.prod_le_prod
    · intro p _
      exact (Real.exp_pos _).le
    · intro p _
      unfold primeSquareCorrectedWeight
      nlinarith [sq_nonneg (zetaPrimeExpWeight σ p)]
  have hs : ‖∑ V ∈ Q.powerset, (-1 : ℂ) ^ V.card * F (primeSquareIntersection W V)‖ ≤
      A * Real.exp (primeSquareWeightMass σ) * ∏ p ∈ W, primeSquareCorrectedWeight σ p := by
    apply (norm_sum_le _ _).trans
    calc
      _ ≤ ∑ V ∈ Q.powerset, A * zetaPrimeExpWeight σ (primeSquareIntersection W V) := by
        apply Finset.sum_le_sum
        intro V hV
        rw [norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul]
        exact hF _ (primeSquareIntersection_pos W V hW
          (fun p hp ↦ hQ p (Finset.mem_powerset.mp hV hp)))
      _ = A * ∑ V ∈ Q.powerset, zetaPrimeExpWeight σ (primeSquareIntersection W V) := (Finset.mul_sum ..).symm
      _ ≤ _ := (mul_le_mul_of_nonneg_left (sum_primeSquareIntersection_weight_le W Q hW hQ hσ) hA).trans_eq (by
        unfold primeSquareCorrectedWeight
        ring)
  exact (norm_sub_le _ _).trans ((add_le_add
    ((hF _ hW0).trans (mul_le_mul_of_nonneg_left hp hA)) hs).trans_eq (by ring))

/-- The finite positive constant paying all square overlaps and their
shared-prime corrections at an exponent strictly beyond one half. -/
def primeSquareSurvivorCost (σ : ℝ) : ℝ :=
  2 * (1 + Real.exp (primeSquareWeightMass σ)) * Real.exp (2 * primeSquareWeightMass σ)

/-- The complete square-sieve constant is strictly positive. -/
theorem primeSquareSurvivorCost_pos (σ : ℝ) : 0 < primeSquareSurvivorCost σ := by
  unfold primeSquareSurvivorCost
  positivity

/-- The whole signed square deletion inside the surviving first-power
pattern has an independent bound. The selected square family is arbitrary;
only the first-power prime cutoff enters the exponential. -/
theorem norm_primeSquareSurvivorTransform_le (F : ℕ → ℂ) (S Q : Finset ℕ) (R : ℕ)
    (hS : ∀ p ∈ S, p.Prime ∧ p ≤ R) (hQ : ∀ p ∈ Q, p.Prime)
    {σ A : ℝ} (hσ : 1 / 2 < σ) (hA : 0 ≤ A)
    (hF : ∀ P : ℕ, 0 < P → ‖F P‖ ≤ A * zetaPrimeExpWeight σ P) :
    ‖primeSquareSurvivorTransform F S Q‖ ≤
      A * primeSquareSurvivorCost σ * Real.exp (4 * Real.sqrt R) := by
  let B := A * (1 + Real.exp (primeSquareWeightMass σ))
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hb (W : Finset ℕ) (hW : ∀ p ∈ W, p.Prime) :=
    norm_primeSquareMultipleTransform_le F W Q hW hQ hσ hA hF
  have hbase : ‖primeSquareMultipleTransform F ∅ Q‖ ≤ B := by
    simpa only [Finset.prod_empty, mul_one] using hb ∅ (by simp)
  have hsum : ‖∑ T ∈ S.powerset.filter (fun T ↦ 2 ≤ T.card), ∑ U ∈ (S \ T).powerset,
      (-1 : ℂ) ^ U.card * primeSquareMultipleTransform F (T ∪ U) Q‖ ≤
        B * ∏ p ∈ S, (1 + 2 * primeSquareCorrectedWeight σ p) := by
    apply (norm_sum_le _ _).trans
    calc
      _ ≤ ∑ T ∈ S.powerset.filter (fun T ↦ 2 ≤ T.card), ∑ U ∈ (S \ T).powerset,
          B * ∏ p ∈ T ∪ U, primeSquareCorrectedWeight σ p := by
        apply Finset.sum_le_sum
        intro T hT
        apply (norm_sum_le _ _).trans
        apply Finset.sum_le_sum
        intro U hU
        rw [norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul]
        apply hb (T ∪ U)
        intro p hp
        apply (hS p _).1
        rcases Finset.mem_union.mp hp with hp | hp
        · exact Finset.mem_powerset.mp (Finset.mem_filter.mp hT).1 hp
        · exact (Finset.mem_sdiff.mp (Finset.mem_powerset.mp hU hp)).1
      _ = B * ∑ T ∈ S.powerset.filter (fun T ↦ 2 ≤ T.card), ∑ U ∈ (S \ T).powerset,
          ∏ p ∈ T ∪ U, primeSquareCorrectedWeight σ p := by simp_rw [Finset.mul_sum]
      _ ≤ _ := mul_le_mul_of_nonneg_left
        (sum_prime_patterns_product_le S _ (primeSquareCorrectedWeight_nonneg σ)) hB
  have hprod := prod_one_add_primeSquareCorrectedWeight_le S R hS hσ
  have he : 1 ≤ Real.exp (2 * primeSquareWeightMass σ) * Real.exp (4 * Real.sqrt R) := by
    rw [← Real.exp_add]
    exact Real.one_le_exp_iff.mpr (by nlinarith [primeSquareWeightMass_nonneg σ, Real.sqrt_nonneg (R : ℝ)])
  apply (norm_sub_le _ _).trans
  apply (add_le_add hbase hsum).trans
  have hb1 := mul_le_mul_of_nonneg_left he hB
  have hb2 := mul_le_mul_of_nonneg_left hprod hB
  dsimp [B] at *
  unfold primeSquareSurvivorCost
  nlinarith

end
end RiemannGaussian
