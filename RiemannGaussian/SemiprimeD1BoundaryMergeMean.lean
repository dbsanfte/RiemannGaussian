/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1BoundaryInitialVariance
import RiemannGaussian.SemiprimeD1BoundaryVariance

/-! # Exact mean of the consecutive three-region merge load -/
set_option autoImplicit false
namespace RiemannGaussian.SemiprimeD1BoundaryMergeMean
open SemiprimeD1BoundaryPlan SemiprimeD1BoundaryInitialVariance

/-- Count a lower initial interval in the actual ascending colour list. -/
theorem count_lt (k t : Nat) :
    ((List.range k).filter (fun a => decide (a < t))).length = min k t := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [List.range_succ, List.filter_append, List.length_append, ih]
    by_cases h : k < t <;> simp [h] <;> omega

/-- Count the complementary upper interval in the same literal list. -/
theorem count_ge (k t : Nat) :
    ((List.range k).filter (fun a => decide (t ≤ a))).length = k - min k t := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [List.range_succ, List.filter_append, List.length_append, ih]
    by_cases h : t ≤ k <;> simp [h] <;> omega

/-- Every successful new-class coordinate has exactly one colour. -/
theorem count_ne (k t : Nat) :
    ((List.range k).filter (fun a => !(a == t))).length =
      k - if t < k then 1 else 0 := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [List.range_succ, List.filter_append, List.length_append, ih]
    by_cases h : k = t
    · subst k
      simp
    · have he : (k == t) = false := beq_eq_false_iff_ne.mpr h
      simp only [List.filter_cons, he, Bool.not_false, List.filter_nil, ite_true,
        List.length_cons, List.length_nil]
      split_ifs <;> omega

/-- Sum constant weights over the three literal regions without dropping a colour. -/
theorem sum_regions (xs : List Nat) (t a b c : Nat) :
    (xs.map (fun x => if x < t then a else if x == t then b else c)).sum =
      (xs.filter (fun x => decide (x < t))).length * a +
      (xs.filter (fun x => x == t)).length * b +
      (xs.filter (fun x => decide (t + 1 ≤ x))).length * c := by
  have point (x : Nat) :
      (if x < t then a else if x == t then b else c) =
      (if decide (x < t) then a else 0) + (if x == t then b else 0) +
        (if decide (t + 1 ≤ x) then c else 0) := by
    by_cases h : x < t
    · have he : (x == t) = false := beq_eq_false_iff_ne.mpr (by omega)
      have ht : ¬ t + 1 ≤ x := by omega
      simp only [h, he, ht, decide_true, decide_false, ite_true, ite_false,
        Bool.false_eq_true, Nat.add_zero]
    · by_cases heq : x = t
      · subst x
        simp
      · have he : (x == t) = false := beq_eq_false_iff_ne.mpr heq
        have ht : t + 1 ≤ x := by omega
        simp only [h, he, ht, decide_false, decide_true, ite_false, ite_true,
          Bool.false_eq_true, Nat.zero_add]
  have he : xs.map (fun x => if x < t then a else if x == t then b else c) =
      xs.map (fun x => (if decide (x < t) then a else 0) + (if x == t then b else 0) +
        (if decide (t + 1 ≤ x) then c else 0)) := by
    apply List.map_congr_left
    intro x _
    exact point x
  rw [he, List.sum_map_add, List.sum_map_add,
    sum_success_weight, sum_success_weight, sum_success_weight]

/-- One first-endpoint colour has its exact complementary-region population. -/
theorem row_count (k j a : Nat) (hj : 2 ≤ j) (hjk : j ≤ k) :
    ((List.range k).filter (fun b => indicator (.merge j) a b)).length =
      if a < j - 1 then k - (j - 1) else if a == j - 1 then k - 1 else j := by
  by_cases ha : a < j - 1
  · have he : (fun b => indicator (.merge j) a b) = (fun b => decide (j - 1 ≤ b)) := by
      funext b
      by_cases hb : b < j - 1 <;> by_cases he : b = j - 1 <;>
        simp [indicator, region, ha, hb, he] <;> omega
    rw [he, count_ge, min_eq_right (by omega : j - 1 ≤ k), ite_eq_left ha]
  · by_cases heq : a = j - 1
    · have he : (fun b => indicator (.merge j) a b) = (fun b => !(b == j - 1)) := by
        funext b
        by_cases hb : b < j - 1 <;> by_cases he : b = j - 1 <;>
          simp [indicator, region, heq, hb, he]
      rw [he, count_ne]
      simp [heq, show j - 1 < k by omega]
    · have he : (fun b => indicator (.merge j) a b) = (fun b => decide (b < j)) := by
        funext b
        by_cases hb : b < j - 1 <;> by_cases he : b = j - 1 <;>
          simp [indicator, region, ha, heq, hb, he] <;> omega
      rw [he, count_lt, min_eq_right hjk]
      simp [ha, heq]

/-- The exact executable two-colour mean numerator for every actual merge. -/
theorem eventCount_merge (k j : Nat) (hj : 2 ≤ j) (hjk : j ≤ k) :
    eventCount k (.merge j) = 2 * (j * (k + 1 - j) - 1) := by
  have he : colourWords k 2 = (List.range k).flatMap (fun a =>
      (List.range k).map (fun b => [a, b])) := by
    simp [colourWords, ←List.map_eq_flatMap, Function.comp_def]
  unfold eventCount
  rw [he, List.filter_flatMap, List.length_flatMap]
  have hrow (a : Nat) :
      (((List.range k).map (fun b => [a, b])).filter (fun sample =>
        indicator (.merge j) (sample.getD 0 0) (sample.getD 1 0))).length =
      if a < j - 1 then k - (j - 1) else if a == j - 1 then k - 1 else j := by
    rw [List.filter_map, List.length_map]
    simpa only [Function.comp_def, List.getD_cons_zero, List.getD_cons_succ] using row_count k j a hj hjk
  simp_rw [hrow]
  rw [sum_regions, count_lt, count_ge]
  have hjm : j - 1 < k := by omega
  simp only [min_eq_right (by omega : j - 1 ≤ k), List.filter_beq,
    List.count_range, hjm, ite_true, List.length_replicate, Nat.one_mul]
  rw [show j - 1 + 1 = j by omega, min_eq_right hjk]
  have h1 := Nat.sub_add_cancel (show 1 ≤ j by omega)
  have h2 := Nat.sub_add_cancel hjk
  have h3 := Nat.sub_add_cancel (show j ≤ k + 1 by omega)
  have h4 := Nat.sub_add_cancel (show 1 ≤ j * (k + 1 - j) by nlinarith)
  have h5 := Nat.sub_add_cancel (show j - 1 ≤ k by omega)
  have h6 := Nat.sub_add_cancel (show 1 ≤ k by omega)
  nlinarith

/-- Every executed load uses exactly its literal unconditional event mean. -/
theorem mean_identity (m k : Nat) (hk : 2 ≤ k) (load : Load) (hl : load ∈ loads k) :
    meanNumerator m k load = m * eventCount k load := by
  rcases List.mem_append.mp hl with hb | hm
  · obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hb
    rw [eventCount_bucket k c (List.mem_range.mp hc)]
    rfl
  · obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hm
    have hir := List.mem_range.mp hi
    rw [eventCount_merge k (i + 2) (by omega) (by omega)]
    simp only [meanNumerator]
    ring

/-- Closed whole-family variance bound for the actual initial integer potential. -/
theorem initial_bound (g : Graph) (k : Nat)
    (hg : SemiprimeD1BoundaryPotential.Valid g) (hk : 2 ≤ k) :
    ((potential g k []).value : Real) ≤
      (k : Real)^4 * ((2 * k - 1 : Nat) : Real) *
        (g.edges.length : Real) * (maxDegree g : Real) / 2 := by
  exact SemiprimeD1BoundaryVariance.initial_potential_real_bound g k hg (by omega)
    (mean_identity g.edges.length k hk)

end RiemannGaussian.SemiprimeD1BoundaryMergeMean
