/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import Mathlib

/-!
# Streamed ternary Möbius menu

The recursion branches on exclusion, inclusion in S only, or inclusion in both
S and U. It sums callbacks immediately and never constructs the mask family.
The numerical choose estimate below is adapted from OpenAI Math, Apache-2.0,
commit 7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a,
OAI/Algorithms/SubexponentialSAT/BranchTree.lean, choose_le_rpow_real.
-/
set_option autoImplicit false
set_option maxHeartbeats 1600000
namespace RiemannGaussian.SemiprimeCounterEnumeration
open scoped BigOperators

variable {V A : Type*} [DecidableEq V] [AddCommMonoid A]

/-- The mathematical subset-pair menu, with inclusive support cutoff q. -/
def menu (s : Finset V) (q : ℕ) (f : Finset V → Finset V → A) : A :=
  ∑ S ∈ s.powerset, if S.card ≤ q then ∑ U ∈ S.powerset, f S U else 0

/-- Split a powerset sum without constructing its image in the traversal. -/
theorem sum_powerset_insert (s : Finset V) (a : V) (ha : a ∉ s)
    (f : Finset V → A) :
    (∑ S ∈ (insert a s).powerset, f S) =
      (∑ S ∈ s.powerset, f S) + ∑ S ∈ s.powerset, f (insert a S) := by
  rw [Finset.powerset_insert, Finset.sum_union]
  · congr 1
    apply Finset.sum_image
    intro x hx y hy he
    have hax := Finset.notMem_of_mem_powerset_of_notMem hx ha
    have hay := Finset.notMem_of_mem_powerset_of_notMem hy ha
    simpa only [Finset.erase_insert hax, Finset.erase_insert hay] using congrArg (Finset.erase · a) he
  · apply Finset.disjoint_left.mpr
    intro x hx him
    obtain ⟨y, _, rfl⟩ := Finset.mem_image.mp him
    exact ha ((Finset.mem_powerset.mp hx) (Finset.mem_insert_self a y))

/-- A zero budget traverses only the excluded branch. -/
theorem menu_insert_zero (s : Finset V) (a : V) (ha : a ∉ s)
    (f : Finset V → Finset V → A) : menu (insert a s) 0 f = menu s 0 f := by
  unfold menu
  rw [sum_powerset_insert s a ha]
  have hz : (∑ S ∈ s.powerset,
      if (insert a S).card ≤ 0 then ∑ U ∈ (insert a S).powerset, f (insert a S) U else 0) = 0 := by
    apply Finset.sum_eq_zero
    intro S hS
    have hnot := Finset.notMem_of_mem_powerset_of_notMem hS ha
    simp [Finset.card_insert_of_notMem hnot]
  rw [hz, add_zero]

/-- The exact three branches of the inclusive-budget subset-pair menu. -/
theorem menu_insert_succ (s : Finset V) (a : V) (ha : a ∉ s) (q : ℕ)
    (f : Finset V → Finset V → A) :
    menu (insert a s) (q+1) f = menu s (q+1) f +
      menu s q (fun S U => f (insert a S) U) +
      menu s q (fun S U => f (insert a S) (insert a U)) := by
  unfold menu
  rw [sum_powerset_insert s a ha]
  rw [add_assoc]
  congr 1
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro S hS
  have hnot := Finset.notMem_of_mem_powerset_of_notMem hS ha
  rw [Finset.card_insert_of_notMem hnot]
  simp only [Nat.add_le_add_iff_right]
  by_cases hb : S.card ≤ q
  · simp only [ite_eq_left hb]
    exact sum_powerset_insert S a hnot (f (insert a S))
  · simp only [ite_eq_right hb, add_zero]

/-- Actual depth-first traversal: only three recursive scalar results are kept. -/
def stream : List V → ℕ → (Finset V → Finset V → A) → A
  | [], _, f => f ∅ ∅
  | _ :: tail, 0, f => stream tail 0 f
  | a :: tail, q+1, f => stream tail (q+1) f +
      stream tail q (fun S U => f (insert a S) U) +
      stream tail q (fun S U => f (insert a S) (insert a U))

/-- The traversal equals the full finite Möbius menu for every additive callback. -/
theorem stream_eq_menu (todo : List V) (hn : todo.Nodup) (q : ℕ)
    (f : Finset V → Finset V → A) : stream todo q f = menu todo.toFinset q f := by
  induction todo generalizing q f with
  | nil => simp [stream, menu]
  | cons a tail ih =>
    obtain ⟨ha, ht⟩ := List.nodup_cons.mp hn
    have ha' : a ∉ tail.toFinset := by simpa using ha
    cases q with
    | zero => simpa only [stream, List.toFinset_cons, menu_insert_zero _ _ ha'] using ih ht 0 f
    | succ q =>
      simp only [stream, List.toFinset_cons, menu_insert_succ _ _ ha', ih ht]

/-- Exact number of callbacks on a length-n menu. -/
def callbacks : ℕ → ℕ → ℕ
  | 0, _ => 1
  | n+1, 0 => callbacks n 0
  | n+1, q+1 => callbacks n (q+1) + callbacks n q + callbacks n q

/-- Inclusive weighted binomial count; the strict Taylor width is J=q+1. -/
def weightedCount (n q : ℕ) : ℕ := ∑ j ∈ Finset.range (q+1), 2^j * n.choose j

@[simp] theorem weightedCount_zero (n : ℕ) : weightedCount n 0 = 1 := by
  simp [weightedCount]

/-- Increasing the inclusive support cutoff adds its last weighted binomial. -/
theorem weightedCount_succ (n q : ℕ) :
    weightedCount n (q+1) = weightedCount n q + 2^(q+1)*n.choose (q+1) := by
  exact Finset.sum_range_succ _ _

/-- Pascal's rule for the ternary traversal. -/
theorem weightedCount_pascal (n q : ℕ) :
    weightedCount (n+1) (q+1) = weightedCount n (q+1) +
      weightedCount n q + weightedCount n q := by
  induction q with
  | zero => simp [weightedCount, Finset.sum_range_succ, Nat.choose_succ_succ]; omega
  | succ q ih =>
    rw [weightedCount_succ (n+1) (q+1), ih,
      Nat.choose_succ_succ, weightedCount_succ n (q+1), weightedCount_succ n q, pow_succ]
    ring

/-- Every callback is counted exactly, including the empty-support callback. -/
theorem callbacks_eq_weightedCount (n q : ℕ) : callbacks n q = weightedCount n q := by
  induction n generalizing q with
  | zero =>
    rw [weightedCount, Finset.sum_range_succ']
    simp [callbacks]
  | succ n ih =>
    cases q with
    | zero => simp [callbacks, ih]
    | succ q => rw [callbacks, ih, ih, weightedCount_pascal]

/-- The actual traversal with counters attached to the same recursive calls. -/
structure Report (A : Type*) where
  /-- The accumulated callback value. -/
  value : A
  /-- Number of callback invocations. -/
  callbacks : ℕ
  /-- Number of traversal nodes. -/
  nodes : ℕ
  /-- Maximum recursive depth. -/
  depth : ℕ

/-- Instrumented scalar traversal; no output-mask list is returned. -/
def tracked : List V → ℕ → (Finset V → Finset V → A) → Report A
  | [], _, f => ⟨f ∅ ∅, 1, 1, 0⟩
  | _ :: tail, 0, f =>
      let r := tracked tail 0 f
      ⟨r.value, r.callbacks, r.nodes+1, r.depth+1⟩
  | a :: tail, q+1, f =>
      let e := tracked tail (q+1) f
      let s := tracked tail q (fun S U => f (insert a S) U)
      let u := tracked tail q (fun S U => f (insert a S) (insert a U))
      ⟨e.value+s.value+u.value, e.callbacks+s.callbacks+u.callbacks,
        e.nodes+s.nodes+u.nodes+1, max e.depth (max s.depth u.depth)+1⟩

/-- Values and callback counts refer to the same executed traversal. -/
theorem tracked_correct (todo : List V) (q : ℕ) (f : Finset V → Finset V → A) :
    (tracked todo q f).value = stream todo q f ∧
      (tracked todo q f).callbacks = callbacks todo.length q ∧
      (tracked todo q f).nodes ≤ (todo.length+1)*callbacks todo.length q ∧
      (tracked todo q f).depth = todo.length := by
  induction todo generalizing q f with
  | nil => simp [tracked, stream, callbacks]
  | cons a tail ih =>
    cases q with
    | zero =>
      have h := ih 0 f
      simp only [tracked, stream, callbacks, List.length_cons]
      refine ⟨h.1, h.2.1, ?_, by omega⟩
      have hc : 1 ≤ callbacks tail.length 0 := by
        rw [callbacks_eq_weightedCount, weightedCount_zero]
      nlinarith [h.2.2.1]
    | succ q =>
      have he := ih (q+1) f
      have hs := ih q (fun S U => f (insert a S) U)
      have hu := ih q (fun S U => f (insert a S) (insert a U))
      simp only [tracked, stream, callbacks, List.length_cons]
      refine ⟨by rw [he.1, hs.1, hu.1], by rw [he.2.1, hs.2.1, hu.2.1], ?_, ?_⟩
      · have hc : 1 ≤ callbacks tail.length (q+1) := by
          rw [callbacks_eq_weightedCount]
          have h := Finset.single_le_sum (s := Finset.range (q+1+1))
            (f := fun j => 2^j * tail.length.choose j) (a := 0)
            (fun _ _ => Nat.zero_le _) (by simp)
          simpa only [weightedCount, pow_zero, Nat.choose_zero_right, one_mul] using h
        nlinarith [he.2.2.1, hs.2.2.1, hu.2.2.1, he.2.1, hs.2.1, hu.2.1]
      · rw [he.2.2.2, hs.2.2.2, hu.2.2.2, max_self, max_self]

/-- Correctness, exact callback count and depth are attached to one traversal. -/
theorem tracked_menu (todo : List V) (hn : todo.Nodup) (q : ℕ)
    (f : Finset V → Finset V → A) :
    (tracked todo q f).value = menu todo.toFinset q f ∧
      (tracked todo q f).callbacks = weightedCount todo.length q ∧
      (tracked todo q f).nodes ≤ (todo.length+1)*weightedCount todo.length q ∧
      (tracked todo q f).depth = todo.length := by
  have h := tracked_correct todo q f
  rw [stream_eq_menu todo hn q f, callbacks_eq_weightedCount] at h
  exact h

/-- Published real-cutoff binomial estimate, adapted from OpenAI Math
BranchTree.choose_le_rpow_real at the pinned Apache-2.0 source cited above. -/
theorem choose_le_rpow_real (n j : ℕ) {u : ℝ} (hu : 0 < u)
    (hun : u ≤ n) (hj : (j : ℝ) ≤ u) :
    (n.choose j : ℝ) ≤ (4*(n : ℝ)/u)^u := by
  have hbase : 1 ≤ (n : ℝ)/u := (le_div_iff₀ hu).2 (by simpa using hun)
  have hnonneg : 0 ≤ (n : ℝ)/u := le_trans zero_le_one hbase
  have hsplit : (n : ℝ)^j/(j.factorial : ℝ) =
      ((n : ℝ)/u)^j * (u^j/(j.factorial : ℝ)) := by
    rw [div_pow]
    field_simp
  have hpow : ((n : ℝ)/u)^j ≤ ((n : ℝ)/u)^u := by
    simpa only [Real.rpow_natCast] using Real.rpow_le_rpow_of_exponent_le hbase hj
  have hexp : Real.exp u ≤ (4 : ℝ)^u := by
    rw [← Real.exp_one_rpow]
    exact Real.rpow_le_rpow (Real.exp_nonneg _) (by linarith [Real.exp_one_lt_d9]) hu.le
  calc
    (n.choose j : ℝ) ≤ (n : ℝ)^j/(j.factorial : ℝ) := Nat.choose_le_pow_div j n
    _ = ((n : ℝ)/u)^j * (u^j/(j.factorial : ℝ)) := hsplit
    _ ≤ ((n : ℝ)/u)^j * Real.exp u :=
      mul_le_mul_of_nonneg_left (Real.pow_div_factorial_le_exp u hu.le j) (pow_nonneg hnonneg j)
    _ ≤ ((n : ℝ)/u)^u * Real.exp u := mul_le_mul_of_nonneg_right hpow (Real.exp_nonneg u)
    _ ≤ ((n : ℝ)/u)^u * (4 : ℝ)^u :=
      mul_le_mul_of_nonneg_left hexp (Real.rpow_nonneg hnonneg _)
    _ = (4*(n : ℝ)/u)^u := by
      rw [← Real.mul_rpow hnonneg (by norm_num : (0 : ℝ) ≤ 4)]
      congr 1
      ring

/-- Weighted Möbius entropy includes the 2^j choices of U inside each support. -/
theorem weightedCount_le_entropy (n q : ℕ) {u : ℝ} (hu : 0 < u)
    (hun : u ≤ n) (hqu : (q : ℝ) ≤ u) :
    (weightedCount n q : ℝ) ≤ ((q : ℝ)+1) * (8*(n : ℝ)/u)^u := by
  unfold weightedCount
  push_cast
  have hterm (j : ℕ) (hj : j ∈ Finset.range (q+1)) :
      (2 : ℝ)^j * (n.choose j : ℝ) ≤ (8*(n : ℝ)/u)^u := by
    have hju : (j : ℝ) ≤ u :=
      (Nat.cast_le.mpr (Nat.le_of_lt_succ (Finset.mem_range.mp hj))).trans hqu
    have htwo : (2 : ℝ)^j ≤ (2 : ℝ)^u := by
      simpa only [Real.rpow_natCast] using
        Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2) hju
    calc
      _ ≤ (2 : ℝ)^u * (4*(n : ℝ)/u)^u :=
        mul_le_mul htwo (choose_le_rpow_real n j hu hun hju)
          (Nat.cast_nonneg _) (Real.rpow_nonneg (by norm_num) _)
      _ = (8*(n : ℝ)/u)^u := by
        rw [← Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2) (by positivity)]
        congr 1
        ring
  calc
    ∑ j ∈ Finset.range (q+1), (2 : ℝ)^j * (n.choose j : ℝ) ≤
        ∑ _j ∈ Finset.range (q+1), (8*(n : ℝ)/u)^u := Finset.sum_le_sum hterm
    _ = _ := by simp

/-- The counter's strict Taylor width J=q+1 uses every support of size at most q. -/
theorem strict_width_callbacks (todo : List V) (q : ℕ)
    (f : Finset V → Finset V → A) :
    (tracked todo q f).callbacks =
      ∑ j ∈ Finset.range (q+1), 2^j * todo.length.choose j := by
  rw [(tracked_correct todo q f).2.1, callbacks_eq_weightedCount]
  rfl

end RiemannGaussian.SemiprimeCounterEnumeration

#print axioms RiemannGaussian.SemiprimeCounterEnumeration.tracked_menu
#print axioms RiemannGaussian.SemiprimeCounterEnumeration.weightedCount_le_entropy
