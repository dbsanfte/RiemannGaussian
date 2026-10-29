/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1BoundaryPlan

/-! # Exact minimum selection in the executable boundary partition
Selection uses the literal acquired potential. The local averaging identity
remains a separate prerequisite of the potential-descent composition.
-/
set_option autoImplicit false
set_option maxHeartbeats 200000
set_option Elab.async false

namespace RiemannGaussian.SemiprimeD1BoundaryChoice
open SemiprimeD1BoundaryPlan
open scoped BigOperators

/-- Actual colour, exact scaled potential, and evaluated work. -/
abbrev Candidate := Nat × Int × Nat

/-- Runtime strict comparison; ties retain the earlier candidate. -/
def prefer (best next : Candidate) : Candidate :=
  if next.2.1 < best.2.1 then next else best

/-- The literal evaluated candidate list. -/
def candidates (g : Graph) (k : Nat) (fixed : List Nat) : List Candidate :=
  (List.range k).map (fun c =>
    let p := potential g k (fixed ++ [c])
    (c, p.value, p.clock))

/-- Exact record retained by the selector's fold. -/
def best (g : Graph) (k : Nat) (fixed : List Nat) : Candidate :=
  (candidates g k fixed).foldl prefer ((candidates g k fixed).headD (0, 0, 0))

/-- This proof-side record exposes precisely the executed colour. -/
theorem leastCandidate_value (g : Graph) (k : Nat) (fixed : List Nat) :
    (leastCandidate g k fixed).value = (best g k fixed).1 := rfl

/-- Folding never increases the initial potential. -/
theorem fold_le_initial (xs : List Candidate) (initial : Candidate) :
    (xs.foldl prefer initial).2.1 ≤ initial.2.1 := by
  induction xs generalizing initial with
  | nil => rfl
  | cons head tail ih =>
    simp only [List.foldl_cons]
    apply (ih (prefer initial head)).trans
    unfold prefer
    split_ifs <;> omega

/-- Every actual candidate bounds the selected potential from above. -/
theorem fold_le_member (xs : List Candidate) (initial x : Candidate) (hx : x ∈ xs) :
    (xs.foldl prefer initial).2.1 ≤ x.2.1 := by
  induction xs generalizing initial with
  | nil => simp only [List.not_mem_nil] at hx
  | cons head tail ih =>
    simp only [List.foldl_cons]
    rcases List.mem_cons.mp hx with rfl | hx
    · apply (fold_le_initial tail (prefer initial x)).trans
      unfold prefer
      split_ifs <;> omega
    · exact ih (prefer initial head) hx

/-- Every property shared by the candidate records survives the fold. -/
theorem fold_property (P : Candidate → Prop) (xs : List Candidate) (initial : Candidate)
    (hi : P initial) (hx : ∀ x ∈ xs, P x) : P (xs.foldl prefer initial) := by
  induction xs generalizing initial with
  | nil => exact hi
  | cons head tail ih =>
    simp only [List.foldl_cons]
    apply ih
    · unfold prefer
      split_ifs
      · exact hx head List.mem_cons_self
      · exact hi
    · intro x hm
      exact hx x (List.mem_cons_of_mem head hm)

/-- Positive colour count supplies an actual nonempty candidate list. -/
theorem candidates_ne_nil (g : Graph) (k : Nat) (fixed : List Nat) (hk : 0 < k) :
    candidates g k fixed ≠ [] := by
  intro h
  have hh := congrArg List.length h
  simp only [candidates, List.length_map, List.length_range, List.length_nil] at hh
  omega

/-- The selected record was actually evaluated. -/
theorem best_mem (g : Graph) (k : Nat) (fixed : List Nat) (hk : 0 < k) :
    best g k fixed ∈ candidates g k fixed := by
  have hn := candidates_ne_nil g k fixed hk
  unfold best
  apply fold_property (fun x => x ∈ candidates g k fixed)
  · cases he : candidates g k fixed with
    | nil => exact False.elim (hn he)
    | cons head tail => simp only [List.headD_cons, List.mem_cons_self]
  · intro x hx
    exact hx

/-- Membership identifies the exact colour and acquired potential. -/
theorem candidate_spec (g : Graph) (k : Nat) (fixed : List Nat) (x : Candidate)
    (hx : x ∈ candidates g k fixed) :
    x.1 < k ∧ x.2.1 = (potential g k (fixed ++ [x.1])).value := by
  obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hx
  exact ⟨List.mem_range.mp hc, rfl⟩

/-- The returned colour is always in the actual menu. -/
theorem leastCandidate_lt (g : Graph) (k : Nat) (fixed : List Nat) (hk : 0 < k) :
    (leastCandidate g k fixed).value < k := by
  rw [leastCandidate_value]
  exact (candidate_spec g k fixed _ (best_mem g k fixed hk)).1

/-- Actual selected extension has no greater potential than any candidate. -/
theorem selected_le (g : Graph) (k : Nat) (fixed : List Nat) (hk : 0 < k)
    (c : Nat) (hc : c < k) :
    (potential g k (fixed ++ [(leastCandidate g k fixed).value])).value ≤
      (potential g k (fixed ++ [c])).value := by
  have hs := (candidate_spec g k fixed _ (best_mem g k fixed hk)).2
  let record : Candidate := (c, (potential g k (fixed ++ [c])).value,
    (potential g k (fixed ++ [c])).clock)
  have hm : record ∈ candidates g k fixed :=
    List.mem_map.mpr ⟨c, List.mem_range.mpr hc, rfl⟩
  have hh := fold_le_member (candidates g k fixed)
    ((candidates g k fixed).headD (0, 0, 0)) record hm
  rw [leastCandidate_value, ← hs]
  exact hh

/-- The exact local averaging identity implies one actual nonincreasing step. -/
theorem selected_le_current (g : Graph) (k : Nat) (fixed : List Nat) (hk : 0 < k)
    (haverage : (∑ c ∈ Finset.range k, (potential g k (fixed ++ [c])).value) =
      (k : Int) * (potential g k fixed).value) :
    (potential g k (fixed ++ [(leastCandidate g k fixed).value])).value ≤
      (potential g k fixed).value := by
  have hs := Finset.sum_le_sum (fun c hc =>
    selected_le g k fixed hk c (Finset.mem_range.mp hc))
  rw [haverage] at hs
  simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul] at hs
  exact (mul_le_mul_iff_right₀ (show (0 : Int) < k by exact_mod_cast hk)).mp hs

/-- The executed colour list has exactly the requested length. -/
theorem extend_length (g : Graph) (k n : Nat) (fixed : List Nat) :
    (extend g k n fixed).value.length = fixed.length + n := by
  induction n generalizing fixed with
  | zero => simp only [extend, Nat.add_zero]
  | succ n ih =>
    simp only [extend, ih, List.length_append, List.length_singleton]
    omega

/-- The executed integer search always returns a bounded positive colour count. -/
theorem chooseK_bounds (g : Graph) : 2 ≤ chooseK g ∧ chooseK g ≤ g.edges.length + 2 := by
  let xs := (List.range (g.edges.length + 1)).map (fun i => i + 2)
  let predicate := fun k => decide (g.edges.length ≤ k ^ 3 * maxDegree g)
  change 2 ≤ (xs.find? predicate).getD 2 ∧ (xs.find? predicate).getD 2 ≤ _
  cases h : xs.find? predicate with
  | none => simp only [Option.getD_none]; omega
  | some k =>
    have hm := List.mem_of_find?_eq_some h
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hm
    have hir := List.mem_range.mp hi
    simp only [Option.getD_some]
    omega

/-- The actual finite assignment loop keeps every selected colour in range. -/
theorem extend_colours (g : Graph) (k n : Nat) (fixed : List Nat) (hk : 0 < k)
    (hf : ∀ c ∈ fixed, c < k) : ∀ c ∈ (extend g k n fixed).value, c < k := by
  induction n generalizing fixed with
  | zero => exact hf
  | succ n ih =>
    apply ih
    intro c hc
    rcases List.mem_append.mp hc with hc | hc
    · exact hf c hc
    · have he := List.mem_singleton.mp hc
      rw [he]
      exact leastCandidate_lt g k fixed hk

/-- Closed acquisition creates exactly one colour for each original vertex. -/
theorem acquire_length (g : Graph) : (acquire g).colours.length = g.vertices := by
  exact (extend_length g (chooseK g) g.vertices []).trans (Nat.zero_add _)

/-- Closed acquisition uses only its own finite colour menu. -/
theorem acquire_colours (g : Graph) :
    ∀ c ∈ (acquire g).colours, c < (acquire g).k := by
  apply extend_colours g (chooseK g) g.vertices [] (by have h := (chooseK_bounds g).1; omega)
  simp only [List.not_mem_nil, false_implies, implies_true]

/-- Local averaging propagates through the whole executed finite assignment loop. -/
theorem extend_potential_le (g : Graph) (k n : Nat) (fixed : List Nat) (hk : 0 < k)
    (haverage : ∀ current : List Nat, fixed.length ≤ current.length →
      current.length < fixed.length + n →
      (∑ c ∈ Finset.range k, (potential g k (current ++ [c])).value) =
        (k : Int) * (potential g k current).value) :
    (potential g k (extend g k n fixed).value).value ≤ (potential g k fixed).value := by
  induction n generalizing fixed with
  | zero => rfl
  | succ n ih =>
    let next := fixed ++ [(leastCandidate g k fixed).value]
    have hh := selected_le_current g k fixed hk (haverage fixed le_rfl (by omega))
    have ht := ih next (by
      intro current hlo hhi
      apply haverage current
      · dsimp only [next] at hlo
        simp only [List.length_append, List.length_singleton] at hlo
        omega
      · dsimp only [next] at hhi
        simp only [List.length_append, List.length_singleton] at hhi
        omega)
    exact ht.trans hh

end RiemannGaussian.SemiprimeD1BoundaryChoice
