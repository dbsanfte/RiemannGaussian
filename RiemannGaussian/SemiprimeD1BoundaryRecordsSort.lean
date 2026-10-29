/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1BoundaryRecordsOrder
import Mathlib.Data.Nat.Size

/-! # Correctness and logarithmic pass budget of the actual bottom-up sort
Theorems concern BoundaryRecords.sort itself, including its explicit fuel and
EOF cases. Every full payload is preserved, without an equality instance on
records or a supplied sorted permutation.
-/
set_option autoImplicit false
namespace RiemannGaussian.SemiprimeD1BoundaryRecordsSort
open SemiprimeD1BoundaryRecordsOrder
open SemiprimeD1BoundaryRecords (Entry)

/-- With its paid record budget the actual merge agrees with the standard
stable merge under the very same actual key comparator. -/
theorem mergeFuel_value (fuel : Nat) (xs ys : List Entry)
    (hf : xs.length+ys.length ≤ fuel) :
    (SemiprimeD1BoundaryRecords.mergeFuel fuel xs ys).value=List.merge xs ys entryLe := by
  induction fuel generalizing xs ys with
  | zero =>
    have hx : xs=[] := List.length_eq_zero_iff.mp (by omega)
    have hy : ys=[] := List.length_eq_zero_iff.mp (by omega)
    subst xs; subst ys
    simp [SemiprimeD1BoundaryRecords.mergeFuel,SemiprimeD1BoundaryRecords.copyEntries]
  | succ fuel ih =>
    cases xs with
    | nil => cases ys <;> simp [SemiprimeD1BoundaryRecords.mergeFuel,SemiprimeD1BoundaryRecords.copyEntries]
    | cons x xs =>
      cases ys with
      | nil => simp [SemiprimeD1BoundaryRecords.mergeFuel,SemiprimeD1BoundaryRecords.copyEntries]
      | cons y ys =>
        have hx : xs.length+(y::ys).length ≤ fuel := by simp only [List.length_cons] at hf ⊢; omega
        have hy : (x::xs).length+ys.length ≤ fuel := by simp only [List.length_cons] at hf ⊢; omega
        by_cases h : (SemiprimeD1BoundaryRecords.compareKey x.key y.key).value=Ordering.gt
        · simp [SemiprimeD1BoundaryRecords.mergeFuel,h,ih _ _ hy,
            entryLe,EntryLE,KeyLE]
        · simp [SemiprimeD1BoundaryRecords.mergeFuel,h,ih _ _ hx,
            entryLe,EntryLE,KeyLE]

/-- The real merge's own length-derived fuel is sufficient. -/
theorem merge_value (xs ys : List Entry) :
    (SemiprimeD1BoundaryRecords.merge xs ys).value=List.merge xs ys entryLe :=
  mergeFuel_value _ _ _ le_rfl

/-- Every full entry, with multiplicity and payload, survives a real merge. -/
theorem merge_perm (xs ys : List Entry) :
    (SemiprimeD1BoundaryRecords.merge xs ys).value.Perm (xs++ys) := by
  rw [merge_value]
  exact List.merge_perm_append entryLe

/-- Each real merge preserves the exact total record count. -/
theorem merge_length (xs ys : List Entry) :
    (SemiprimeD1BoundaryRecords.merge xs ys).value.length=xs.length+ys.length := by
  simpa only [List.length_append] using (merge_perm xs ys).length_eq

/-- Merging nondecreasing runs produces a nondecreasing actual output. -/
theorem merge_sorted (xs ys : List Entry) (hx : xs.Pairwise EntryLE) (hy : ys.Pairwise EntryLE) :
    (SemiprimeD1BoundaryRecords.merge xs ys).value.Pairwise EntryLE := by
  let : Std.Total EntryLE := ⟨entryLE_total⟩
  let : IsTrans Entry EntryLE := ⟨entryLE_trans⟩
  rw [merge_value]
  exact hx.merge hy

/-- One actual adjacent-run pass preserves every flattened full record. -/
theorem mergePass_perm : ∀runs : List (List Entry),
    (SemiprimeD1BoundaryRecords.mergePass runs).value.flatten.Perm runs.flatten
  | [] => by simp [SemiprimeD1BoundaryRecords.mergePass]
  | [xs] => by simp [SemiprimeD1BoundaryRecords.mergePass]
  | xs::ys::rest => by
    have h := (merge_perm xs ys).append (mergePass_perm rest)
    simpa only [SemiprimeD1BoundaryRecords.mergePass,List.flatten_cons,List.append_assoc] using h

/-- A merge pass visits the same total number of records. -/
theorem mergePass_flatten_length (runs : List (List Entry)) :
    (SemiprimeD1BoundaryRecords.mergePass runs).value.flatten.length=runs.flatten.length :=
  (mergePass_perm runs).length_eq

/-- Every real pass halves the number of runs with the exact ceiling. -/
theorem mergePass_length : ∀runs : List (List Entry),
    (SemiprimeD1BoundaryRecords.mergePass runs).value.length=(runs.length+1)/2
  | [] => by simp [SemiprimeD1BoundaryRecords.mergePass]
  | [xs] => by simp [SemiprimeD1BoundaryRecords.mergePass]
  | xs::ys::rest => by
    simp only [SemiprimeD1BoundaryRecords.mergePass,List.length_cons]
    rw [mergePass_length rest]
    omega

/-- Every output run inherits sortedness from the actual input runs. -/
theorem mergePass_sorted : ∀runs : List (List Entry),
    (∀xs∈runs,xs.Pairwise EntryLE) →
      ∀xs∈(SemiprimeD1BoundaryRecords.mergePass runs).value,xs.Pairwise EntryLE
  | [],h => by simp [SemiprimeD1BoundaryRecords.mergePass]
  | [xs],h => by simpa [SemiprimeD1BoundaryRecords.mergePass] using h
  | xs::ys::rest,h => by
    intro run hr
    simp only [SemiprimeD1BoundaryRecords.mergePass,List.mem_cons] at hr
    rcases hr with rfl | hr
    · exact merge_sorted xs ys (h xs (by simp)) (h ys (by simp))
    · exact mergePass_sorted rest (by intro r hr; exact h r (by simp [hr])) run hr

/-- Even an insufficient pass budget preserves all entries via its explicit
flatten fallback. This statement does not claim that fallback is sorted. -/
theorem sortPasses_perm (fuel : Nat) (runs : List (List Entry)) :
    (SemiprimeD1BoundaryRecords.sortPasses fuel runs).value.Perm runs.flatten := by
  induction fuel generalizing runs with
  | zero =>
    cases runs with
    | nil => simp [SemiprimeD1BoundaryRecords.sortPasses]
    | cons xs rest => cases rest <;> simp [SemiprimeD1BoundaryRecords.sortPasses,SemiprimeD1BoundaryRecords.copyEntries]
  | succ fuel ih =>
    cases runs with
    | nil => simp [SemiprimeD1BoundaryRecords.sortPasses]
    | cons xs rest =>
      cases rest with
      | nil => simp [SemiprimeD1BoundaryRecords.sortPasses]
      | cons ys rest =>
        exact (ih _).trans (mergePass_perm (xs::ys::rest))

/-- A binary run-count budget is sufficient for actual sorted termination. -/
theorem sortPasses_sorted (fuel : Nat) (runs : List (List Entry))
    (hcount : runs.length ≤ 2^fuel) (hs : ∀xs∈runs,xs.Pairwise EntryLE) :
    (SemiprimeD1BoundaryRecords.sortPasses fuel runs).value.Pairwise EntryLE := by
  induction fuel generalizing runs with
  | zero =>
    cases runs with
    | nil => simp [SemiprimeD1BoundaryRecords.sortPasses]
    | cons xs rest =>
      cases rest with
      | nil => simpa [SemiprimeD1BoundaryRecords.sortPasses] using hs xs (by simp)
      | cons ys rest => simp only [List.length_cons,pow_zero] at hcount; omega
  | succ fuel ih =>
    cases runs with
    | nil => simp [SemiprimeD1BoundaryRecords.sortPasses]
    | cons xs rest =>
      cases rest with
      | nil => simpa [SemiprimeD1BoundaryRecords.sortPasses] using hs xs (by simp)
      | cons ys rest =>
        have hp : (SemiprimeD1BoundaryRecords.mergePass (xs::ys::rest)).value.length ≤ 2^fuel := by
          rw [mergePass_length]
          simp only [List.length_cons,pow_succ] at hcount ⊢
          omega
        exact ih _ hp (mergePass_sorted _ hs)

/-- The actual sort preserves complete entries and every repeated occurrence. -/
theorem sort_perm (es : List Entry) : (SemiprimeD1BoundaryRecords.sort es).value.Perm es := by
  have h := sortPasses_perm (Nat.size es.length+1) (es.map (fun e => [e]))
  simpa only [SemiprimeD1BoundaryRecords.sort,←List.flatMap_def,List.flatMap_singleton'] using h

/-- Exact output cardinality of the actual closed sort. -/
theorem sort_length (es : List Entry) : (SemiprimeD1BoundaryRecords.sort es).value.length=es.length :=
  (sort_perm es).length_eq

/-- The closed length-derived pass budget produces lexicographic key order. -/
theorem sort_sorted (es : List Entry) : (SemiprimeD1BoundaryRecords.sort es).value.Pairwise EntryLE := by
  apply sortPasses_sorted (Nat.size es.length+1) (es.map (fun e => [e]))
  · simp only [List.length_map]
    exact (Nat.lt_size_self es.length).le.trans
      (Nat.pow_le_pow_right (by decide : 0<(2:Nat)) (Nat.le_succ _))
  · intro run hr
    obtain ⟨e,_,rfl⟩ := List.mem_map.mp hr
    simp

end RiemannGaussian.SemiprimeD1BoundaryRecordsSort
