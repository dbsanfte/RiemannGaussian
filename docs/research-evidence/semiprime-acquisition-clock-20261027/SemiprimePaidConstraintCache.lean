/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeMaterializedSourceCache
import RiemannGaussian.SemiprimeSourceConstraintAcquisition

/-! # Paid cached universal integer constraints
The numerator family is acquired by the existing actual parity/difference
program. Each later constraint reads that finite family by executed list scans.
The report counts scalar/register/list work; physical bit refinement is separate.
-/
set_option autoImplicit false
set_option maxHeartbeats 1600000
namespace RiemannGaussian.SemiprimePaidConstraintCache
open OAI.Algorithms.SubexponentialSAT
open MulticolorTypes SqrtLog
open SemiprimeMaterializedSourceUniversal
variable {r Q : ℕ}

/-- Actual finite list access, including all visited cells. -/
def getRun {α : Type*} : List α → ℕ → Run (Option α)
  | [], _ => ⟨none,1⟩
  | a::_, 0 => ⟨some a,2⟩
  | _::as, k+1 => let tail := getRun as k; ⟨tail.value,tail.work+2⟩

theorem getRun_value {α : Type*} (xs : List α) (k : ℕ) :
    (getRun xs k).value=xs[k]? := by
  induction xs generalizing k with
  | nil => simp [getRun]
  | cons a as ih => cases k <;> simp [getRun,ih]

theorem getRun_work {α : Type*} (xs : List α) (k : ℕ) :
    (getRun xs k).work≤2*xs.length+1 := by
  induction xs generalizing k with
  | nil => simp [getRun]
  | cons a as ih =>
      cases k with
      | zero => simp only [getRun,List.length_cons]; omega
      | succ k =>
          have ht := ih k
          simp only [getRun,List.length_cons]
          omega

/-- Read one stored original universal numerator with two keyed scans. -/
def numerator (keys : List (UniversalType r Q 1)) (cache : List (List (List ℤ)))
    (t : Fin Q) (u y : UniversalType r Q 1) : Run ℤ :=
  let node := getRun cache t.val
  let row := SemiprimeMaterializedSourceCache.lookup u keys (node.value.getD [])
  let entry := SemiprimeMaterializedSourceCache.lookup y keys (row.value.getD [])
  ⟨entry.value.getD 0,node.work+row.work+entry.work+3⟩

/-- Actual cached acquisition, not an externally supplied numerator function. -/
theorem numerator_value (A R : ℕ) (keys : List (UniversalType r Q 1))
    (complete : ∀ u, u∈keys) (t : Fin Q) (u y : UniversalType r Q 1) :
    (numerator keys (table A R keys).value t u y).value=LayoutNumerator.entry 0 t A R u y := by
  unfold numerator
  dsimp only
  rw [getRun_value,table_value]
  have ht : (List.finRange Q)[t.val]?=some t := by
    rw [List.getElem?_eq_getElem (by simp),List.getElem_finRange]
    congr 1
  simp only [List.getElem?_map,ht,Option.map_some,Option.getD_some]
  rw [SemiprimeMaterializedSourceCache.lookup_map u keys _ (complete u)]
  simp only [Option.getD_some]
  rw [SemiprimeMaterializedSourceCache.lookup_map y keys _ (complete y)]
  rfl

theorem numerator_work (keys : List (UniversalType r Q 1)) (cache : List (List (List ℤ)))
    (t : Fin Q) (u y : UniversalType r Q 1) :
    (numerator keys cache t u y).work≤2*cache.length+2*(keys.length*(7*Q+4)+1)+4 := by
  have hn := getRun_work cache t.val
  have hr := SemiprimeMaterializedSourceCache.lookup_work u keys
    ((getRun cache t.val).value.getD [])
  have he := SemiprimeMaterializedSourceCache.lookup_work y keys
    ((SemiprimeMaterializedSourceCache.lookup u keys ((getRun cache t.val).value.getD [])).value.getD [])
  unfold numerator
  dsimp only
  omega

/-- A cleared-defect entry; all head tests and complete equality comparisons execute. -/
def constraint (denominator : ℤ) (keys : List (UniversalType r Q 1))
    (cache : List (List (List ℤ))) (t : Fin Q) (g : Fin r)
    (u y : UniversalType r Q 1) : Run ℤ :=
  if u.head t=g ∧ u.slot 0 t≠g then
    if y.head t=g ∧ y.slot 0 t≠g then
      let entry := numerator keys cache t u y
      let eq := SemiprimeMaterializedSourceCache.same u y
      ⟨(if eq.value then denominator else 0)-entry.value,entry.work+eq.work+11⟩
    else ⟨0,8⟩
  else ⟨0,4⟩

/-- Exactly the original padded constraint, including every zero-padding branch. -/
theorem constraint_value (A R : ℕ) (keys : List (UniversalType r Q 1))
    (complete : ∀ u, u∈keys) (t : Fin Q) (g : Fin r) (u y : UniversalType r Q 1) :
    (constraint ((powerTwo (R-1)).value) keys (table A R keys).value t g u y).value=
      SemiprimeUniversalSourceExecution.constraint A R t g u y := by
  unfold constraint SemiprimeUniversalSourceExecution.constraint
  split_ifs <;> simp_all only [numerator_value A R keys complete,
    SemiprimeMaterializedSourceCache.same_correct,powerTwo_value,
    SemiprimeUniversalSourceExecution.numerator_eq,ite_true,ite_false]

theorem constraint_work (denominator : ℤ) (keys : List (UniversalType r Q 1))
    (cache : List (List (List ℤ))) (t : Fin Q) (g : Fin r)
    (u y : UniversalType r Q 1) :
    (constraint denominator keys cache t g u y).work≤
      2*cache.length+2*(keys.length*(7*Q+4)+1)+7*Q+16 := by
  have hn := numerator_work keys cache t u y
  have he := SemiprimeMaterializedSourceCache.same_work u y
  unfold constraint
  split_ifs <;> dsimp only <;> omega

/-- Immutable integer numerator table and its acquired denominator. -/
structure Cache where
  /-- Original universal alphabet in its source order. -/
  keys : List (UniversalType r Q 1)
  /-- One acquired Q-by-D-by-D numerator family. -/
  entries : List (List (List ℤ))
  /-- Acquired power of two used to clear the universal defect. -/
  denominator : ℤ

/-- Acquire all universal numerator data once, before any original-coordinate scans. -/
def acquire (A R : ℕ) (keys : List (UniversalType r Q 1)) : Run (Cache (r:=r) (Q:=Q)) :=
  let entries := table A R keys
  let denominator := powerTwo (R-1)
  ⟨⟨keys,entries.value,denominator.value⟩,entries.work+denominator.work+3⟩

/-- Runtime read from the actual acquired universal integer data. -/
def read (cache : Cache (r:=r) (Q:=Q)) (t : Fin Q) (g : Fin r)
    (u y : UniversalType r Q 1) : Run ℤ :=
  constraint cache.denominator cache.keys cache.entries t g u y

theorem read_acquire (A R : ℕ) (keys : List (UniversalType r Q 1))
    (complete : ∀ u, u∈keys) (t : Fin Q) (g : Fin r) (u y : UniversalType r Q 1) :
    (read (acquire A R keys).value t g u y).value=
      SemiprimeUniversalSourceExecution.constraint A R t g u y :=
  constraint_value A R keys complete t g u y

theorem acquire_work (A R : ℕ) (keys : List (UniversalType r Q 1)) :
    (acquire A R keys).work≤tableBudget A R Q keys.length+2*R+4 := by
  have ht := table_work A R keys
  unfold acquire
  dsimp only
  rw [powerTwo_work]
  omega

theorem read_acquire_work (A R : ℕ) (keys : List (UniversalType r Q 1))
    (t : Fin Q) (g : Fin r) (u y : UniversalType r Q 1) :
    (read (acquire A R keys).value t g u y).work≤
      9*Q+2*(keys.length*(7*Q+4)+1)+16 := by
  have h := constraint_work (powerTwo (R-1)).value keys (table A R keys).value t g u y
  have hl : (table A R keys).value.length=Q := by
    rw [table_value,List.length_map,List.length_finRange]
  rw [hl] at h
  change (constraint (powerTwo (R-1)).value keys (table A R keys).value t g u y).work≤_
  omega

end RiemannGaussian.SemiprimePaidConstraintCache
