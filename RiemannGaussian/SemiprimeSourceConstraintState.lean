/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeSourceConstraintHeight
import RiemannGaussian.SemiprimeCachedRawConstraints

/-! # Actual owner sums and acquired original integer-family states
Original finite lists and cached universal entries supply all scalar bounds;
no state-height, integer-entry or selected-matrix answer is a runtime input.
-/
set_option autoImplicit false
set_option maxHeartbeats 800000
namespace RiemannGaussian.SemiprimeSourceConstraintState
open scoped BigOperators
open OAI.Algorithms.SubexponentialSAT
open MulticolorTypes SqrtLog
open SemiprimeMaterializedSourceUniversal SemiprimeSourceUniversalHeight
open SemiprimeSourceConstraintHeight
variable {I : Type} [DecidableEq I] {r Q : ℕ}

/-- Original finite owner-list size times the derived copy bound. -/
def sourceBound (A Q R M : ℕ) : ℕ := M*2^(constraintExponent A Q R)

/-- Original owner-list size contributes only linearly to the bit exponent. -/
theorem sourceBound_dyadic (A Q R M : ℕ) :
    sourceBound A Q R M ≤ 2^(constraintExponent A Q R+M) := by
  unfold sourceBound
  calc
    M*2^(constraintExponent A Q R) ≤ 2^M*2^(constraintExponent A Q R) :=
      Nat.mul_le_mul_right _ (Nat.le_of_lt (Nat.lt_two_pow_self (n:=M)))
    _ = _ := by rw [← pow_add]; congr 1; omega

/-- Every actual owner-filter callback is bounded independently of incidence multiplicity. -/
theorem owner_term_abs {V : Type} [DecidableEq V] (A R : ℕ)
    (keys : List (UniversalType r Q 1)) (complete : ∀ u,u∈keys)
    (owner : I → V) (addresses : SemiprimeMaterializedSourcePullback.Addresses I r Q)
    (producer : I → Run (UniversalType r Q 1)) (t : Fin Q) (g : Fin r)
    (j : SemiprimePaidConstraintRows.Index I r Q) (v : V) (i : I) :
    |((if owner i=v then
      let out := SemiprimePaidConstraintRows.copy addresses producer
        (SemiprimePaidConstraintCache.acquire A R keys).value t g j i
      (⟨out.value,out.work+2⟩ : Run ℤ) else ⟨0,2⟩)).value| ≤
      (2^(constraintExponent A Q R):ℕ) := by
  split_ifs
  · exact copy_abs A R keys complete addresses producer t g j i
  · simp

/-- Every actual right-recursive owner-sum frame is bounded before cancellation. -/
theorem source_suffix_abs {V : Type} [DecidableEq V] (A R : ℕ)
    (keys : List (UniversalType r Q 1)) (complete : ∀ u,u∈keys)
    (is : List I) (owner : I → V) (addresses : SemiprimeMaterializedSourcePullback.Addresses I r Q)
    (producer : I → Run (UniversalType r Q 1)) (t : Fin Q) (g : Fin r)
    (j : SemiprimePaidConstraintRows.Index I r Q) (v : V) (k : ℕ) :
    |(SemiprimePaidConstraintRows.source (is.drop k) owner addresses producer
      (SemiprimePaidConstraintCache.acquire A R keys).value t g j v).value| ≤
      (sourceBound A Q R (is.drop k).length:ℕ) := by
  exact sumRuns_abs _ _ _ (fun i _ => owner_term_abs A R keys complete owner addresses producer t g j v i)

/-- The full acquired original-coordinate entry has its original-list bound. -/
theorem source_abs {V : Type} [DecidableEq V] (A R : ℕ)
    (keys : List (UniversalType r Q 1)) (complete : ∀ u,u∈keys)
    (is : List I) (owner : I → V) (addresses : SemiprimeMaterializedSourcePullback.Addresses I r Q)
    (producer : I → Run (UniversalType r Q 1)) (t : Fin Q) (g : Fin r)
    (j : SemiprimePaidConstraintRows.Index I r Q) (v : V) :
    |(SemiprimePaidConstraintRows.source is owner addresses producer
      (SemiprimePaidConstraintCache.acquire A R keys).value t g j v).value| ≤
      (sourceBound A Q R is.length:ℕ) := by
  simpa only [List.drop_zero] using source_suffix_abs A R keys complete is owner addresses producer t g j v 0

/-- Every stored entry of the actual four-dimensional acquisition table is bounded. -/
theorem table_cell_abs {n : ℕ} (A R : ℕ) (keys : List (UniversalType r Q 1))
    (complete : ∀ u,u∈keys) (is : List I) (owner : I → Fin n)
    (addresses : SemiprimeMaterializedSourcePullback.Addresses I r Q)
    (producer : I → Run (UniversalType r Q 1)) (js : List (SemiprimePaidConstraintRows.Index I r Q))
    (node : List (List (List ℤ))) (head : List (List ℤ)) (row : List ℤ) (z : ℤ)
    (hn : node∈(SemiprimePaidConstraintAcquisition.table is owner addresses producer
      (SemiprimePaidConstraintCache.acquire A R keys).value js).value)
    (hh : head∈node) (hr : row∈head) (hz : z∈row) :
    |z| ≤ (sourceBound A Q R is.length:ℕ) := by
  rw [SemiprimePaidConstraintAcquisition.table_value] at hn
  obtain ⟨t,_,rfl⟩ := List.mem_map.mp hn
  obtain ⟨g,_,rfl⟩ := List.mem_map.mp hh
  obtain ⟨j,_,rfl⟩ := List.mem_map.mp hr
  obtain ⟨v,_,rfl⟩ := List.mem_map.mp hz
  exact source_abs A R keys complete is owner addresses producer t g j v

/-- Actual acquired families inherit the table bound without a packing answer premise. -/
theorem acquire_cell_abs {n : ℕ} (A R : ℕ) (keys : List (UniversalType r Q 1))
    (complete : ∀ u,u∈keys) (is : List I) (owner : I → Fin n)
    (producer : I → Run (UniversalType r Q 1))
    (node : List (List (List ℤ))) (head : List (List ℤ)) (row : List ℤ) (z : ℤ)
    (hn : node∈(SemiprimePaidConstraintAcquisition.acquire A R is owner keys producer).value.entries)
    (hh : head∈node) (hr : row∈head) (hz : z∈row) :
    |z| ≤ (sourceBound A Q R is.length:ℕ) :=
  table_cell_abs A R keys complete is owner _ producer _ node head row z hn hh hr hz

/-- Successful actual list scans return a literal member, including arbitrary out-of-range scans. -/
theorem getRun_mem {α : Type*} (xs : List α) (k : ℕ) (a : α)
    (h : (SemiprimePaidConstraintCache.getRun xs k).value=some a) : a∈xs := by
  induction xs generalizing k with
  | nil => simp [SemiprimePaidConstraintCache.getRun] at h
  | cons b xs ih =>
    cases k with
    | zero => simp only [SemiprimePaidConstraintCache.getRun] at h; cases h; simp
    | succ k => exact List.mem_cons_of_mem b (ih k h)

omit [DecidableEq I] in
/-- Four actual finite scans preserve any proved concrete stored-cell bound. -/
theorem read_abs_of_cells (family : SemiprimePaidConstraintAcquisition.Family I r Q)
    (B t g j v : ℕ)
    (hc : ∀ node∈family.entries,∀ head∈node,∀ row∈head,∀ z∈row,|z| ≤ (B:ℤ)) :
    |(SemiprimePaidOriginalConstraints.read family t g j v).value| ≤ (B:ℤ) := by
  unfold SemiprimePaidOriginalConstraints.read
  cases hn : (SemiprimePaidConstraintCache.getRun family.entries t).value with
  | none => simp [hn,SemiprimePaidConstraintCache.getRun]
  | some node =>
    have hnm := getRun_mem _ _ _ hn
    cases hh : (SemiprimePaidConstraintCache.getRun node g).value with
    | none => simp [hn,hh,SemiprimePaidConstraintCache.getRun]
    | some head =>
      have hhm := getRun_mem _ _ _ hh
      cases hr : (SemiprimePaidConstraintCache.getRun head j).value with
      | none => simp [hn,hh,hr,SemiprimePaidConstraintCache.getRun]
      | some row =>
        have hrm := getRun_mem _ _ _ hr
        cases hz : (SemiprimePaidConstraintCache.getRun row v).value with
        | none => simp [hn,hh,hr,hz]
        | some z =>
          simpa only [hn,hh,hr,hz,Option.getD_some] using hc node hnm head hhm row hrm z (getRun_mem _ _ _ hz)

/-- Exact scalar payload count for the actual dense four-level table. -/
theorem table_scalar_cells {n : ℕ} (is : List I) (owner : I → Fin n)
    (addresses : SemiprimeMaterializedSourcePullback.Addresses I r Q)
    (producer : I → Run (UniversalType r Q 1))
    (cache : SemiprimePaidConstraintCache.Cache (r:=r) (Q:=Q))
    (js : List (SemiprimePaidConstraintRows.Index I r Q)) :
    ((SemiprimePaidConstraintAcquisition.table is owner addresses producer cache js).value.flatMap
      (fun node => node.flatMap (fun head => head.flatMap id))).length=Q*(r*(js.length*n)) := by
  rw [SemiprimePaidConstraintAcquisition.table_value]
  simp [List.length_flatMap,List.map_map,Function.comp_def]

/-- Actual acquired families retain the exact original row-name length in their cell count. -/
theorem acquire_scalar_cells {n : ℕ} (A R : ℕ) (is : List I) (owner : I → Fin n)
    (keys : List (UniversalType r Q 1)) (producer : I → Run (UniversalType r Q 1)) :
    let family := (SemiprimePaidConstraintAcquisition.acquire A R is owner keys producer).value
    (family.entries.flatMap (fun node => node.flatMap (fun head => head.flatMap id))).length=
      Q*(r*(family.indices.length*n)) := by
  exact table_scalar_cells is owner _ producer _ _

/-- Every stored scalar in the ORIGINAL computed-word acquisition has an original-input cap. -/
theorem original_cell_abs [Fintype I] {E : Type} [DecidableEq E] {n : ℕ}
    (owner : I → Fin n) (factor : I → E)
    (en : SemiprimeSourceLayout.Enumerations I (Fin n) E r Q) (eps : ℚ) (R : ℕ)
    (node : List (List (List ℤ))) (head : List (List ℤ)) (row : List ℤ) (z : ℤ)
    (hn : node∈(SemiprimePaidOriginalConstraints.acquire owner factor en eps R).value.entries)
    (hh : head∈node) (hr : row∈head) (hz : z∈row) :
    |z| ≤ (sourceBound (Subexp.TailInterval.intervalStart r Q R) Q R en.incidences.values.length:ℕ) :=
  acquire_cell_abs _ R en.types.values en.types.complete en.incidences.values owner _ node head row z hn hh hr hz

/-- All four-scan reads of the original acquired family, including out-of-range defaults. -/
theorem original_read_abs [Fintype I] {E : Type} [DecidableEq E] {n : ℕ}
    (owner : I → Fin n) (factor : I → E)
    (en : SemiprimeSourceLayout.Enumerations I (Fin n) E r Q) (eps : ℚ) (R : ℕ)
    (t g j v : ℕ) :
    |(SemiprimePaidOriginalConstraints.read (SemiprimePaidOriginalConstraints.acquire owner factor en eps R).value
      t g j v).value| ≤
      (sourceBound (Subexp.TailInterval.intervalStart r Q R) Q R en.incidences.values.length:ℕ) :=
  read_abs_of_cells _ _ t g j v (fun node hn head hh row hr z hz =>
    original_cell_abs owner factor en eps R node head row z hn hh hr hz)

/-- Head masking the actual original cache introduces only the literal zero branch. -/
theorem masked_original_read_abs [Fintype I] {E : Type} [DecidableEq E] {n : ℕ}
    (owner : I → Fin n) (factor : I → E)
    (en : SemiprimeSourceLayout.Enumerations I (Fin n) E r Q) (eps : ℚ) (R : ℕ)
    (head : Fin n → Fin r) (t : Fin Q) (g : Fin r) (j : ℕ) (v : Fin n) :
    |(SemiprimeCachedRawConstraints.read head
      (SemiprimePaidOriginalConstraints.acquire owner factor en eps R).value t g j v).value| ≤
      (sourceBound (Subexp.TailInterval.intervalStart r Q R) Q R en.incidences.values.length:ℕ) := by
  unfold SemiprimeCachedRawConstraints.read
  split_ifs
  · exact original_read_abs owner factor en eps R t.val g.val j v.val
  · simp

/-- Original acquisition, with no supplied labels, has the exact dense scalar cell count. -/
theorem original_scalar_cells [Fintype I] {E : Type} [DecidableEq E] {n : ℕ}
    (owner : I → Fin n) (factor : I → E)
    (en : SemiprimeSourceLayout.Enumerations I (Fin n) E r Q) (eps : ℚ) (R : ℕ) :
    let family := (SemiprimePaidOriginalConstraints.acquire owner factor en eps R).value
    (family.entries.flatMap (fun node => node.flatMap (fun head => head.flatMap id))).length=
      Q*(r*(family.indices.length*n)) :=
  acquire_scalar_cells _ R en.incidences.values owner en.types.values _

end RiemannGaussian.SemiprimeSourceConstraintState
