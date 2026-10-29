/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeMaterializedSourceAcquisition
import RiemannGaussian.SemiprimeLocalExecutionHeight

/-! # Heights and array cells of the actual source cache and pullback
These invariants follow the finite cache lookups and right-recursive array sums.
The audit lists below describe returned arrays at executed recursion frames; they
are proof views, not new runtime suppliers or a complete machine-space theorem.
-/
set_option autoImplicit false
set_option maxHeartbeats 1600000
namespace RiemannGaussian.SemiprimeSourcePullbackHeight
open OAI.Algorithms.SubexponentialSAT
open MulticolorTypes
open SemiprimeJetArray SemiprimeJetArrayHeight SemiprimeHermiteArrayHeight
open SemiprimeLocalExecutionHeight SemiprimeArrayOps
open SemiprimeMaterializedSourceUniversal SemiprimeMaterializedSourcePullback
variable {I : Type} {r Q : ℕ}

/-- Uniform shape and coefficient bound of a materialized two-dimensional cache. -/
def CacheBound (cache : List (List (Array ℚ))) (J d B : ℕ) : Prop :=
  ∀ row ∈ cache, ∀ a ∈ row, a.size=J ∧ ArrayBound a J d B

/-- A successful actual lookup returns a member of the supplied finite values. -/
theorem lookup_some_mem {α : Type*} (target : UniversalType r Q 1)
    (keys : List (UniversalType r Q 1)) (values : List α) (a : α)
    (h : (SemiprimeMaterializedSourceCache.lookup target keys values).value=some a) :
    a∈values := by
  induction keys generalizing values with
  | nil => simp [SemiprimeMaterializedSourceCache.lookup] at h
  | cons key keys ih =>
    cases values with
    | nil => simp [SemiprimeMaterializedSourceCache.lookup] at h
    | cons v vs =>
      simp only [SemiprimeMaterializedSourceCache.lookup] at h
      split_ifs at h with he
      · simp only [Option.some.injEq] at h
        subst a
        exact List.mem_cons_self
      · exact List.mem_cons_of_mem v (ih vs h)

/-- Both Boolean literal branches have their literal size and common denominator. -/
theorem literal_bound (J d B : ℕ) (one : Bool) (hd : 0<d) (hB : d≤B) :
    (literal J one).value.size=J ∧ ArrayBound (literal J one).value J d B := by
  refine ⟨by simp [literal], ?_⟩
  intro k hk
  rw [literal_coefficient J one k hk]
  split_ifs
  · exact representation_mono (representation_one d hd) hB
  · exact representation_mono (representation_zero d) (Nat.zero_le _)

/-- Neither missing-key branch nor a successful scan enlarges the cached bound. -/
theorem cache_read_bound (R d B : ℕ) (keys : List (UniversalType r Q 1))
    (cache : List (List (Array ℚ))) (u y : UniversalType r Q 1)
    (hc : CacheBound cache (R+1) d B) :
    (SemiprimeMaterializedSourceCache.read R keys cache u y).value.size=R+1 ∧
      ArrayBound (SemiprimeMaterializedSourceCache.read R keys cache u y).value (R+1) d B := by
  have hz : (Array.replicate (R+1) (0:ℚ)).size=R+1 ∧
      ArrayBound (Array.replicate (R+1) (0:ℚ)) (R+1) d B :=
    ⟨by simp, zero_bound (R+1) d B⟩
  unfold SemiprimeMaterializedSourceCache.read
  dsimp only
  cases ho : (SemiprimeMaterializedSourceCache.lookup u keys cache).value with
  | none => exact hz
  | some row =>
    have hr := lookup_some_mem u keys cache row ho
    dsimp only
    cases hi : (SemiprimeMaterializedSourceCache.lookup y keys row).value with
    | none => exact hz
    | some a => exact hc row hr a (lookup_some_mem y keys row a hi)

/-- All address branches of one original-coordinate contribution retain the bound. -/
theorem assembled_bound [DecidableEq I] (R d B : ℕ) (as : Addresses I r Q)
    (keys : List (UniversalType r Q 1)) (cache : List (List (Array ℚ))) (i j : I)
    (hd : 0<d) (hB : d≤B) (hc : CacheBound cache (R+1) d B) :
    (assembled R as keys cache i j).value.size=R+1 ∧
      ArrayBound (assembled R as keys cache i j).value (R+1) d B := by
  unfold assembled
  dsimp only
  split
  · exact literal_bound _ _ _ _ hd hB
  · split
    · exact literal_bound _ _ _ _ hd hB
    · split_ifs
      · exact cache_read_bound _ _ _ _ _ _ _ hc
      · exact literal_bound _ _ _ _ hd hB

/-- Every completed right-recursive sum has exactly the requested array width. -/
theorem sumArrays_size (J : ℕ) (f : I → Run (Array ℚ)) (is : List I) :
    (sumArrays J f is).value.size=J := by
  cases is <;> simp [sumArrays,literal,add,addJet]

/-- Bounds every recursive suffix by its actual number of contribution terms. -/
theorem sumArrays_bound (J d B : ℕ) (f : I → Run (Array ℚ)) (is : List I)
    (hf : ∀ i∈is, ArrayBound (f i).value J d B) :
    ArrayBound (sumArrays J f is).value J d (is.length*B) := by
  induction is with
  | nil =>
    intro k hk
    rw [sumArrays,literal_coefficient J false k hk]
    simpa only [Bool.false_and,Bool.false_eq_true,ite_false,List.length_nil,Nat.zero_mul] using representation_zero d
  | cons i is ih =>
    have ht := ih (fun j hj => hf j (List.mem_cons_of_mem i hj))
    intro k hk
    change Representation (coefficient (addJet (f i).value (sumArrays J f is).value J).coefficients k) _ _
    have h := addJet_representation _ _ J d B (is.length*B)
      (hf i List.mem_cons_self) ht k hk
    convert h using 1
    simp only [List.length_cons]
    ring

/-- Covers the actual stored suffix accumulator at every recursion depth. -/
theorem sumArrays_suffix_bound (J d B : ℕ) (f : I → Run (Array ℚ))
    (is : List I) (k : ℕ) (hf : ∀ i∈is, ArrayBound (f i).value J d B) :
    ArrayBound (sumArrays J f (is.drop k)).value J d (is.length*B) := by
  apply arrayBound_mono (sumArrays_bound J d B f (is.drop k)
    (fun i hi => hf i (List.mem_of_mem_drop hi)))
  exact Nat.mul_le_mul_right B (by simp only [List.length_drop]; omega)

/-- Proof view of every sum return array and callback return array in the actual recursion. -/
def sumFrameArrays (J : ℕ) (f : I → Run (Array ℚ)) : List I → List (Array ℚ)
  | [] => [(literal J false).value]
  | i::is => (f i).value :: (sumArrays J f (i::is)).value :: sumFrameArrays J f is

/-- Summed scalar slots, counting arrays separately even if an implementation shares them. -/
def arrayCells (xs : List (Array ℚ)) : ℕ := (xs.map Array.size).sum

/-- Exact array-slot count over all returned recursion-frame and callback arrays. -/
theorem sumFrameArrays_cells (J : ℕ) (f : I → Run (Array ℚ)) (is : List I)
    (hf : ∀ i∈is, (f i).value.size=J) :
    arrayCells (sumFrameArrays J f is)=(2*is.length+1)*J := by
  induction is with
  | nil => simp [sumFrameArrays,arrayCells,literal]
  | cons i is ih =>
    have ht := ih (fun j hj => hf j (List.mem_cons_of_mem i hj))
    simp only [sumFrameArrays,arrayCells,List.map_cons,List.sum_cons,
      hf i List.mem_cons_self,sumArrays_size] at ⊢
    change J+ (J+arrayCells (sumFrameArrays J f is))=_
    rw [ht,List.length_cons]
    ring

/-- All arrays in the recursion view obey one original-contribution bound. -/
theorem sumFrameArrays_bound (J d B : ℕ) (f : I → Run (Array ℚ)) (is : List I)
    (hf : ∀ i∈is, ArrayBound (f i).value J d B) :
    ∀ a∈sumFrameArrays J f is, ArrayBound a J d ((is.length+1)*B) := by
  induction is with
  | nil =>
    intro a ha
    simp only [sumFrameArrays,List.mem_singleton] at ha
    subst a
    intro k hk
    rw [literal_coefficient J false k hk]
    exact representation_mono (representation_zero d) (Nat.zero_le _)
  | cons i is ih =>
    intro a ha
    simp only [sumFrameArrays,List.mem_cons] at ha
    rcases ha with rfl | rfl | ha
    · exact arrayBound_mono (hf i List.mem_cons_self) (by simp only [List.length_cons]; nlinarith)
    · exact arrayBound_mono (sumArrays_bound J d B f (i::is) hf)
        (Nat.mul_le_mul_right B (Nat.le_succ _))
    · exact arrayBound_mono (ih (fun j hj => hf j (List.mem_cons_of_mem i hj)) a ha)
        (by simp only [List.length_cons]; nlinarith)

/-- Original variable filtering produces only bounded assembled arrays or zero arrays. -/
theorem sourceRow_bound [DecidableEq I] {n : ℕ} (R d B : ℕ) (is : List I)
    (owner : I → Fin n) (as : Addresses I r Q) (keys : List (UniversalType r Q 1))
    (cache : List (List (Array ℚ))) (i : I) (v : Fin n)
    (hd : 0<d) (hB : d≤B) (hc : CacheBound cache (R+1) d B) :
    (sourceRow R is owner as keys cache i v).value.size=R+1 ∧
      ArrayBound (sourceRow R is owner as keys cache i v).value (R+1) d (is.length*B) := by
  refine ⟨sumArrays_size _ _ _, ?_⟩
  apply sumArrays_bound
  intro j _
  split_ifs <;> dsimp only
  · exact (assembled_bound R d B as keys cache i j hd hB hc).2
  · exact (literal_bound (R+1) d B false hd hB).2

/-- Actual filtered source-row recursion at every stored suffix. -/
theorem sourceRow_suffix_bound [DecidableEq I] {n : ℕ} (R d B : ℕ) (is : List I)
    (owner : I → Fin n) (as : Addresses I r Q) (keys : List (UniversalType r Q 1))
    (cache : List (List (Array ℚ))) (i : I) (v : Fin n) (k : ℕ)
    (hd : 0<d) (hB : d≤B) (hc : CacheBound cache (R+1) d B) :
    ArrayBound (sourceRow R (is.drop k) owner as keys cache i v).value
      (R+1) d (is.length*B) := by
  apply arrayBound_mono (sourceRow_bound R d B (is.drop k) owner as keys cache i v hd hB hc).2
  exact Nat.mul_le_mul_right B (by simp only [List.length_drop]; omega)

/-- Count all scalar array slots of an acquired two-dimensional cache. -/
def cacheCells (cache : List (List (Array ℚ))) : ℕ := (cache.map arrayCells).sum

/-- Uniform rectangular caches have their exact materialized array-slot count. -/
theorem cacheCells_map {A C : Type*} (xs : List A) (ys : List C)
    (f : A → C → Array ℚ) (J : ℕ) (hf : ∀ x∈xs, ∀ y∈ys, (f x y).size=J) :
    cacheCells (xs.map (fun x => ys.map (f x)))=xs.length*ys.length*J := by
  have hi (x : A) (hx : x∈xs) : arrayCells (ys.map (f x))=ys.length*J := by
    unfold arrayCells
    rw [List.map_map]
    have he : ys.map (Array.size ∘ f x)=ys.map (fun _ => J) :=
      List.map_congr_left (fun y hy => hf x hx y hy)
    rw [he]
    simp
  unfold cacheCells
  rw [List.map_map]
  have he : xs.map (arrayCells ∘ fun x => ys.map (f x))=xs.map (fun _ => ys.length*J) :=
    List.map_congr_left (fun x hx => hi x hx)
  rw [he]
  simp only [List.map_const',List.sum_replicate,smul_eq_mul]
  ring

/-- This is the actual source-cache materialization, including every universal pair. -/
theorem universal_cache_cells (A R : ℕ) (keys : List (UniversalType r Q 1)) :
    cacheCells (SemiprimeMaterializedSourceRows.acquire A R keys).value=
      keys.length*keys.length*(R+1) := by
  rw [SemiprimeMaterializedSourceRows.acquire_value]
  apply cacheCells_map
  intro u _ y _
  exact SemiprimeSourceCodeArrays.compile_size (R+1) _

/-- Actual original-row acquisition retains incidence-by-variable-by-width cells. -/
theorem acquire_cells [DecidableEq I] {n : ℕ} (R : ℕ) (is : List I)
    (owner : I → Fin n) (as : Addresses I r Q) (keys : List (UniversalType r Q 1)) :
    cacheCells (acquire R is owner as keys).value=is.length*n*(R+1) := by
  rw [acquire_value]
  have h := cacheCells_map is (List.finRange n) (fun i v =>
    (sourceRow R is owner as keys
      (SemiprimeMaterializedSourceRows.acquire (centered r Q R) R keys).value i v).value)
    (R+1) (fun _ _ _ _ => sumArrays_size _ _ _)
  simpa only [List.length_finRange] using h

/-- All original cached rows derive from the actual acquired universal cache. -/
theorem acquire_bound [DecidableEq I] {n : ℕ} (R d B : ℕ) (is : List I)
    (owner : I → Fin n) (as : Addresses I r Q) (keys : List (UniversalType r Q 1))
    (hd : 0<d) (hB : d≤B)
    (hc : CacheBound (SemiprimeMaterializedSourceRows.acquire (centered r Q R) R keys).value
      (R+1) d B) :
    CacheBound (acquire R is owner as keys).value (R+1) d (is.length*B) := by
  rw [acquire_value]
  intro row hr a ha
  obtain ⟨i,_,rfl⟩ := List.mem_map.mp hr
  obtain ⟨v,_,rfl⟩ := List.mem_map.mp ha
  exact sourceRow_bound R d B is owner as keys _ i v hd hB hc

/-- The physical immutable array grid has the same coefficient invariant as its source lists. -/
def FrozenBound (a : Array (Array (Array ℚ))) (J d B : ℕ) : Prop :=
  CacheBound (a.toList.map Array.toList) J d B

/-- Freezing traverses metadata but cannot create new scalar values. -/
theorem freeze_bound (rows : List (List (Array ℚ))) (J d B : ℕ)
    (h : CacheBound rows J d B) :
    FrozenBound (SemiprimeMaterializedSourceAcquisition.freeze rows) J d B := by
  simpa [FrozenBound,SemiprimeMaterializedSourceAcquisition.freeze,List.map_map,
    Function.comp_def] using h

/-- Exact number of scalar slots after the actual immutable copy. -/
theorem freeze_cells (rows : List (List (Array ℚ))) :
    cacheCells ((SemiprimeMaterializedSourceAcquisition.freeze rows).toList.map Array.toList)=
      cacheCells rows := by
  simp [SemiprimeMaterializedSourceAcquisition.freeze,List.map_map,Function.comp_def]

/-- Packing labels are generated by the original callback; their values do not affect array shape. -/
theorem source_acquisition_cells [DecidableEq I] {n : ℕ} (R : ℕ) (is : List I)
    (owner : I → Fin n) (keys : List (UniversalType r Q 1))
    (producer : I → Run (UniversalType r Q 1)) :
    cacheCells ((SemiprimeMaterializedSourceAcquisition.acquire R is owner keys producer).value.toList.map
      Array.toList)=is.length*n*(R+1) := by
  change cacheCells ((SemiprimeMaterializedSourceAcquisition.freeze _).toList.map Array.toList)=_
  rw [freeze_cells]
  exact acquire_cells R is owner _ keys

/-- The original paid source acquisition preserves the universal-bound derivation. -/
theorem source_acquisition_bound [DecidableEq I] {n : ℕ} (R d B : ℕ) (is : List I)
    (owner : I → Fin n) (keys : List (UniversalType r Q 1))
    (producer : I → Run (UniversalType r Q 1)) (hd : 0<d) (hB : d≤B)
    (hc : CacheBound (SemiprimeMaterializedSourceRows.acquire (centered r Q R) R keys).value
      (R+1) d B) :
    FrozenBound (SemiprimeMaterializedSourceAcquisition.acquire R is owner keys producer).value
      (R+1) d (is.length*B) :=
  freeze_bound _ _ _ _ (acquire_bound R d B is owner _ keys hd hB hc)

end RiemannGaussian.SemiprimeSourcePullbackHeight
