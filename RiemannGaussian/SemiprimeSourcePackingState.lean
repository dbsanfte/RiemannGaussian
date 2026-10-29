/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimePaidConstraintAcquisition
import RiemannGaussian.SemiprimeSourcePullbackHeight
import RiemannGaussian.SemiprimeMaterializedOriginalSource

/-! # Actual finite packing cache and address state invariants
No correct packing or output-label function is assumed. All numerical bounds
follow the actual finite input lists and the executed scans themselves.
-/
set_option autoImplicit false
set_option maxHeartbeats 600000
namespace RiemannGaussian.SemiprimeSourcePackingState
open scoped BigOperators
open OAI.Algorithms.SubexponentialSAT
open MulticolorTypes
open SemiprimeMaterializedSourceUniversal SemiprimeMaterializedPacking
variable {I : Type} {r Q : ℕ}

/-- Actual map allocation and all callback storage charges are paid by its own report. -/
theorem mapPaid_cells_le_work {α β : Type*} (f : α → Run β) (cells : α → ℕ) (xs : List α)
    (hc : ∀ x∈xs,cells x ≤ (f x).work) :
    (xs.map cells).sum+xs.length ≤ (mapPaid f xs).work := by
  induction xs with
  | nil => simp [mapPaid]
  | cons x xs ih =>
    have hh := hc x List.mem_cons_self
    have ht := ih (fun y hy => hc y (List.mem_cons_of_mem _ hy))
    simp only [List.map_cons,List.sum_cons,List.length_cons,mapPaid]
    omega

/-- The acquired label cache has one row for each original incidence. -/
theorem labels_length (producer : I → Run (UniversalType r Q 1)) (vertices : List I) :
    (labels producer vertices).value.length=vertices.length := by
  rw [labels_value,List.length_map]

/-- Cached labels refer only to actual input incidences. -/
theorem labels_mem (producer : I → Run (UniversalType r Q 1)) (vertices : List I)
    (iv : I × UniversalType r Q 1) (h : iv∈(labels producer vertices).value) : iv.1∈vertices := by
  rw [labels_value] at h
  obtain ⟨i,hi,rfl⟩ := List.mem_map.mp h
  exact hi

/-- Each label coordinate is an original finite colour, without a magnitude oracle. -/
theorem label_coordinate_lt (u : UniversalType r Q 1) (t : Fin Q) :
    (u.head t).val<r ∧ (u.slot 0 t).val<r := ⟨(u.head t).isLt,(u.slot 0 t).isLt⟩

/-- Every bucket result consists only of the original cached incidence IDs. -/
theorem bucket_mem (u : UniversalType r Q 1) (ls : List (I × UniversalType r Q 1))
    (i : I) (h : i∈(bucket u ls).value) : i∈ls.map Prod.fst := by
  induction ls with
  | nil => simp [bucket] at h
  | cons iv ls ih =>
    rcases iv with ⟨j,v⟩
    simp only [bucket] at h
    split_ifs at h
    · rcases List.mem_cons.mp h with h|h
      · subst i; simp
      · exact List.mem_cons_of_mem j (ih h)
    · exact List.mem_cons_of_mem j (ih h)

/-- Each bucket is bounded by the actual number of scanned cache rows. -/
theorem bucket_length (u : UniversalType r Q 1) (ls : List (I × UniversalType r Q 1)) :
    (bucket u ls).value.length ≤ ls.length := by
  induction ls with
  | nil => simp [bucket]
  | cons iv ls ih =>
    rcases iv with ⟨i,v⟩
    simp only [bucket,List.length_cons]
    split_ifs
    · exact Nat.succ_le_succ ih
    · exact ih.trans (Nat.le_succ _)

/-- New bucket-list cells, following the SAME conditional cons recursion. -/
def bucketAllocations (u : UniversalType r Q 1) : List (I × UniversalType r Q 1) → ℕ
  | [] => 0
  | (_,v)::vs => (if (SemiprimeMaterializedSourceCache.same v u).value then 1 else 0)+bucketAllocations u vs

/-- The actual allocation counter is its output length, not an arbitrary heap assumption. -/
theorem bucket_allocations_eq (u : UniversalType r Q 1) (ls : List (I × UniversalType r Q 1)) :
    bucketAllocations u ls=(bucket u ls).value.length := by
  induction ls with
  | nil => rfl
  | cons iv ls ih =>
    rcases iv with ⟨i,v⟩
    simp only [bucketAllocations,bucket,ih]
    split_ifs <;> simp [Nat.add_comm]

/-- Every bucket's actual newly allocated cons cell is paid by its original report. -/
theorem bucket_allocations_le_work (u : UniversalType r Q 1) (ls : List (I × UniversalType r Q 1)) :
    bucketAllocations u ls ≤ (bucket u ls).work := by
  rw [bucket_allocations_eq,bucket_work]
  have h := bucket_length u ls
  nlinarith

/-- Every minimum recursion return stays below the original cap. -/
theorem minimum_le_cap (cap : ℕ) (bs : List (List I)) : (minimum cap bs).value ≤ cap := by
  induction bs with
  | nil => exact le_rfl
  | cons b bs ih => exact (Nat.min_le_right _ _).trans ih

/-- Every scanned suffix of the bucket list has the same original numerical cap. -/
theorem minimum_suffix_le (cap : ℕ) (bs : List (List I)) (k : ℕ) :
    (minimum cap (bs.drop k)).value ≤ cap := minimum_le_cap cap _

variable [DecidableEq I]

/-- Position returns are bounded even when the input incidence is absent. -/
theorem position_le_length (i : I) (xs : List I) : (position i xs).value ≤ xs.length := by
  induction xs with
  | nil => rfl
  | cons j xs ih =>
    simp only [position,List.length_cons]
    split_ifs <;> dsimp only <;> omega

/-- All recursion suffix positions and stack lengths stay below the original list length. -/
theorem position_suffix_le (i : I) (xs : List I) (k : ℕ) :
    (position i (xs.drop k)).value ≤ xs.length :=
  (position_le_length i _).trans (by simp only [List.length_drop]; omega)

/-- The actual place output preserves its source incidence. -/
theorem place_incidence (keys : List (UniversalType r Q 1)) (bs : List (List I)) (blocks : ℕ)
    (iv : I × UniversalType r Q 1) : (place keys bs blocks iv).value.1=iv.1 := rfl

/-- Every emitted address ID is strictly below the actual cached minimum. -/
theorem place_id_lt (keys : List (UniversalType r Q 1)) (bs : List (List I)) (blocks : ℕ)
    (iv : I × UniversalType r Q 1) (b : ℕ) (u : UniversalType r Q 1)
    (h : (place keys bs blocks iv).value.2=some (b,u)) : b<blocks := by
  unfold place at h
  dsimp only at h
  split_ifs at h with hp
  · cases h; exact hp

/-- Every emitted address retains the original acquired label. -/
theorem place_label (keys : List (UniversalType r Q 1)) (bs : List (List I)) (blocks : ℕ)
    (iv : I × UniversalType r Q 1) (b : ℕ) (u : UniversalType r Q 1)
    (h : (place keys bs blocks iv).value.2=some (b,u)) : u=iv.2 := by
  unfold place at h
  dsimp only at h
  split_ifs at h
  · cases h; rfl

/-- Original acquisition always emits exactly one address row per original incidence. -/
theorem acquire_length (vertices : List I) (keys : List (UniversalType r Q 1))
    (producer : I → Run (UniversalType r Q 1)) :
    (SemiprimeMaterializedPacking.acquire vertices keys producer).value.length=vertices.length := by
  simp only [SemiprimeMaterializedPacking.acquire,mapPaid_value,List.length_map,labels_length]

/-- No actual acquired address escapes the original incidence count. -/
theorem acquire_address_bound (vertices : List I) (keys : List (UniversalType r Q 1))
    (producer : I → Run (UniversalType r Q 1)) (iv : I × Option (ℕ × UniversalType r Q 1))
    (hi : iv∈(SemiprimeMaterializedPacking.acquire vertices keys producer).value)
    (b : ℕ) (u : UniversalType r Q 1) (hb : iv.2=some (b,u)) :
    iv.1∈vertices ∧ b<vertices.length := by
  simp only [SemiprimeMaterializedPacking.acquire,mapPaid_value] at hi
  obtain ⟨label,hl,rfl⟩ := List.mem_map.mp hi
  refine ⟨?_,?_⟩
  · rw [place_incidence]
    exact labels_mem producer vertices label hl
  · exact (place_id_lt _ _ _ _ b u hb).trans_le (minimum_le_cap _ _)

/-- Snapshot addresses are produced by the identical original packing scans. -/
theorem snapshot_addresses (vertices : List I) (keys : List (UniversalType r Q 1))
    (producer : I → Run (UniversalType r Q 1)) :
    (SemiprimePaidPackingSnapshot.acquire vertices keys producer).value.addresses=
      (SemiprimeMaterializedPacking.acquire vertices keys producer).value := rfl

/-- Actual cached block count is bounded with no correct-packing assumption. -/
theorem snapshot_blocks_le (vertices : List I) (keys : List (UniversalType r Q 1))
    (producer : I → Run (UniversalType r Q 1)) :
    (SemiprimePaidPackingSnapshot.acquire vertices keys producer).value.blocks ≤ vertices.length :=
  minimum_le_cap _ _

/-- The actual snapshot stores exactly the original number of address rows. -/
theorem snapshot_length (vertices : List I) (keys : List (UniversalType r Q 1))
    (producer : I → Run (UniversalType r Q 1)) :
    (SemiprimePaidPackingSnapshot.acquire vertices keys producer).value.addresses.length=vertices.length := by
  rw [snapshot_addresses,acquire_length]

/-- Every actual snapshot address has an original bounded ID and original incidence. -/
theorem snapshot_address_bound (vertices : List I) (keys : List (UniversalType r Q 1))
    (producer : I → Run (UniversalType r Q 1)) (iv : I × Option (ℕ × UniversalType r Q 1))
    (hi : iv∈(SemiprimePaidPackingSnapshot.acquire vertices keys producer).value.addresses)
    (b : ℕ) (u : UniversalType r Q 1) (hb : iv.2=some (b,u)) :
    iv.1∈vertices ∧ b<vertices.length := by
  rw [snapshot_addresses] at hi
  exact acquire_address_bound vertices keys producer iv hi b u hb

/-- Original packing acquisition pays its actual output-list cons cells. -/
theorem acquire_output_cells_le_work (vertices : List I) (keys : List (UniversalType r Q 1))
    (producer : I → Run (UniversalType r Q 1)) :
    (SemiprimeMaterializedPacking.acquire vertices keys producer).value.length ≤
      (SemiprimeMaterializedPacking.acquire vertices keys producer).work := by
  rw [acquire_length]
  unfold SemiprimeMaterializedPacking.acquire
  dsimp only
  omega

omit [DecidableEq I] in
/-- Exact lengths of all acquired bucket lists are bounded by the two input menus. -/
theorem bucket_bank_cells (vertices : List I) (keys : List (UniversalType r Q 1))
    (producer : I → Run (UniversalType r Q 1)) :
    (((mapPaid (fun u => bucket u (labels producer vertices).value) keys).value).map List.length).sum ≤
      keys.length*vertices.length := by
  rw [mapPaid_value,List.map_map]
  have h : ∀ xs : List (UniversalType r Q 1),
      (xs.map (fun u => (bucket u (labels producer vertices).value).value.length)).sum ≤ xs.length*vertices.length := by
    intro xs
    induction xs with
    | nil => simp
    | cons u xs ih =>
      have hb := bucket_length u (labels producer vertices).value
      rw [labels_length] at hb
      simp only [List.map_cons,List.sum_cons,List.length_cons]
      nlinarith
  exact h keys

omit [DecidableEq I] in
/-- All newly constructed bucket cons cells and the bucket-bank list itself are paid. -/
theorem bucket_bank_allocations_le_work (vertices : List I) (keys : List (UniversalType r Q 1))
    (producer : I → Run (UniversalType r Q 1)) :
    (keys.map (fun u => bucketAllocations u (labels producer vertices).value)).sum+keys.length ≤
      (mapPaid (fun u => bucket u (labels producer vertices).value) keys).work :=
  mapPaid_cells_le_work _ _ _ (fun u _ => bucket_allocations_le_work u _)

/-- A conservative audit view of returned bucket lists over all recursive suffixes. -/
def bucketFrameCells (u : UniversalType r Q 1) (ls : List (I × UniversalType r Q 1)) : ℕ :=
  ((List.range (ls.length+1)).map (fun k => (bucket u (ls.drop k)).value.length)).sum

omit [DecidableEq I] in
/-- All bucket return-frame payloads are polynomial in the original scanned length. -/
theorem bucket_frame_cells_bound (u : UniversalType r Q 1) (ls : List (I × UniversalType r Q 1)) :
    bucketFrameCells u ls ≤ (ls.length+1)*ls.length := by
  have h : ∀ ks : List ℕ,(ks.map (fun k => (bucket u (ls.drop k)).value.length)).sum ≤ ks.length*ls.length := by
    intro ks
    induction ks with
    | nil => simp
    | cons k ks ih =>
      have hb : (bucket u (ls.drop k)).value.length ≤ ls.length :=
        (bucket_length u (ls.drop k)).trans (by simp only [List.length_drop]; omega)
      simp only [List.map_cons,List.sum_cons,List.length_cons]
      nlinarith
  simpa only [bucketFrameCells,List.length_range] using h (List.range (ls.length+1))

/-- Actual generated row names have bounded block IDs and original leftover IDs. -/
def NameBound (keys : List (UniversalType r Q 1)) (vertices : List I) (blocks : ℕ) :
    SemiprimePaidConstraintRows.Index I r Q → Prop
  | .inl (b,u) => b<blocks ∧ u∈keys
  | .inr i => i∈vertices

omit [DecidableEq I] in
/-- Every generated complete-block row uses a strictly bounded literal ID. -/
theorem blockNames_bound (keys : List (UniversalType r Q 1)) (blocks : ℕ)
    (j : SemiprimePaidConstraintRows.Index I r Q)
    (hj : j∈(SemiprimePaidConstraintAcquisition.blockNames keys blocks).value) :
    NameBound keys [] blocks j := by
  rw [SemiprimePaidConstraintAcquisition.blockNames_value] at hj
  obtain ⟨b,hb,hj⟩ := List.mem_flatMap.mp hj
  obtain ⟨u,hu,rfl⟩ := List.mem_map.mp hj
  exact ⟨List.mem_range.mp hb,hu⟩

omit [DecidableEq I] in
/-- Every original generated name, including identity leftovers, uses only original data. -/
theorem names_bound (keys : List (UniversalType r Q 1)) (blocks : ℕ) (vertices : List I)
    (j : SemiprimePaidConstraintRows.Index I r Q)
    (hj : j∈(SemiprimePaidConstraintAcquisition.names keys blocks vertices).value) :
    NameBound keys vertices blocks j := by
  simp only [SemiprimePaidConstraintAcquisition.names,collect_value] at hj
  rcases List.mem_append.mp hj with hb|hi
  · have h := blockNames_bound keys blocks j hb
    cases j with
    | inl z => exact h
    | inr i => exact False.elim (List.not_mem_nil h)
  · obtain ⟨i,hi,rfl⟩ := List.mem_map.mp hi
    change i∈vertices
    simpa only [List.mem_map,Sum.inr.injEq,exists_eq_right] using hi

/-- Actual snapshot row-name count is at most M*D+M. -/
theorem snapshot_names_length (vertices : List I) (keys : List (UniversalType r Q 1))
    (producer : I → Run (UniversalType r Q 1)) :
    (SemiprimePaidConstraintAcquisition.names keys
      (SemiprimePaidPackingSnapshot.acquire vertices keys producer).value.blocks vertices).value.length ≤
      vertices.length*keys.length+vertices.length := by
  rw [SemiprimePaidConstraintAcquisition.names_length]
  exact Nat.add_le_add_right (Nat.mul_le_mul_right _ (snapshot_blocks_le vertices keys producer)) _

/-- Actual collect output cons cells are retained in the original callback report. -/
theorem collect_length_le_work {α β : Type*} (f : α → Run β) (xs : List α) :
    (collect f xs).value.length ≤ (collect f xs).work := by
  induction xs with
  | nil => simp [collect]
  | cons x xs ih => simp only [collect,List.length_cons]; omega

/-- New cons cells in the SAME blockNames recursion: collect plus append copies. -/
def blockNameAllocations (keys : List (UniversalType r Q 1)) : ℕ → ℕ
  | 0 => 0
  | b+1 => blockNameAllocations keys b+
      (SemiprimePaidConstraintAcquisition.blockNames (I:=I) keys b).value.length+keys.length

omit [DecidableEq I] in
/-- Every generated block-name cons and copied append cell is paid by the actual report. -/
theorem blockName_allocations_le_work (keys : List (UniversalType r Q 1)) (b : ℕ) :
    blockNameAllocations (I:=I) keys b ≤ (SemiprimePaidConstraintAcquisition.blockNames (I:=I) keys b).work := by
  induction b with
  | zero => simp [blockNameAllocations,SemiprimePaidConstraintAcquisition.blockNames]
  | succ b ih =>
    have h := collect_length_le_work (fun u => (⟨Sum.inl (b,u),2⟩ : Run (SemiprimePaidConstraintRows.Index I r Q))) keys
    rw [collect_value,List.length_map] at h
    simp only [blockNameAllocations,SemiprimePaidConstraintAcquisition.blockNames]
    omega

omit [DecidableEq I] in
/-- The actual block-name allocation recurrence has a fixed original-size envelope. -/
theorem blockName_allocations_bound (keys : List (UniversalType r Q 1)) (b : ℕ) :
    blockNameAllocations (I:=I) keys b ≤ (b+1)^2*keys.length := by
  induction b with
  | zero => simp [blockNameAllocations]
  | succ b ih =>
    simp only [blockNameAllocations,SemiprimePaidConstraintAcquisition.blockNames_length]
    nlinarith

/-- Coordinate/constructor slots in the principal retained packing lists.
This is a conservative field view, not a maximum machine-heap claim. -/
def retainedCells (vertices : List I) (keys : List (UniversalType r Q 1))
    (producer : I → Run (UniversalType r Q 1)) : ℕ :=
  let ls := (labels producer vertices).value
  let bs := (mapPaid (fun u => bucket u ls) keys).value
  let snap := (SemiprimePaidPackingSnapshot.acquire vertices keys producer).value
  let names := (SemiprimePaidConstraintAcquisition.names keys snap.blocks vertices).value
  vertices.length+keys.length*(2*Q+1)+ls.length*(2*Q+2)+bs.length+
    (bs.map List.length).sum+snap.addresses.length*(2*Q+4)+names.length*(2*Q+3)+1

/-- A fixed polynomial in ACTUAL original menu sizes bounds that retained field view. -/
def retainedBudget (M D Q : ℕ) : ℕ :=
  M+D*(2*Q+1)+M*(2*Q+2)+D+D*M+M*(2*Q+4)+(M*D+M)*(2*Q+3)+1

/-- Actual returned/cached lists satisfy the original-input field bound without label advice. -/
theorem retained_cells_bound (vertices : List I) (keys : List (UniversalType r Q 1))
    (producer : I → Run (UniversalType r Q 1)) :
    retainedCells vertices keys producer ≤ retainedBudget vertices.length keys.length Q := by
  have hb := bucket_bank_cells vertices keys producer
  have hn := snapshot_names_length vertices keys producer
  unfold retainedCells retainedBudget
  dsimp only
  rw [labels_length,snapshot_length]
  simp only [mapPaid_value,List.length_map]
  gcongr
  simpa only [mapPaid_value] using hb

/-- All block-name recursion-frame outputs are bounded by the actual original size. -/
theorem blockNames_frame_length (vertices : List I) (keys : List (UniversalType r Q 1))
    (producer : I → Run (UniversalType r Q 1)) (b : ℕ)
    (hb : b ≤ (SemiprimePaidPackingSnapshot.acquire vertices keys producer).value.blocks) :
    (SemiprimePaidConstraintAcquisition.blockNames (I:=I) keys b).value.length ≤ vertices.length*keys.length := by
  rw [SemiprimePaidConstraintAcquisition.blockNames_length]
  exact Nat.mul_le_mul_right _ (hb.trans (snapshot_blocks_le vertices keys producer))

/-- The actual generated names of the snapshot have bounded native IDs even for leftovers. -/
theorem snapshot_names_bound (vertices : List I) (keys : List (UniversalType r Q 1))
    (producer : I → Run (UniversalType r Q 1)) (j : SemiprimePaidConstraintRows.Index I r Q)
    (hj : j∈(SemiprimePaidConstraintAcquisition.names keys
      (SemiprimePaidPackingSnapshot.acquire vertices keys producer).value.blocks vertices).value) :
    NameBound keys vertices vertices.length j := by
  have hn := names_bound keys _ vertices j hj
  cases j with
  | inl p => exact ⟨hn.1.trans_le (snapshot_blocks_le vertices keys producer),hn.2⟩
  | inr i => exact hn

omit [DecidableEq I] in
/-- New label-list cells and pair records are paid, independent of producer cost. -/
theorem labels_cells_le_work (producer : I → Run (UniversalType r Q 1)) (vertices : List I) :
    2*vertices.length ≤ (labels producer vertices).work := by
  have h := mapPaid_cells_le_work
    (fun i => let v := producer i; (⟨(i,v.value),v.work+1⟩ : Run (I × UniversalType r Q 1)))
    (fun _ => 1) vertices (fun _ _ => by dsimp only; omega)
  simpa only [List.map_const',List.sum_replicate,nsmul_eq_mul,Nat.cast_id,mul_one,two_mul,labels] using h

/-- New cons cells in the actual names append after block acquisition. -/
def nameAllocations (keys : List (UniversalType r Q 1)) (b : ℕ) (vertices : List I) : ℕ :=
  blockNameAllocations (I:=I) keys b+vertices.length+
    (SemiprimePaidConstraintAcquisition.blockNames (I:=I) keys b).value.length

omit [DecidableEq I] in
/-- Block allocation, leftover collect cells and append copies all appear in the SAME names report. -/
theorem name_allocations_le_work (keys : List (UniversalType r Q 1)) (b : ℕ) (vertices : List I) :
    nameAllocations keys b vertices ≤ (SemiprimePaidConstraintAcquisition.names keys b vertices).work := by
  have hb := blockName_allocations_le_work (I:=I) keys b
  have ht := collect_length_le_work (fun i => (⟨Sum.inr i,1⟩ : Run (SemiprimePaidConstraintRows.Index I r Q))) vertices
  rw [collect_value,List.length_map] at ht
  unfold nameAllocations SemiprimePaidConstraintAcquisition.names
  dsimp only
  omega

omit [DecidableEq I] in
/-- Even a failed lookup has a bounded bucket/default list, with no completeness assumption. -/
theorem acquired_bucket_read_length (vertices : List I) (keys : List (UniversalType r Q 1))
    (producer : I → Run (UniversalType r Q 1)) (u : UniversalType r Q 1) :
    ((SemiprimeMaterializedSourceCache.lookup u keys
      (mapPaid (fun y => bucket y (labels producer vertices).value) keys).value).value.getD []).length ≤ vertices.length := by
  cases h : (SemiprimeMaterializedSourceCache.lookup u keys
      (mapPaid (fun y => bucket y (labels producer vertices).value) keys).value).value with
  | none => simp
  | some xs =>
    have hm := SemiprimeSourcePullbackHeight.lookup_some_mem _ _ _ _ h
    rw [mapPaid_value] at hm
    obtain ⟨y,_,rfl⟩ := List.mem_map.mp hm
    simpa only [labels_length,Option.getD_some] using bucket_length y (labels producer vertices).value

/-- The ACTUAL internal position scalar remains bounded even on the leftover branch. -/
theorem acquired_position_le (vertices : List I) (keys : List (UniversalType r Q 1))
    (producer : I → Run (UniversalType r Q 1)) (iv : I × UniversalType r Q 1) :
    (position iv.1 ((SemiprimeMaterializedSourceCache.lookup iv.2 keys
      (mapPaid (fun y => bucket y (labels producer vertices).value) keys).value).value.getD [])).value ≤ vertices.length :=
  (position_le_length _ _).trans (acquired_bucket_read_length vertices keys producer iv.2)

omit [DecidableEq I] in
/-- All actual label-map suffix return lists stay within the original incidence count. -/
theorem labels_suffix_length (producer : I → Run (UniversalType r Q 1)) (vertices : List I) (k : ℕ) :
    (labels producer (vertices.drop k)).value.length ≤ vertices.length := by
  rw [labels_length,List.length_drop]
  omega

/-- Original searched labels instantiate the packing bounds directly, without a producer answer. -/
theorem original_packing_bounds [Fintype I] {E : Type} [DecidableEq E] {n : ℕ}
    (owner : I → Fin n) (factor : I → E)
    (en : SemiprimeSourceLayout.Enumerations I (Fin n) E r Q) (eps : ℚ) :
    let producer := SemiprimeMaterializedSourceWords.producer owner factor en.wordFirst en.wordTail
      en.terms.values en.indices.values
      (eps*(en.incidences.values.length:ℚ)/(en.types.values.length:ℚ)) ((n:ℚ)/(2*(r:ℚ)))
    let snap := (SemiprimePaidPackingSnapshot.acquire en.incidences.values en.types.values producer.value).value
    snap.blocks ≤ en.incidences.values.length ∧
      snap.addresses.length=en.incidences.values.length ∧
      retainedCells en.incidences.values en.types.values producer.value ≤
        retainedBudget en.incidences.values.length en.types.values.length Q ∧
      (SemiprimePaidConstraintAcquisition.names en.types.values snap.blocks en.incidences.values).value.length ≤
        en.incidences.values.length*en.types.values.length+en.incidences.values.length := by
  exact ⟨snapshot_blocks_le _ _ _,snapshot_length _ _ _,retained_cells_bound _ _ _,snapshot_names_length _ _ _⟩

end RiemannGaussian.SemiprimeSourcePackingState
