/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackMarkedRootRecordsRowCost
import RiemannGaussian.SemiprimeD1StackMarkedRootRecordsLoop
/-! # Whole actual paired-sweep cost in physical input bytes and scope arity -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackMarkedRootRecordsByteCost
open SemiprimeD1StackMarkedRootRecordsEncoding SemiprimeD1StackMarkedRootRecordsRows
open SemiprimeD1StackMarkedRootRecordsLoop SemiprimeD1StackMarkedRootRecordsRowCost
open SemiprimeD1TensorTapeCodec (vectorBits)
/-- Each actual old row carries both complete fields, including empty vector/table delimiters. -/
theorem old_cons_length (row : Row) (rows : List Row) :
    (oldRecords (row::rows)).length=
      2*(vectorBits row.scope).length+2*row.oldTable.length+3+(oldRecords rows).length := by
  simp only [oldRecords,List.foldr_cons,List.length_cons,SemiprimeSourceHistogramKeyBits.frame_length]
  omega
/-- Both physical fields are paid by the original acquired record tape. -/
theorem row_in_old (rows : List Row) (row : Row) (hr : row∈rows) :
    (vectorBits row.scope).length+row.oldTable.length ≤ (oldRecords rows).length := by
  induction rows with
  | nil => cases hr
  | cons head tail ih =>
    rw [old_cons_length]
    rcases List.mem_cons.mp hr with he|ht
    · subst row;omega
    · have h := ih ht;omega
/-- The five actual frame lengths pay all descriptor payload bytes and their delimiters. -/
theorem descriptor_cons_length (row : Row) (rows : List Row) :
    (descriptors (row::rows)).length=2*SemiprimeD1StackMarkedRootRecordsParse.mass row.fields+5+(descriptors rows).length := by
  simp only [descriptors,List.foldr_cons,SemiprimeD1EdgeCatalogueEncoding.record,
    SemiprimeSourceHistogramKeyBits.frame_length]
  rw [mass_eq]
  omega
/-- Every actual descriptor payload byte belongs to the paid descriptor stream. -/
theorem row_in_descriptors (rows : List Row) (row : Row) (hr : row∈rows) :
    SemiprimeD1StackMarkedRootRecordsParse.mass row.fields ≤ (descriptors rows).length := by
  induction rows with
  | nil => cases hr
  | cons head tail ih =>
    rw [descriptor_cons_length]
    rcases List.mem_cons.mp hr with he|ht
    · subst row;omega
    · have h := ih ht;omega
/-- One actual row marker is present for every factor, including zero-port factors. -/
theorem rows_count (rows : List Row) : rows.length ≤ (oldRecords rows).length := by
  induction rows with
  | nil => decide
  | cons head tail ih => rw [List.length_cons,old_cons_length];omega
/-- Actual common physical resource before the paired sweep. -/
def resource (bits : List Bool) (rows : List Row) : Nat :=
  bits.length+(oldRecords rows).length+(descriptors rows).length+2
/-- No native numeric port interpretation enters the uniform physical resource estimate. -/
theorem radius_le (bits : List Bool) (rows : List Row) (row : Row) (hr : row∈rows) :
    radius bits row ≤ resource bits rows := by
  have h0 := row_in_old rows row hr
  have h1 := row_in_descriptors rows row hr
  unfold radius resource
  omega
/-- Pure sum of actual row caps, bounded by the same acquired bytes and maximal actual arity. -/
theorem sum_rowBudget_le (bits : List Bool) (rows : List Row) (hb : bits≠[]) (R B : Nat)
    (hr : ∀ row∈rows,radius bits row ≤ R) (ha : ∀ row∈rows,row.scope.length ≤ B) :
    (rows.map (rowBudget bits)).sum ≤ rows.length*(10^26*R^2*2^B) := by
  induction rows with
  | nil => simp only [List.map_nil,List.sum_nil,List.length_nil,Nat.zero_mul,Nat.le_refl]
  | cons row rows ih =>
    have h0 := rowBudget_le bits row hb
    have hrad := Nat.pow_le_pow_left (hr row (by simp)) 2
    have hpow := Nat.pow_le_pow_right (by decide : 0 < (2:Nat)) (ha row (by simp))
    have hrow : rowBudget bits row ≤ 10^26*R^2*2^B :=
      h0.trans (Nat.mul_le_mul (Nat.mul_le_mul_left _ hrad) hpow)
    have htail := ih (fun r h => hr r (by simp [h])) (fun r h => ha r (by simp [h]))
    simp only [List.map_cons,List.sum_cons,List.length_cons]
    nlinarith only [hrow,htail]
/-- The same source's entire physical loop has a cubic byte cap per actual maximal scope. -/
theorem loopBudget_le (bits : List Bool) (rows : List Row) (hb : bits≠[]) (B : Nat)
    (ha : ∀ row∈rows,row.scope.length ≤ B) :
    loopBudget bits rows ≤ 10^26*(resource bits rows)^3*2^B+3 := by
  have hs := sum_rowBudget_le bits rows hb (resource bits rows) B (radius_le bits rows) ha
  have hn : rows.length ≤ resource bits rows := by have h := rows_count rows;unfold resource;omega
  have hmul := Nat.mul_le_mul_right (10^26*(resource bits rows)^2*2^B) hn
  unfold loopBudget
  calc
    _ ≤ resource bits rows*(10^26*(resource bits rows)^2*2^B)+3 := by omega
    _ = _ := by ring
/-- Produced output bytes are paid by actual logger/source work, summed once in forward order. -/
theorem payload_length (bits : List Bool) (rows : List Row) :
    (payload bits rows).length ≤ (rows.map (rowBudget bits)).sum := by
  induction rows with
  | nil => rfl
  | cons row rows ih =>
    have h := newRow_length_le bits row
    change (newRow bits row++payload bits rows).length ≤ rowBudget bits row+(rows.map (rowBudget bits)).sum
    rw [List.length_append]
    omega
end RiemannGaussian.SemiprimeD1StackMarkedRootRecordsByteCost
