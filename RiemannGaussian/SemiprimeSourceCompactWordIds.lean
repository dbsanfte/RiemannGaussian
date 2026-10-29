/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeSourceCompactBits
import RiemannGaussian.SemiprimeMaterializedWords

/-! # Original-count acquisition of compact ascending physical word IDs
No old padded-ID bank is acquired or re-encoded. Each emitted ID is copied once
and the next ID is physically incremented and trimmed once.
-/
set_option autoImplicit false
namespace RiemannGaussian.SemiprimeSourceCompactWordIds
open SemiprimeBitArithmetic SemiprimeMaterializedWords
open SemiprimeSourceCompactBits (Compact)

/-- Direct physical ascending sequence with cached current counter. -/
def ascending (current : List Bool) : ℕ → Run (List (List Bool))
  | 0 => ⟨[],1⟩
  | n+1 =>
    let out := SemiprimeSourceCompactBits.copy current
    let next := SemiprimeSourceCompactBits.increment current
    let rest := ascending next.bits n
    ⟨out.bits::rest.value,out.clock+next.clock+rest.work+5⟩

/-- Original endpoint starts from literal compact zero. -/
def acquire (n : ℕ) : Run (List (List Bool)) := ascending [] n

/-- Exact ordered numerical values, not merely a set cover. -/
theorem ascending_values (current : List Bool) (n : ℕ) :
    (ascending current n).value.map bitValue=List.range' (bitValue current) n := by
  induction n generalizing current with
  | zero => rfl
  | succ n ih =>
    simp only [ascending,List.map_cons,SemiprimeSourceCompactBits.copy_bits,
      SemiprimeSourceCompactBits.increment_value,List.range'_succ,ih]

/-- All actual output words are compact when the actual initial counter is compact. -/
theorem ascending_compact (current : List Bool) (n : ℕ) (hc : Compact current) :
    ∀ id∈(ascending current n).value,Compact id := by
  induction n generalizing current with
  | zero => simp [ascending]
  | succ n ih =>
    simp only [ascending,SemiprimeSourceCompactBits.copy_bits,List.mem_cons]
    intro id hi
    rcases hi with rfl|hi
    · exact hc
    · exact ih _ (SemiprimeSourceCompactBits.increment_compact current) id hi

/-- Output cardinality is the original input count. -/
theorem ascending_length (current : List Bool) (n : ℕ) :
    (ascending current n).value.length=n := by
  have h := congrArg List.length (ascending_values current n)
  simpa only [List.length_map,List.length_range'] using h

/-- Direct acquisition emits exactly zero through n−1 in that order. -/
theorem acquire_values (n : ℕ) : (acquire n).value.map bitValue=List.range n := by
  simpa only [acquire,bitValue,← List.range_eq_range'] using ascending_values [] n

/-- Every acquired ID is physically compact from the actual zero initializer. -/
theorem acquire_compact (n : ℕ) : ∀ id∈(acquire n).value,Compact id :=
  ascending_compact [] n trivial

/-- Actual acquired sequence length, no assumed bank cardinality. -/
theorem acquire_length (n : ℕ) : (acquire n).value.length=n := ascending_length [] n

/-- Every acquired ID is in the exact original range. -/
theorem acquire_value_lt (n : ℕ) (id : List Bool) (hi : id∈(acquire n).value) :
    bitValue id<n := by
  have h : bitValue id∈(acquire n).value.map bitValue := List.mem_map.mpr ⟨id,hi,rfl⟩
  rw [acquire_values] at h
  exact List.mem_range.mp h

/-- Original count gives intrinsic logarithmic ID widths. -/
theorem acquire_bounded (n : ℕ) :
    ∀ id∈(acquire n).value,id.length ≤ Nat.clog 2 (n+1) := by
  intro id hi
  apply SemiprimeSourceCompactBits.compact_length_of_lt _ (acquire_compact n id hi)
  have hv := acquire_value_lt n id hi
  have hp := Nat.le_pow_clog (by decide : 1<(2:ℕ)) (n+1)
  omega

/-- Compact Boolean magnitudes have no distinct encodings of the same value. -/
theorem compact_value_injective (a b : List Bool) (ha : Compact a) (hb : Compact b)
    (he : bitValue a=bitValue b) : a=b := by
  induction a generalizing b with
  | nil =>
    cases b with
    | nil => rfl
    | cons c cs =>
      have h := SemiprimeSourceCompactBits.compact_pos (c::cs) hb (by simp)
      change 0=bitValue (c::cs) at he
      omega
  | cons a as ih =>
    cases b with
    | nil =>
      have h := SemiprimeSourceCompactBits.compact_pos (a::as) ha (by simp)
      change bitValue (a::as)=0 at he
      omega
    | cons b bs =>
      have htaila := ha.1
      have htailb := hb.1
      cases a <;> cases b <;>
        simp only [bitValue,bitNat,Bool.false_eq_true,ite_false,ite_true] at he
      · have ht : bitValue as=bitValue bs := by omega
        rw [ih bs htaila htailb ht]
      · omega
      · omega
      · have ht : bitValue as=bitValue bs := by omega
        rw [ih bs htaila htailb ht]

/-- No actual acquired ID is duplicated. -/
theorem acquire_nodup (n : ℕ) : (acquire n).value.Nodup := by
  apply List.Nodup.of_map (f:=bitValue)
  rw [acquire_values]
  exact List.nodup_range

/-- The literal empty ID is the first actual candidate whenever a candidate exists. -/
theorem acquire_head (n : ℕ) (hn : 0<n) :
    (acquire n).value=[]::(acquire n).value.tail := by
  cases n with
  | zero => omega
  | succ n => simp only [acquire,ascending,SemiprimeSourceCompactBits.copy_bits,List.tail_cons]

/-- Common per-ID cost includes the copy, compact increment and loop control. -/
def stepBudget (M : ℕ) : ℕ := 30*(Nat.clog 2 (M+1)+2)+20

/-- Each actual recursive counter derives its width from the original count cap. -/
theorem ascending_clock (current : List Bool) (n M : ℕ) (hc : Compact current)
    (hm : bitValue current+n ≤ M) :
    (ascending current n).work ≤ n*stepBudget M+1 := by
  induction n generalizing current with
  | zero => simp [ascending]
  | succ n ih =>
    have hw : current.length ≤ Nat.clog 2 (M+1) := by
      apply SemiprimeSourceCompactBits.compact_length_of_lt current hc
      have hp := Nat.le_pow_clog (by decide : 1<(2:ℕ)) (M+1)
      omega
    have hnext : bitValue (SemiprimeSourceCompactBits.increment current).bits+n ≤ M := by
      rw [SemiprimeSourceCompactBits.increment_value]
      omega
    have hr := ih _ (SemiprimeSourceCompactBits.increment_compact current) hnext
    have hcopy := SemiprimeSourceCompactBits.copy_clock current
    have hinc := SemiprimeSourceCompactBits.increment_clock current (Nat.clog 2 (M+1)+1)
      (by omega) (by omega)
    unfold stepBudget at hr ⊢
    simp only [ascending]
    nlinarith

/-- Complete direct ID acquisition is linear in count times logarithmic physical width. -/
theorem acquire_clock (n : ℕ) : (acquire n).work ≤ n*stepBudget n+1 :=
  ascending_clock [] n n trivial (by simp [bitValue])

end RiemannGaussian.SemiprimeSourceCompactWordIds
