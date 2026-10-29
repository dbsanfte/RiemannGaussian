/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackIncrement
import Mathlib.Data.List.Nodup

/-! # Exact before-overflow assignment order
All natural/list expressions here are proof specifications. The finite loop
executes physical overflow tests and never evaluates these counters or catalogues.
-/
set_option autoImplicit false
namespace RiemannGaussian.SemiprimeD1StackAssignmentOrder
open SemiprimeD1StackIncrement (wrapped overflow)
open SemiprimeBitArithmetic (bitValue bitNat)

/-- Number of assignments from this word through the last pre-overflow word. -/
def remaining (xs : List Bool) : ℕ := 2^xs.length-bitValue xs

/-- Proof-only chronological specification of repeated wrapped increments. -/
def assignments : ℕ → List Bool → List (List Bool)
  | 0,_ => []
  | n+1,xs => xs::assignments n (wrapped xs)

/-- No valid fixed-width word has zero assignments left before overflow. -/
theorem remaining_pos (xs : List Bool) : 0<remaining xs := by
  have h := SemiprimeBitArithmetic.bitValue_lt_width xs
  unfold remaining
  omega

/-- The overflow iteration is exactly the final remaining assignment. -/
theorem overflow_remaining (xs : List Bool) (h : overflow xs=true) : remaining xs=1 := by
  have hv := SemiprimeD1StackIncrement.value_balance xs
  have hb := SemiprimeBitArithmetic.bitValue_lt_width xs
  simp only [h,bitNat,ite_true,Nat.mul_one] at hv
  unfold remaining
  omega

/-- Before overflow the actual wrapped value increases by exactly one. -/
theorem wrapped_value_step (xs : List Bool) (h : overflow xs=false) :
    bitValue (wrapped xs)=bitValue xs+1 := by
  have hv := SemiprimeD1StackIncrement.value_balance xs
  simpa [h,bitNat] using hv

/-- The next actual word has exactly one fewer iteration left. -/
theorem remaining_step (xs : List Bool) (h : overflow xs=false) :
    remaining (wrapped xs)+1=remaining xs := by
  have hv := wrapped_value_step xs h
  have hb := SemiprimeBitArithmetic.bitValue_lt_width xs
  simp only [remaining,SemiprimeD1StackIncrement.wrapped_length,hv]
  omega

/-- Every prefix specification has its exact literal iteration length. -/
theorem assignments_length (n : ℕ) (xs : List Bool) : (assignments n xs).length=n := by
  induction n generalizing xs with
  | zero => rfl
  | succ n ih => simp [assignments,ih]

/-- All actual generated words retain the original fixed width. -/
theorem assignments_width (n : ℕ) (xs ys : List Bool) (h : ys∈assignments n xs) :
    ys.length=xs.length := by
  induction n generalizing xs with
  | zero => simp [assignments] at h
  | succ n ih =>
    simp only [assignments,List.mem_cons] at h
    rcases h with rfl|h
    · rfl
    · exact (ih (wrapped xs) h).trans (SemiprimeD1StackIncrement.wrapped_length xs)

/-- Every nonwrapping chronological prefix enumerates consecutive natural values. -/
theorem assignments_values (n : ℕ) (xs : List Bool) (hn : n≤remaining xs) :
    (assignments n xs).map bitValue=List.range' (bitValue xs) n := by
  induction n generalizing xs with
  | zero => simp [assignments]
  | succ n ih =>
    by_cases hz : n=0
    · subst n; simp [assignments,List.range'_succ]
    · have ho : overflow xs=false := by
        cases h : overflow xs with
        | false => rfl
        | true => have hr := overflow_remaining xs h; omega
      have hr := remaining_step xs ho
      have ht : n≤remaining (wrapped xs) := by omega
      simp only [assignments,List.map_cons,List.range'_succ]
      rw [ih (wrapped xs) ht,wrapped_value_step xs ho]

/-- Fixed-width binary values uniquely identify the literal padded word. -/
theorem word_value_injective (xs ys : List Bool) (hlen : xs.length=ys.length)
    (hval : bitValue xs=bitValue ys) : xs=ys := by
  induction xs generalizing ys with
  | nil => cases ys <;> simp_all
  | cons b bs ih =>
    cases ys with
    | nil => simp at hlen
    | cons c cs =>
      have hl : bs.length=cs.length := by simpa using hlen
      cases b <;> cases c <;> simp [bitValue,bitNat] at hval ⊢
      all_goals first | omega | exact ih cs hl (by omega)

/-- The acquired zero word has its exact original width and value. -/
theorem zero_remaining (width : ℕ) : remaining (List.replicate width false)=2^width := by
  have hv : bitValue (List.replicate width false)=0 := by
    induction width with
    | zero => rfl
    | succ n ih => simp [List.replicate_succ,bitValue,bitNat,ih]
  simp [remaining,hv]

/-- Exactly 2^width distinct assignments occur before the first overflow. -/
theorem zero_nodup (width : ℕ) :
    (assignments (2^width) (List.replicate width false)).Nodup := by
  apply List.Nodup.of_map bitValue
  rw [assignments_values _ _ (by rw [zero_remaining])]
  exact List.nodup_range'

/-- Every fixed-width original assignment appears, including width zero. -/
theorem zero_complete (width : ℕ) (ys : List Bool) :
    ys∈assignments (2^width) (List.replicate width false) ↔ ys.length=width := by
  constructor
  · intro h
    simpa using assignments_width (2^width) (List.replicate width false) ys h
  · intro hlen
    have hy : bitValue ys<2^width := by
      simpa [hlen] using SemiprimeBitArithmetic.bitValue_lt_width ys
    have hv := assignments_values (2^width) (List.replicate width false) (by rw [zero_remaining])
    have hzero : bitValue (List.replicate width false)=0 := by
      have hr := zero_remaining width
      have hb := SemiprimeBitArithmetic.bitValue_lt_width (List.replicate width false)
      simp only [remaining,List.length_replicate] at hr hb
      omega
    rw [hzero] at hv
    have hm : bitValue ys∈(assignments (2^width) (List.replicate width false)).map bitValue := by
      rw [hv]
      simpa using hy
    obtain ⟨word,hw,he⟩ := List.mem_map.mp hm
    have hl : word.length=ys.length := by
      have hh := assignments_width (2^width) (List.replicate width false) word hw
      simpa [hlen] using hh
    have heq := word_value_injective word ys hl he
    simpa [heq] using hw

end RiemannGaussian.SemiprimeD1StackAssignmentOrder
