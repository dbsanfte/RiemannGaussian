/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeSourceCompactBits

/-! # Count actual original records with compact physical increments
No native length answer is encoded; the actual list constructors drive the loop.
-/
set_option autoImplicit false
namespace RiemannGaussian.SemiprimeSourceHistogramCountInput
open SemiprimeBitArithmetic
open SemiprimeSourceCompactBits (Compact Report)

/-- Inspect each actual record cell and retain its physical counter increment. -/
def count {A : Type*} : List A → Report
  | [] => ⟨[],1⟩
  | _::xs =>
    let old := count xs
    let next := SemiprimeSourceCompactBits.increment old.bits
    ⟨next.bits,old.clock+next.clock+5⟩

/-- The actual records, not supplied cardinality advice, determine the output. -/
theorem count_value {A : Type*} (xs : List A) : bitValue (count xs).bits=xs.length := by
  induction xs with
  | nil => rfl
  | cons a xs ih => simp only [count,SemiprimeSourceCompactBits.increment_value,ih,List.length_cons]

/-- Every recursively acquired count is compact. -/
theorem count_compact {A : Type*} (xs : List A) : Compact (count xs).bits := by
  cases xs with
  | nil => trivial
  | cons a xs => exact SemiprimeSourceCompactBits.increment_compact _

/-- Original list count gives intrinsic logarithmic physical storage. -/
theorem count_length {A : Type*} (xs : List A) :
    (count xs).bits.length ≤ Nat.clog 2 (xs.length+1) := by
  have h := SemiprimeSourceCompactBits.compact_length_clog _ (count_compact xs)
  simpa only [count_value] using h

/-- One physical increment and visited record cell, in original count width. -/
def stepBudget (M : ℕ) : ℕ := 30*(Nat.clog 2 (M+1)+2)+20

/-- All recursive tails fit the same original acquired list-count cap. -/
theorem count_clock_cap {A : Type*} (xs : List A) (M : ℕ) (hlen : xs.length ≤ M) :
    (count xs).clock ≤ xs.length*stepBudget M+1 := by
  induction xs with
  | nil => simp [count]
  | cons a xs ih =>
    have htail := ih (by simp only [List.length_cons] at hlen;omega)
    have hw : (count xs).bits.length ≤ Nat.clog 2 (M+1) :=
      (count_length xs).trans (Nat.clog_mono_right 2 (by simp only [List.length_cons] at hlen;omega))
    have hi := SemiprimeSourceCompactBits.increment_clock (count xs).bits
      (Nat.clog 2 (M+1)+1) (by omega) (by omega)
    unfold stepBudget at htail ⊢
    simp only [count,List.length_cons]
    nlinarith

/-- Complete list-driven count clock, no counter/height/work oracle. -/
theorem count_clock {A : Type*} (xs : List A) :
    (count xs).clock ≤ xs.length*stepBudget xs.length+1 := count_clock_cap xs xs.length le_rfl

end RiemannGaussian.SemiprimeSourceHistogramCountInput
