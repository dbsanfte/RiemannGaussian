/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeSourceCompactBits

/-! # Paid unambiguous framing of acquired Boolean histogram keys
Each first-field bit has a true continuation tag, and false ends that field.
The already acquired second field is an immutable tail, not a fresh full copy.
Tries inspect the resulting actual key bits, including every second-field bit.
-/
set_option autoImplicit false
namespace RiemannGaussian.SemiprimeSourceHistogramKeyBits
open SemiprimeSourceCompactBits (Report)

/-- Mathematical byte layout of two fields; used to specify the executed framing. -/
def frame : List Bool → List Bool → List Bool
  | [],ys => false::ys
  | b::bs,ys => true::b::frame bs ys

/-- Execute framing by copying/tagging every first-field bit and retaining the
actual immutable second-field tail reference. -/
def pair : List Bool → List Bool → Report
  | [],ys => ⟨false::ys,3⟩
  | b::bs,ys =>
    let rest := pair bs ys
    ⟨true::b::rest.bits,rest.clock+6⟩

/-- The actual returned key has exactly the specified unambiguous field layout. -/
theorem pair_bits (xs ys : List Bool) : (pair xs ys).bits=frame xs ys := by
  induction xs with
  | nil => rfl
  | cons b bs ih => simp only [pair,frame,ih]

/-- Every returned key cell belongs to a copied first field/tag or the actual second field. -/
theorem frame_length (xs ys : List Bool) : (frame xs ys).length=2*xs.length+ys.length+1 := by
  induction xs with
  | nil => simp [frame]
  | cons b bs ih => simp only [frame,List.length_cons,ih];omega

/-- Physical framing has linear work in the copied field, without rescanning the tail. -/
theorem pair_clock (xs ys : List Bool) : (pair xs ys).clock=6*xs.length+3 := by
  induction xs with
  | nil => rfl
  | cons b bs ih => simp only [pair,List.length_cons,ih];omega

/-- No two different field pairs have the same actual framed key. -/
theorem frame_injective (xs ys xs' ys' : List Bool)
    (h : frame xs ys=frame xs' ys') : xs=xs' ∧ ys=ys' := by
  induction xs generalizing xs' with
  | nil =>
    cases xs' with
    | nil => exact ⟨rfl,List.cons.inj h |>.2⟩
    | cons b bs => simp only [frame,List.cons.injEq,Bool.false_eq_true,false_and] at h
  | cons b bs ih =>
    cases xs' with
    | nil => simp only [frame,List.cons.injEq,Bool.true_eq_false,false_and] at h
    | cons c cs =>
      have hc : b=c ∧ frame bs ys=frame cs ys' := List.cons.inj (List.cons.inj h).2
      have ht := ih cs hc.2
      exact ⟨by rw [hc.1,ht.1],ht.2⟩

/-- Equality of executed compound keys retains equality of BOTH original fields. -/
theorem pair_eq_iff (xs ys xs' ys' : List Bool) :
    (pair xs ys).bits=(pair xs' ys').bits ↔ xs=xs' ∧ ys=ys' := by
  rw [pair_bits,pair_bits]
  exact ⟨frame_injective xs ys xs' ys',by rintro ⟨rfl,rfl⟩;rfl⟩

/-- Actual parsed first field, remaining tail and syntax/test report. -/
structure Split where
  /-- Physical copied first field. -/
  first : List Bool
  /-- Actual remaining immutable input tail. -/
  rest : List Bool
  /-- Whether a real end-of-first-field tag was reached. -/
  valid : Bool
  /-- All inspected tags/data and copied first-field cells. -/
  clock : ℕ

/-- Parse a framed field by inspecting its actual tag and data bits. -/
def split : List Bool → Split
  | [] => ⟨[],[],false,1⟩
  | false::ys => ⟨[],ys,true,3⟩
  | true::[] => ⟨[],[],false,3⟩
  | true::b::bs =>
    let out := split bs
    ⟨b::out.first,out.rest,out.valid,out.clock+6⟩

/-- Parsing an actually framed pair recovers both complete fields exactly. -/
theorem split_frame (xs ys : List Bool) :
    (split (frame xs ys)).first=xs ∧ (split (frame xs ys)).rest=ys ∧
      (split (frame xs ys)).valid=true := by
  induction xs with
  | nil => exact ⟨rfl,rfl,rfl⟩
  | cons b bs ih => simp only [frame,split,ih.1,ih.2.1,ih.2.2,and_self]

/-- A complete framed-field parse pays only for that field and its terminating tag. -/
theorem split_frame_clock (xs ys : List Bool) :
    (split (frame xs ys)).clock=6*xs.length+3 := by
  induction xs with
  | nil => rfl
  | cons b bs ih => simp only [frame,split,List.length_cons,ih];omega

end RiemannGaussian.SemiprimeSourceHistogramKeyBits
