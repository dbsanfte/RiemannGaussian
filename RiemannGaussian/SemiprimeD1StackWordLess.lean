/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackSubtractorExecution
import RiemannGaussian.SemiprimeD1StackProcedureTrace
import RiemannGaussian.SemiprimeD1StackPhysicalLoops

/-! # Actual numeric less-than guard for public checker words
The literal subtractor produces a real borrow prefix. The caller reads that bit,
writes the Boolean answer, and physically drains every remaining difference bit.
The original word values and desired comparison never occur in finite control.
-/
set_option autoImplicit false
set_option maxHeartbeats 700000
set_option Elab.async false
namespace RiemannGaussian.SemiprimeD1StackWordLess
namespace C
export SemiprimeD1StackCalls (Instruction State execute step run)
end C
namespace S
export SemiprimeD1StackAdder (Stack store)
end S

/-- Five fixed Boolean data roles, including the physical comparison output. -/
abbrev Stack := S.Stack⊕Unit
/-- Fixed controller plus the literal subtractor's finite labels. -/
inductive Label where
  | start | readBorrow | save (b : Bool) | clearDifference | done
  | subtract (pc : SemiprimeD1StackSubtractor.Label)
  deriving DecidableEq,Fintype,Repr
/-- Actual Boolean comparison output stack. -/
def output : Stack := .inr ()
/-- Complete fixed physical comparison/cleanup code. -/
def program : Label→C.Instruction Stack Label
  | .start => .call (.subtract (.start false)) .readBorrow
  | .readBorrow => .base (.pop (.inl .output) (.save false) (.save false) (.save true))
  | .save b => .base (.push output b .clearDifference)
  | .clearDifference => .base (.pop (.inl .output) .done .clearDifference .clearDifference)
  | .done => .base .halt
  | .subtract pc => SemiprimeD1StackMultiplierLink.instruction Sum.inl Label.subtract
      (SemiprimeD1StackSubtractor.code pc)
/-- Exact physical operand/work/result payload. -/
def store (a b scratch diff valid : List Bool) : Stack→List Bool :=
  Sum.elim (S.store a b scratch diff) (fun _=>valid)
/-- Only both physical operand words are prepared at entry. -/
def initial (a b : List Bool) : C.State Stack Label :=
  ⟨some .start,none,none,store a b [] [] [],[]⟩
/-- Fixed actual machine with no comparison or decoded-value operation. -/
def machine : Turing.FinTM2 := SemiprimeD1StackCalls.machine (.inl .left) output .start program
/-- Every data/return alphabet is finite, independent of both operands. -/
theorem all_alphabets_finite : ∀k,Finite (machine.Γ k) :=
  SemiprimeD1StackCalls.all_alphabets_finite (.inl .left) output .start program
/-- Transient control is finite and contains no numeric-word payload. -/
theorem control_finite : Finite machine.σ :=
  SemiprimeD1StackCalls.control_finite (.inl .left) output .start program

end RiemannGaussian.SemiprimeD1StackWordLess
