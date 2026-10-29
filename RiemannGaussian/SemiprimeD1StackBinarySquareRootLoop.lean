/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackBinarySquareRootDecision
/-! # Complete descending-power loop: exactly L+1 real binary candidate tests -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackBinarySquareRootLoop
open SemiprimeD1StackBinarySquareRoot SemiprimeD1StackBinarySquareRootEncoding
open SemiprimeD1StackBinarySquareRootPrimitives SemiprimeD1StackBinarySquareRootDecision
open SemiprimeD1StackProcedureTrace
open SemiprimeD1StackPackedRootMetadataEncoding (baseWord)
/-- One extra zero bit at the low end is exactly the preceding binary power. -/
theorem base_succ (n : ℕ) : baseWord (n+1)=false::baseWord n := by
  simp only [baseWord,List.replicate_succ,List.cons_append]
/-- Actual one-cell power shift consumes the real bit and selects continue/finish. -/
theorem shift_run (bits p r : List Bool) (bit : Bool) :
    Runs program 1 (ctl .shift) (idle bits (bit::p) r)
      (if bit then ctl .reverse else ctl .rootCopy) (idle bits p r) := by
  apply one_base program _ _ (.pop power (ctl .reverse) (ctl .rootCopy) (ctl .reverse)) _ _ rfl
  · cases bit <;> rfl
  · change Function.update (idle bits (bit::p) r) (metadata (M.aux .base)) p=idle bits p r
    dsimp only [idle]
    rw [bank_metadata,retained_update]
/-- Exact actual instruction clock of the n+1 descending candidate-bit tests. -/
def loopTime (bits : List Bool) : ℕ→List Bool→ℕ
  | 0,r => iterationTime bits (baseWord 0) r+1
  | n+1,r => iterationTime bits (baseWord (n+1)) r+1+
      loopTime bits n (E.nextWord bits r (baseWord (n+1)))
/-- Whole literal loop from any actual descending-power boundary, all33 roles. -/
theorem loop_run (bits r : List Bool) (n : ℕ) :
    Runs program (loopTime bits n r) (ctl .rootCopy) (idle bits (baseWord n) r)
      (ctl .reverse) (idle bits [] (E.wordLoop bits n r)) := by
  induction n generalizing r with
  | zero =>
    have h0:=iteration_run bits (baseWord 0) r
    have h1:=shift_run bits [] (E.nextWord bits r (baseWord 0)) true
    exact join h0 h1
  | succ n ih =>
    have h0:=iteration_run bits (baseWord (n+1)) r
    have h1:=shift_run bits (baseWord n) (E.nextWord bits r (baseWord (n+1))) false
    rw [←base_succ] at h1
    exact join (join h0 h1) (ih (E.nextWord bits r (baseWord (n+1))))
end RiemannGaussian.SemiprimeD1StackBinarySquareRootLoop
