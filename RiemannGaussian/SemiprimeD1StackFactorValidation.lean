/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackValidationLink
import RiemannGaussian.SemiprimeD1StackDividerExecution
import RiemannGaussian.SemiprimeD1FactorValidationBits

/-! # Fixed finite-stack proper-factor validation
Original input and candidate remain Boolean payload. Real nested division,
copy and comparison procedures acquire every output and branch flag.
-/
set_option autoImplicit false
set_option maxHeartbeats 1500000
namespace RiemannGaussian.SemiprimeD1StackFactorValidation
namespace C
export SemiprimeD1StackCalls (Instruction State execute step run)
end C
namespace D
export SemiprimeD1StackDivider (Stack Aux Label code payload)
end D

/-- Fixed auxiliary input, flag and copy-work stacks. -/
inductive Aux where
  | input | candidate | guard | copyScratch | lower | upper | valid
  deriving DecidableEq,Repr

/-- Actual finite auxiliary-stack enumeration. -/
instance : Fintype Aux := Fintype.ofList [.input,.candidate,.guard,.copyScratch,.lower,.upper,.valid]
  (by intro k; cases k <;> simp)

/-- Eighteen fixed Boolean data stacks. -/
abbrev Stack := D.Stack ⊕ Aux

/-- Fixed copy inclusions; no target address depends on either input. -/
inductive CopyKind where
  | guard | input | divisor | left | right
  deriving DecidableEq,Repr

/-- Actual finite copy-site enumeration. -/
instance : Fintype CopyKind := Fintype.ofList [.guard,.input,.divisor,.left,.right]
  (by intro k; cases k <;> simp)

/-- Literal subtractor-bank inclusion into the nested divider bank. -/
def subStack (k : SemiprimeD1StackAdder.Stack) : Stack := .inl (.inl k)

/-- Literal persistent copy input. -/
def copyInput : CopyKind → Stack
  | .guard | .divisor | .left => .inr .candidate
  | .input | .right => .inr .input

/-- Literal copy destination. -/
def copyOutput : CopyKind → Stack
  | .guard => .inr .guard
  | .input => .inl (.inr .input)
  | .divisor => .inl (.inr .divisor)
  | .left => subStack .left
  | .right => subStack .right

/-- The real three-stack map for each included copy body. -/
def copyStack (kind : CopyKind) (k : Fin 3) : Stack :=
  if k=0 then copyInput kind else if k=1 then copyOutput kind else .inr .copyScratch

/-- All included copy operands are distinct actual stacks. -/
theorem copyStack_injective (kind : CopyKind) : Function.Injective (copyStack kind) := by
  cases kind <;> decide

/-- Fixed controller states, with only finitely many individual Boolean flags. -/
inductive Control where
  | start | scanGuard (nonzero : Bool) | guardDone (nonzero : Bool)
  | callDivisor | callDivider | callLower | lowerHigh | lowerLow | lowerSub
  | lowerRead | lowerSave (borrow : Bool) | clearLower | callUpper | callUpperRight
  | upperSub | upperRead | upperSave (borrow : Bool) | clearUpper
  | scanR (nonzero : Bool) | lowerFlag (nonzero : Bool) | upperFlag (nonzero lower : Bool)
  | finish (valid : Bool) | cleanupInput | cleanupCandidate | done
  deriving DecidableEq,Fintype,Repr

/-- All literal nested procedure and controller labels. -/
inductive Label where
  | divider (pc : D.Label)
  | subtractor (pc : SemiprimeD1StackSubtractor.Label)
  | copy (kind : CopyKind) (pc : Fin 9)
  | control (pc : Control)
  deriving DecidableEq,Fintype,Repr

/-- Actual linked fixed validation program, with a physical zero-divisor guard. -/
def code : Label → C.Instruction Stack Label
  | .divider pc => SemiprimeD1StackValidationLink.instruction Sum.inl Label.divider (D.code pc)
  | .subtractor pc => SemiprimeD1StackMultiplierLink.instruction subStack Label.subtractor
      (SemiprimeD1StackSubtractor.code pc)
  | .copy kind pc => SemiprimeD1StackMultiplierLink.instruction (copyStack kind) (Label.copy kind)
      (SemiprimeD1StackCopy.code pc)
  | .control .start => .call (.copy .guard 0) (.control (.scanGuard false))
  | .control (.scanGuard nz) => .base (.pop (.inr .guard) (.control (.guardDone nz))
      (.control (.scanGuard nz)) (.control (.scanGuard true)))
  | .control (.guardDone false) => .base (.push (.inr .valid) false (.control .cleanupInput))
  | .control (.guardDone true) => .call (.copy .input 0) (.control .callDivisor)
  | .control .callDivisor => .call (.copy .divisor 0) (.control .callDivider)
  | .control .callDivider => .call (.divider (.control .start)) (.control .callLower)
  | .control .callLower => .call (.copy .left 0) (.control .lowerHigh)
  | .control .lowerHigh => .base (.push (subStack .right) true (.control .lowerLow))
  | .control .lowerLow => .base (.push (subStack .right) false (.control .lowerSub))
  | .control .lowerSub => .call (.subtractor (.start false)) (.control .lowerRead)
  | .control .lowerRead => .base (.pop (subStack .output) (.control (.lowerSave true))
      (.control (.lowerSave false)) (.control (.lowerSave true)))
  | .control (.lowerSave b) => .base (.push (.inr .lower) b (.control .clearLower))
  | .control .clearLower => .base (.pop (subStack .output) (.control .callUpper)
      (.control .clearLower) (.control .clearLower))
  | .control .callUpper => .call (.copy .left 0) (.control .callUpperRight)
  | .control .callUpperRight => .call (.copy .right 0) (.control .upperSub)
  | .control .upperSub => .call (.subtractor (.start false)) (.control .upperRead)
  | .control .upperRead => .base (.pop (subStack .output) (.control (.upperSave false))
      (.control (.upperSave false)) (.control (.upperSave true)))
  | .control (.upperSave b) => .base (.push (.inr .upper) b (.control .clearUpper))
  | .control .clearUpper => .base (.pop (subStack .output) (.control (.scanR false))
      (.control .clearUpper) (.control .clearUpper))
  | .control (.scanR nz) => .base (.pop (.inl (.inr .remainder)) (.control (.lowerFlag nz))
      (.control (.scanR nz)) (.control (.scanR true)))
  | .control (.lowerFlag nz) => .base (.pop (.inr .lower) (.control (.upperFlag nz true))
      (.control (.upperFlag nz false)) (.control (.upperFlag nz true)))
  | .control (.upperFlag nz lower) => .base (.pop (.inr .upper) (.control (.finish false))
      (.control (.finish false)) (.control (.finish ((!lower) && !nz))))
  | .control (.finish valid) => .base (.push (.inr .valid) valid (.control .cleanupInput))
  | .control .cleanupInput => .base (.pop (.inr .input) (.control .cleanupCandidate)
      (.control .cleanupInput) (.control .cleanupInput))
  | .control .cleanupCandidate => .base (.pop (.inr .candidate) (.control .done)
      (.control .cleanupCandidate) (.control .cleanupCandidate))
  | .control .done => .base .halt

/-- All actual divider, persistent-input, Boolean-flag and work payloads. -/
def payload (xs ys ds left right scratch diff rem quo cp tmp input candidate guard work lower upper valid : List Bool) :
    Stack → List Bool
  | .inl k => D.payload xs ys ds left right scratch diff rem quo cp tmp k
  | .inr .input => input
  | .inr .candidate => candidate
  | .inr .guard => guard
  | .inr .copyScratch => work
  | .inr .lower => lower
  | .inr .upper => upper
  | .inr .valid => valid

/-- Concrete source configuration with no preloaded continuation frames. -/
def state (pc : Option Label) (flag : Option Bool) (returned : Option Label)
    (xs ys ds left right scratch diff rem quo cp tmp input candidate guard work lower upper valid : List Bool) : C.State Stack Label :=
  ⟨pc,flag,returned,payload xs ys ds left right scratch diff rem quo cp tmp input candidate guard work lower upper valid,[]⟩

/-- Actual fixed finite-stack validation machine with prepared binary operands. -/
def machine : Turing.FinTM2 := SemiprimeD1StackCalls.machine
  (.inr .input) (.inr .valid) (.control .start) code

end RiemannGaussian.SemiprimeD1StackFactorValidation
