/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackMultiplierLink
import RiemannGaussian.SemiprimeD1StackSubtractorExecution

/-! # Fixed restoring-division stack program
All arithmetic data are Boolean stack cells. Three literal inclusions of Copy
prepare the subtractor operands and fitting template; the actual borrow-prefix
controls restoration. No quotient-value iteration occurs.
-/
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace RiemannGaussian.SemiprimeD1StackDivider
namespace C
export SemiprimeD1StackCalls (Instruction State execute step run)
end C

/-- Seven fixed auxiliary Boolean stacks, in addition to the subtractor bank. -/
inductive Aux where
  | input | divisor | digits | remainder | quotient | copyScratch | template
  deriving DecidableEq,Repr

/-- Literal enumeration of the seven auxiliary stack tags. -/
instance : Fintype Aux := Fintype.ofList [.input,.divisor,.digits,.remainder,.quotient,.copyScratch,.template] (by intro k; cases k <;> simp)

/-- Eleven Boolean data stacks, fixed before the input words. -/
abbrev Stack := SemiprimeD1StackAdder.Stack ⊕ Aux

/-- Three actual included copies with different fixed operand-stack maps. -/
inductive CopyKind where
  | remainder | divisor | template
  deriving DecidableEq,Repr

/-- Literal enumeration of the three included copy sites. -/
instance : Fintype CopyKind := Fintype.ofList [.remainder,.divisor,.template] (by intro k; cases k <;> simp)

/-- The input stack of each literal copy inclusion. -/
def copyInput : CopyKind → Stack
  | .remainder => .inr .remainder
  | .divisor | .template => .inr .divisor

/-- The output stack of each literal copy inclusion. -/
def copyOutput : CopyKind → Stack
  | .remainder => .inl .left
  | .divisor => .inl .right
  | .template => .inr .template

/-- Literal three-stack copy mapping; it uses no input-dependent address. -/
def copyStack (kind : CopyKind) (k : Fin 3) : Stack :=
  if k=0 then copyInput kind else if k=1 then copyOutput kind else .inr .copyScratch

/-- Every included copy really has three distinct data stacks. -/
theorem copyStack_injective (kind : CopyKind) : Function.Injective (copyStack kind) := by
  cases kind <;> decide

/-- Fixed controller labels; only individual input/borrow bits enter control. -/
inductive Control where
  | start | reversePush (bit : Bool) | initialize | loop | expand (bit : Bool)
  | callCopyR | callCopyD | callSub | borrowRead | quotientPush (borrow : Bool)
  | discardR | diffToScratch | diffPush (bit : Bool) | scratchToR | remPush (bit : Bool)
  | discardDiff | fitTemplate | fitRead | fitPush (bit : Bool) | fitDiscard
  | fitRestore | restorePush (bit : Bool) | cleanup | done
  deriving DecidableEq,Fintype,Repr

/-- Disjoint finite controller and real procedure labels. -/
inductive Label where
  | subtractor (pc : SemiprimeD1StackSubtractor.Label)
  | copy (kind : CopyKind) (pc : Fin 9)
  | control (pc : Control)
  deriving DecidableEq,Fintype,Repr

/-- Actual fixed division code with real copy/subtractor calls and return pops. -/
def code : Label → C.Instruction Stack Label
  | .subtractor pc => SemiprimeD1StackMultiplierLink.instruction Sum.inl Label.subtractor
      (SemiprimeD1StackSubtractor.code pc)
  | .copy kind pc => SemiprimeD1StackMultiplierLink.instruction (copyStack kind) (Label.copy kind)
      (SemiprimeD1StackCopy.code pc)
  | .control .start => .base (.pop (.inr .input) (.control .initialize)
      (.control (.reversePush false)) (.control (.reversePush true)))
  | .control (.reversePush b) => .base (.push (.inr .digits) b (.control .start))
  | .control .initialize => .call (.copy .template 0) (.control .fitTemplate)
  | .control .loop => .base (.pop (.inr .digits) (.control .cleanup)
      (.control (.expand false)) (.control (.expand true)))
  | .control (.expand b) => .base (.push (.inr .remainder) b (.control .callCopyR))
  | .control .callCopyR => .call (.copy .remainder 0) (.control .callCopyD)
  | .control .callCopyD => .call (.copy .divisor 0) (.control .callSub)
  | .control .callSub => .call (.subtractor (.start false)) (.control .borrowRead)
  | .control .borrowRead => .base (.pop (.inl .output) (.control (.quotientPush true))
      (.control (.quotientPush false)) (.control (.quotientPush true)))
  | .control (.quotientPush borrow) =>
      .base (.push (.inr .quotient) (!borrow) (.control (if borrow then .discardDiff else .discardR)))
  | .control .discardR => .base (.pop (.inr .remainder) (.control .diffToScratch)
      (.control .discardR) (.control .discardR))
  | .control .diffToScratch => .base (.pop (.inl .output) (.control .scratchToR)
      (.control (.diffPush false)) (.control (.diffPush true)))
  | .control (.diffPush b) => .base (.push (.inl .scratch) b (.control .diffToScratch))
  | .control .scratchToR => .base (.pop (.inl .scratch) (.control .initialize)
      (.control (.remPush false)) (.control (.remPush true)))
  | .control (.remPush b) => .base (.push (.inr .remainder) b (.control .scratchToR))
  | .control .discardDiff => .base (.pop (.inl .output) (.control .initialize)
      (.control .discardDiff) (.control .discardDiff))
  | .control .fitTemplate => .base (.pop (.inr .template) (.control .fitDiscard)
      (.control .fitRead) (.control .fitRead))
  | .control .fitRead => .base (.pop (.inr .remainder) (.control (.fitPush false))
      (.control (.fitPush false)) (.control (.fitPush true)))
  | .control (.fitPush b) => .base (.push (.inl .scratch) b (.control .fitTemplate))
  | .control .fitDiscard => .base (.pop (.inr .remainder) (.control .fitRestore)
      (.control .fitDiscard) (.control .fitDiscard))
  | .control .fitRestore => .base (.pop (.inl .scratch) (.control .loop)
      (.control (.restorePush false)) (.control (.restorePush true)))
  | .control (.restorePush b) => .base (.push (.inr .remainder) b (.control .fitRestore))
  | .control .cleanup => .base (.pop (.inr .divisor) (.control .done)
      (.control .cleanup) (.control .cleanup))
  | .control .done => .base .halt

/-- All literal operand, result and workspace stacks. -/
def payload (xs ys ds left right scratch diff rem quo cp tmp : List Bool) : Stack → List Bool
  | .inl .left => left
  | .inl .right => right
  | .inl .scratch => scratch
  | .inl .output => diff
  | .inr .input => xs
  | .inr .divisor => ys
  | .inr .digits => ds
  | .inr .remainder => rem
  | .inr .quotient => quo
  | .inr .copyScratch => cp
  | .inr .template => tmp

/-- Concrete configuration with an empty actual continuation stack. -/
def state (pc : Option Label) (flag : Option Bool) (returned : Option Label)
    (xs ys ds left right scratch diff rem quo cp tmp : List Bool) : C.State Stack Label :=
  ⟨pc,flag,returned,payload xs ys ds left right scratch diff rem quo cp tmp,[]⟩

/-- Fixed compiled machine; its declared pair outputs are quotient and remainder. -/
def machine : Turing.FinTM2 := SemiprimeD1StackCalls.machine
  (.inr .input) (.inr .quotient) (.control .start) code

end RiemannGaussian.SemiprimeD1StackDivider
