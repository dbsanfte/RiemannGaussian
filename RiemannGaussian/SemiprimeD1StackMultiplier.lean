/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackMultiplierLink
import RiemannGaussian.SemiprimeD1StackAdderExecution

/-! # Fixed Boolean-stack multiplier with real procedure calls
The first operand is reversed physically. Each true digit calls the included
copy and adder programs; false digits only shift, preserving raw padding.
-/
set_option autoImplicit false
set_option maxHeartbeats 800000
namespace RiemannGaussian.SemiprimeD1StackMultiplier
namespace A
export SemiprimeD1StackAdder (Stack Label code)
end A
namespace C
export SemiprimeD1StackCalls (Instruction State execute step run)
end C

/-- The fixed nine Boolean data-stack tags. -/
abbrev Stack := A.Stack ⊕ (Fin 3 ⊕ Bool)

/-- Persistent second operand, preserved by each included copy call. -/
def factor : Stack := .inr (.inl 0)
/-- Actual output stack of the included copy procedure. -/
def copied : Stack := .inr (.inl 1)
/-- Actual work stack of the included copy procedure. -/
def copyScratch : Stack := .inr (.inl 2)
/-- Prepared first operand, physically consumed by reversal. -/
def input : Stack := .inr (.inr false)
/-- Physically reversed first operand, consumed one digit at a time. -/
def digits : Stack := .inr (.inr true)

/-- Fixed multiplier controller labels; only individual Boolean digits enter control. -/
inductive Control where
  | start | reversePush (bit : Bool) | loop | shiftFalse | shiftTrue
  | callCopy | copyToScratch | copyPush (bit : Bool) | scratchToLeft | leftPush (bit : Bool)
  | callAdder | sumToScratch | sumPush (bit : Bool) | scratchToAcc | accPush (bit : Bool)
  | cleanup | done
  deriving DecidableEq,Fintype,Repr

/-- Disjoint fixed labels of the adder, copy procedure, and multiplier caller. -/
inductive Label where
  | adder (pc : A.Label) | copy (pc : Fin 9) | control (pc : Control)
  deriving DecidableEq,Fintype,Repr

/-- Literal inclusion of the three copy stacks into the multiplier data bank. -/
def copyStack (k : Fin 3) : Stack := .inr (.inl k)

/-- Actual included procedure bodies and the literal fixed caller. -/
def code : Label → C.Instruction Stack Label
  | .adder pc => SemiprimeD1StackMultiplierLink.instruction Sum.inl Label.adder (A.code pc)
  | .copy pc => SemiprimeD1StackMultiplierLink.instruction copyStack Label.copy
      (SemiprimeD1StackCopy.code pc)
  | .control .start => .base (.pop input (.control .loop) (.control (.reversePush false)) (.control (.reversePush true)))
  | .control (.reversePush b) => .base (.push digits b (.control .start))
  | .control .loop => .base (.pop digits (.control .cleanup) (.control .shiftFalse) (.control .shiftTrue))
  | .control .shiftFalse => .base (.push (.inl .right) false (.control .loop))
  | .control .shiftTrue => .base (.push (.inl .right) false (.control .callCopy))
  | .control .callCopy => .call (.copy 0) (.control .copyToScratch)
  | .control .copyToScratch => .base (.pop copied (.control .scratchToLeft) (.control (.copyPush false)) (.control (.copyPush true)))
  | .control (.copyPush b) => .base (.push (.inl .scratch) b (.control .copyToScratch))
  | .control .scratchToLeft => .base (.pop (.inl .scratch) (.control .callAdder) (.control (.leftPush false)) (.control (.leftPush true)))
  | .control (.leftPush b) => .base (.push (.inl .left) b (.control .scratchToLeft))
  | .control .callAdder => .call (.adder (.start false)) (.control .sumToScratch)
  | .control .sumToScratch => .base (.pop (.inl .output) (.control .scratchToAcc) (.control (.sumPush false)) (.control (.sumPush true)))
  | .control (.sumPush b) => .base (.push (.inl .scratch) b (.control .sumToScratch))
  | .control .scratchToAcc => .base (.pop (.inl .scratch) (.control .loop) (.control (.accPush false)) (.control (.accPush true)))
  | .control (.accPush b) => .base (.push (.inl .right) b (.control .scratchToAcc))
  | .control .cleanup => .base (.pop factor (.control .done) (.control .cleanup) (.control .cleanup))
  | .control .done => .base .halt

/-- Concrete prepared operands and all actual workspace stacks. -/
def payload (xs ys ds left acc scratch out cp cs : List Bool) : Stack → List Bool
  | .inl .left => left
  | .inl .right => acc
  | .inl .scratch => scratch
  | .inl .output => out
  | .inr (.inl k) => if k=0 then ys else if k=1 then cp else cs
  | .inr (.inr b) => if b then ds else xs

/-- Concrete source configuration with an empty actual return stack. -/
def state (pc : Option Label) (flag : Option Bool) (returned : Option Label)
    (xs ys ds left acc scratch out cp cs : List Bool) : C.State Stack Label :=
  ⟨pc,flag,returned,payload xs ys ds left acc scratch out cp cs,[]⟩

/-- Actual compiled fixed finite-stack multiplier with prepared two-stack operands. -/
def machine : Turing.FinTM2 :=
  SemiprimeD1StackCalls.machine input (.inl .right) (.control .start) code

/-- The pure byte recurrence used only to state the execution invariant. -/
def digitStep (ys acc : List Bool) (bit : Bool) : List Bool :=
  if bit then (SemiprimeBitArithmetic.addBits ys (false::acc) false).bits else false::acc

/-- MSB-first execution is exactly the original raw multiplication recurrence. -/
theorem fold_digits (xs ys : List Bool) :
    xs.reverse.foldl (digitStep ys) []=(SemiprimeBitArithmetic.mulBits xs ys).bits := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.reverse_cons,List.foldl_append,List.foldl_cons,List.foldl_nil,ih]
    cases x <;> rfl

/-- The loop's actual raw accumulator grows only polynomially, including padding. -/
theorem digitStep_length (ys acc : List Bool) (bit : Bool) :
    (digitStep ys acc bit).length ≤ acc.length+ys.length+2 := by
  cases bit
  · simp only [digitStep, Bool.false_eq_true, ite_false, List.length_cons]; omega
  · have h:=(SemiprimeBitArithmetic.addBits_counts ys (false::acc) false).2.2.2.2
    simp only [digitStep,ite_true,List.length_cons] at *
    omega

end RiemannGaussian.SemiprimeD1StackMultiplier
