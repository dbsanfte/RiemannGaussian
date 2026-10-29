/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackIncrementBytecode
import RiemannGaussian.SemiprimeD1StackAssignmentBody
import RiemannGaussian.SemiprimeD1StackMultiplierLink

/-! # Literal fixed-width assignment enumeration program
The fixed procedure body logs/restores the current assignment. A real call to
the actual incrementer then produces overflow/wrapped bytes. The finite caller
consumes the overflow bit and either physically moves the wrapped word back or
reverses the completed log and halts. There is no input-sized program, native
loop counter, body evaluator, or iteration-count oracle.
-/
set_option autoImplicit false
namespace RiemannGaussian.SemiprimeD1StackAssignmentLoop
namespace C
export SemiprimeD1StackCalls (Instruction State execute step run)
end C
namespace I
export SemiprimeD1StackIncrementBytecode (Label code entry)
end I
namespace A
export SemiprimeD1StackAssignmentBody (Label code entry)
end A

/-- Fixed data stack indices, all Boolean. -/
inductive Stack | word | scratch | next | history | output deriving DecidableEq,Inhabited,Repr
instance : Fintype Stack where
  elems := {.word,.scratch,.next,.history,.output}
  complete := by intro k; cases k <;> simp

/-- Finite caller-control labels. Boolean fields encode only one literal digit. -/
inductive Control
  | bodyCall | incCall | afterInc | moveDrain | movePush (bit : Bool)
  | restore | restorePush (bit : Bool) | clearNext | finish | reverse | reversePush (bit : Bool) | halt
  deriving DecidableEq,Inhabited,Repr
instance : Fintype Control where
  elems := {.bodyCall,.incCall,.afterInc,.moveDrain,.movePush false,.movePush true,
    .restore,.restorePush false,.restorePush true,.clearNext,.finish,.reverse,.reversePush false,.reversePush true,.halt}
  complete := by
    intro k
    cases k <;> simp

/-- Fixed disjoint component labels, independent of the assignment width. -/
abbrev Label := I.Label ⊕ (A.Label ⊕ Control)

/-- The actual incrementer stack inclusion. -/
def incStack : SemiprimeD1TensorTapeFieldMachine.Stack → Stack
  | .input => .word
  | .scratch => .scratch
  | .output => .next

/-- The actual literal body stack inclusion. -/
def bodyStack : SemiprimeD1StackAssignmentBody.Stack → Stack
  | .word => .word
  | .scratch => .scratch
  | .history => .history

/-- Literal loop-control label. -/
def control (c : Control) : Label := .inr (.inr c)
/-- Literal body label inclusion. -/
def body (l : A.Label) : Label := .inr (.inl l)
/-- Literal incrementer label inclusion. -/
def increment (l : I.Label) : Label := .inl l

/-- Actual fixed whole program with included component code and real returns. -/
def code : Label → C.Instruction Stack Label
  | .inl l => SemiprimeD1StackMultiplierLink.instruction incStack increment (I.code l)
  | .inr (.inl l) => SemiprimeD1StackMultiplierLink.instruction bodyStack body (A.code l)
  | .inr (.inr .bodyCall) => .call (body A.entry) (control .incCall)
  | .inr (.inr .incCall) => .call (increment I.entry) (control .afterInc)
  | .inr (.inr .afterInc) => .base (.pop .next (control .halt) (control .moveDrain) (control .clearNext))
  | .inr (.inr .moveDrain) => .base (.pop .next (control .restore)
      (control (.movePush false)) (control (.movePush true)))
  | .inr (.inr (.movePush b)) => .base (.push .scratch b (control .moveDrain))
  | .inr (.inr .restore) => .base (.pop .scratch (control .bodyCall)
      (control (.restorePush false)) (control (.restorePush true)))
  | .inr (.inr (.restorePush b)) => .base (.push .word b (control .restore))
  | .inr (.inr .clearNext) => .base (.pop .next (control .finish) (control .clearNext) (control .clearNext))
  | .inr (.inr .finish) => .base (.push .history false (control .reverse))
  | .inr (.inr .reverse) => .base (.pop .history (control .halt)
      (control (.reversePush false)) (control (.reversePush true)))
  | .inr (.inr (.reversePush b)) => .base (.push .output b (control .reverse))
  | .inr (.inr .halt) => .base .halt

/-- Actual fixed finite-alphabet procedure machine. Return symbols are finite labels. -/
def machine := SemiprimeD1StackCalls.machine Stack.word Stack.output (control .bodyCall) code

/-- Explicit data payload, without any function-valued operand in the code. -/
def data (word scratch next history output : List Bool) : Stack → List Bool
  | .word => word
  | .scratch => scratch
  | .next => next
  | .history => history
  | .output => output

/-- All five Boolean data stacks and a literal actual return stack. -/
def state (pc : Label) (flag : Option Bool) (returned : Option Label)
    (word scratch next history output : List Bool) (frames : List Label := []) : C.State Stack Label :=
  ⟨some pc,flag,returned,data word scratch next history output,frames⟩

/-- Incrementer data inclusion is injective, with no aliasing of its stacks. -/
theorem incStack_injective : Function.Injective incStack := by
  intro a b h
  cases a <;> cases b <;> simp [incStack] at h ⊢

/-- Body data inclusion is injective, preserving the independent log. -/
theorem bodyStack_injective : Function.Injective bodyStack := by
  intro a b h
  cases a <;> cases b <;> simp [bodyStack] at h ⊢

/-- Fixed literal incrementer instruction inclusion. -/
theorem increment_code (l : I.Label) : code (increment l)=
    SemiprimeD1StackMultiplierLink.instruction incStack increment (I.code l) := rfl

/-- Fixed literal logging-body instruction inclusion. -/
theorem body_code (l : A.Label) : code (body l)=
    SemiprimeD1StackMultiplierLink.instruction bodyStack body (A.code l) := rfl

end RiemannGaussian.SemiprimeD1StackAssignmentLoop
