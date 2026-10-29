/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1BinaryDigitAcquisitionBounds
import RiemannGaussian.SemiprimeD1StackFermatBounds
import RiemannGaussian.SemiprimeD1StackAxesBounds

/-! # Shared original-input public parameter acquisition
One fixed program runs the original binary-input digit acquisition once, then
constructs both Fermat words and both axes/depth from its retained metadata.
Every call and return is literal; no derived operand is initially supplied.
-/
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option Elab.async false
namespace RiemannGaussian.SemiprimeD1BinaryPublicAcquisition
namespace C
export SemiprimeD1StackCalls (Instruction State execute step run)
end C
namespace Digits
export SemiprimeD1BinaryDigitAcquisition (Stack Label program input initial metaStack bankStack)
end Digits
namespace Fermat
export SemiprimeD1StackFermatConstants (Stack Label program)
end Fermat
namespace Axes
export SemiprimeD1StackAxes (Stack Label program)
end Axes

/-- Twenty-eight Boolean data roles, fixed before the original input. -/
abbrev Stack := Digits.Stack⊕(Bool⊕Fin 3)

/-- Static pipeline labels, with no input-dependent control payload. -/
inductive Control where
  | start | fermatCall | axesCall | done
  deriving DecidableEq,Repr
instance : Fintype Control := Fintype.ofList [.start,.fermatCall,.axesCall,.done]
  (by intro k;cases k <;> simp)

/-- All nested component labels remain finite and fixed before N. -/
abbrev Label := Control⊕(Digits.Label⊕(Fermat.Label⊕Axes.Label))
/-- Literal outer label. -/
def mainLabel : Control→Label := Sum.inl
/-- Literal complete digit-acquisition inclusion. -/
def digitLabel (l : Digits.Label) : Label := .inr (.inl l)
/-- Literal constant-construction inclusion. -/
def fermatLabel (l : Fermat.Label) : Label := .inr (.inr (.inl l))
/-- Literal axes/depth-construction inclusion. -/
def axesLabel (l : Axes.Label) : Label := .inr (.inr (.inr l))
/-- The complete digit/metadata data are retained. -/
def digitStack : Digits.Stack→Stack := Sum.inl
/-- The constants share the ACTUALLY acquired metadata and its empty scratch. -/
def fermatStack : Fermat.Stack→Stack
  | .inl k => digitStack (Digits.metaStack k)
  | .inr b => .inr (.inl b)
/-- The axes/depth share the same acquired metadata and scratch. -/
def axesStack : Axes.Stack→Stack
  | .inl k => digitStack (Digits.metaStack k)
  | .inr i => .inr (.inr i)

/-- The ONE executing instruction table. Metadata acquisition is called once;
the later entries start at their reusable physical construction stages. -/
def program : Label→C.Instruction Stack Label
  | .inl .start => .call (digitLabel (SemiprimeD1BinaryDigitAcquisition.mainLabel .start)) (mainLabel .fermatCall)
  | .inl .fermatCall => .call (fermatLabel (.inl .modStart)) (mainLabel .axesCall)
  | .inl .axesCall => .call (axesLabel (.inl .ready)) (mainLabel .done)
  | .inl .done => .base .halt
  | .inr (.inl l) => SemiprimeD1StackValidationLink.instruction digitStack digitLabel (Digits.program l)
  | .inr (.inr (.inl l)) => SemiprimeD1StackValidationLink.instruction fermatStack fermatLabel (Fermat.program l)
  | .inr (.inr (.inr l)) => SemiprimeD1StackValidationLink.instruction axesStack axesLabel (Axes.program l)

/-- Mathematical view of physical cells, never an executing supplier. -/
def store (digits : Digits.Stack→List Bool) (constants : Bool→List Bool)
    (axes : Fin 3→List Bool) : Stack→List Bool := Sum.elim digits (Sum.elim constants axes)
/-- Only original binary N is initially present. -/
def input (bits : List Bool) : Stack→List Bool := store (Digits.input bits) (fun _=>[]) (fun _=>[])
/-- Original binary-input source state, before every acquisition. -/
def initial (bits : List Bool) : C.State Stack Label := ⟨some (mainLabel .start),none,none,input bits,[]⟩
/-- One fixed finite machine, whose output designation is its acquired digit cache. -/
def machine : Turing.FinTM2 := SemiprimeD1StackCalls.machine
  (digitStack (Digits.metaStack .input))
  (digitStack (Digits.bankStack SemiprimeD1StackDigitBank.output)) (mainLabel .start) program

/-- Both constant outputs and all shared work roles are distinct. -/
theorem fermatStack_injective : Function.Injective fermatStack := by
  intro i j h
  cases i <;> cases j <;> simp_all [fermatStack,digitStack,Digits.metaStack]
/-- Both axis outputs, depth and all shared work roles are distinct. -/
theorem axesStack_injective : Function.Injective axesStack := by
  intro i j h
  cases i <;> cases j <;> simp_all [axesStack,digitStack,Digits.metaStack]
/-- Fixed stack inventory, independent of N. -/
theorem stack_card : Fintype.card Stack=28 := by decide
/-- All Boolean and return-tag alphabets are finite before N. -/
theorem all_alphabets_finite : ∀k,Finite (machine.Γ k) :=
  SemiprimeD1StackCalls.all_alphabets_finite
    (digitStack (Digits.metaStack .input))
    (digitStack (Digits.bankStack SemiprimeD1StackDigitBank.output)) (mainLabel .start) program
/-- Finite transient control contains no natural/list/evaluator payload. -/
theorem control_finite : Finite machine.σ :=
  SemiprimeD1StackCalls.control_finite
    (digitStack (Digits.metaStack .input))
    (digitStack (Digits.bankStack SemiprimeD1StackDigitBank.output)) (mainLabel .start) program

end RiemannGaussian.SemiprimeD1BinaryPublicAcquisition
