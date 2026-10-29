/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackWordFitExecution

/-! # Physical fixed-width word extraction with the assignment suffix retained
The program reads or zero-pads exactly one copied template's worth of raw bits.
It then reverses the actual accumulated word and leaves all subsequent input
bits untouched. The raw binary template is counted by LENGTH only.
-/
set_option autoImplicit false
set_option Elab.async false
namespace RiemannGaussian.SemiprimeD1StackWordBlock
namespace C
export SemiprimeD1StackCalls (Instruction State execute step run)
end C
export SemiprimeD1StackWordFit (Stack Label operand template counter scratch output store copyStack copyStack_injective)

/-- New literal word-block code preserves the full unread source assignment.
All labels and data roles remain fixed before any input or template. -/
def program : Label→C.Instruction Stack Label
  | .start => .call (.copy 0) .take
  | .take => .base (.pop counter .restore .read .read)
  | .read => .base (.pop operand (.save false) (.save false) (.save true))
  | .save b => .base (.push scratch b .take)
  | .clear => .base (.jump .restore)
  | .restore => .base (.pop scratch .done (.write false) (.write true))
  | .write b => .base (.push output b .restore)
  | .done => .base .halt
  | .copy pc => SemiprimeD1StackMultiplierLink.instruction copyStack RiemannGaussian.SemiprimeD1StackWordFit.Label.copy (SemiprimeD1StackCopy.code pc)
/-- Only the raw assignment word and retained physical width template are input. -/
def initial (word cached : List Bool) : C.State Stack Label :=
  ⟨some .start,none,none,store word cached [] [] [],[]⟩
/-- Actual fixed finite bit machine; subsequent source bits are not discarded. -/
def machine : Turing.FinTM2 := SemiprimeD1StackCalls.machine operand output .start program
/-- All actual data and finite-label return alphabets are fixed and finite. -/
theorem all_alphabets_finite : ∀k,Finite (machine.Γ k) :=
  SemiprimeD1StackCalls.all_alphabets_finite operand output RiemannGaussian.SemiprimeD1StackWordFit.Label.start program
/-- No decoded width, original N value, list or result occurs in runtime control. -/
theorem control_finite : Finite machine.σ :=
  SemiprimeD1StackCalls.control_finite operand output RiemannGaussian.SemiprimeD1StackWordFit.Label.start program

end RiemannGaussian.SemiprimeD1StackWordBlock
