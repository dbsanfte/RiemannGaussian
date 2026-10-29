/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackProcedureTrace
import RiemannGaussian.SemiprimeD1StackPhysicalLoops
import RiemannGaussian.SemiprimeBitDivision

/-! # Literal width fitting for public checker words
The binary template is retained by a real Copy call. Each copied template cell
causes a physical operand read and zero-padding when absent. Excess operand
cells are physically cleared, then the accumulated word is actually reversed.
The template VALUE is never decoded; only its physical width is used.
-/
set_option autoImplicit false
set_option maxHeartbeats 700000
set_option Elab.async false
namespace RiemannGaussian.SemiprimeD1StackWordFit
namespace C
export SemiprimeD1StackCalls (Instruction State execute step run)
end C

/-- Five fixed Boolean data roles: input, cache, counter, scratch and output. -/
abbrev Stack := Fin 5
/-- Actual operand stack. -/
def operand : Stack := 0
/-- Retained actual binary width template. -/
def template : Stack := 1
/-- Disposable physical copy of the template, not a unary decoded value. -/
def counter : Stack := 2
/-- Shared real copy-restoration and reverse-accumulation scratch. -/
def scratch : Stack := 3
/-- Fixed-width fitted word output. -/
def output : Stack := 4
/-- Three distinct literal Copy roles. -/
def copyStack (k : Fin 3) : Stack := if k=0 then template else if k=1 then counter else scratch
/-- Actual finite labels, fixed before all operand lengths. -/
inductive Label where
  | start | take | read | save (b : Bool) | clear | restore | write (b : Bool) | done
  | copy (pc : Fin 9)
  deriving DecidableEq,Fintype,Repr

/-- ONE finite instruction table; no fitting/value/arithmetic opcode exists. -/
def program : Label→C.Instruction Stack Label
  | .start => .call (.copy 0) .take
  | .take => .base (.pop counter .clear .read .read)
  | .read => .base (.pop operand (.save false) (.save false) (.save true))
  | .save b => .base (.push scratch b .take)
  | .clear => .base (.pop operand .restore .clear .clear)
  | .restore => .base (.pop scratch .done (.write false) (.write true))
  | .write b => .base (.push output b .restore)
  | .done => .base .halt
  | .copy pc => SemiprimeD1StackMultiplierLink.instruction copyStack Label.copy (SemiprimeD1StackCopy.code pc)

/-- Exact mathematical view of the physical payload. -/
def store (word cached count acc out : List Bool) : Stack→List Bool := fun k=>
  if k=0 then word else if k=1 then cached else if k=2 then count else if k=3 then acc else out
/-- Prepared physical word/template source entry; all work and return cells empty. -/
def initial (word cached : List Bool) : C.State Stack Label :=
  ⟨some .start,none,none,store word cached [] [] [],[]⟩
/-- Fixed actual machine; acquiring the physical template is the caller's task. -/
def machine : Turing.FinTM2 := SemiprimeD1StackCalls.machine operand output .start program
/-- Real Copy operands are pairwise distinct. -/
theorem copyStack_injective : Function.Injective copyStack := by decide
/-- All data and real return-tag alphabets are finite before the input. -/
theorem all_alphabets_finite : ∀k,Finite (machine.Γ k) :=
  SemiprimeD1StackCalls.all_alphabets_finite operand output .start program
/-- Finite transient control contains no word, natural value or evaluator. -/
theorem control_finite : Finite machine.σ :=
  SemiprimeD1StackCalls.control_finite operand output .start program

end RiemannGaussian.SemiprimeD1StackWordFit
