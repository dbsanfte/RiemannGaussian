/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackWordFitBounds
import RiemannGaussian.SemiprimeD1StackExprCodec
import RiemannGaussian.SemiprimeD1TensorTapeFieldBytecode
import RiemannGaussian.SemiprimeD1StackProcedureCallsTrace

/-! # Actual physical public expression literal branch
The fixed table reads both literal tags, parses the actual encoded payload,
checks the physically produced parser flag, and fits the word using the actual
retained modulus/template. The unconsumed expression suffix remains physical.
-/
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option Elab.async false
namespace RiemannGaussian.SemiprimeD1StackExprLiteral
namespace C
export SemiprimeD1StackCalls (Instruction State execute step run)
end C
namespace Fit
export SemiprimeD1StackWordFit (Stack Label program operand template scratch output store initial)
end Fit
namespace Field
export SemiprimeD1TensorTapeFieldBytecode (Stack Label code active initial)
end Field

/-- Seven fixed Boolean roles: the fitter bank, code suffix and parser flag. -/
abbrev Stack := Fit.Stack⊕(Unit⊕Unit)
/-- Original encoded expression stream, physically consumed from its head. -/
def inputCode : Stack := .inr (.inl ())
/-- Physical parser validity bit. -/
def valid : Stack := .inr (.inr ())
/-- The actual fixed-width expression value output. -/
def output : Stack := .inl Fit.output
/-- Static parser/fitter operand wiring. -/
def fieldStack : Field.Stack→Stack
  | .inl .input => inputCode
  | .inl .scratch => .inl Fit.scratch
  | .inl .output => .inl Fit.operand
  | .inr _ => valid
/-- Literal finite pipeline control. -/
inductive Control where
  | start | secondTag | fieldCall | checkValid | fitCall | done | bad
  deriving DecidableEq,Repr
instance : Fintype Control := Fintype.ofList
  [.start,.secondTag,.fieldCall,.checkValid,.fitCall,.done,.bad] (by intro k;cases k <;> simp)
/-- Complete component labels, fixed before code/data sizes. -/
abbrev Label := Control⊕(Field.Label⊕Fit.Label)
/-- Static local instruction inclusion. -/
def ctl : Control→Label := Sum.inl
/-- Static literal field-reader inclusion. -/
def fieldLabel (pc : Field.Label) : Label := .inr (.inl pc)
/-- Static literal width-fitting inclusion. -/
def fitLabel (pc : Fit.Label) : Label := .inr (.inr pc)

/-- The ONE actual instruction table. Neither a parser nor fitter opcode occurs. -/
def program : Label→C.Instruction Stack Label
  | .inl .start => .base (.pop inputCode (ctl .bad) (ctl .secondTag) (ctl .bad))
  | .inl .secondTag => .base (.pop inputCode (ctl .bad) (ctl .fieldCall) (ctl .bad))
  | .inl .fieldCall => .call (fieldLabel (Field.active .tagPop (none,false))) (ctl .checkValid)
  | .inl .checkValid => .base (.pop valid (ctl .bad) (ctl .bad) (ctl .fitCall))
  | .inl .fitCall => .call (fitLabel .start) (ctl .done)
  | .inl .done | .inl .bad => .base .halt
  | .inr (.inl pc) => SemiprimeD1StackMultiplierLink.instruction fieldStack fieldLabel (Field.code pc)
  | .inr (.inr pc) => SemiprimeD1StackValidationLink.instruction Sum.inl fitLabel (Fit.program pc)

/-- Exact reached-cell view, not an executing decoded syntax supplier. -/
def store (code : List Bool) (fit : Fit.Stack→List Bool) (flag : List Bool) : Stack→List Bool :=
  Sum.elim fit (Sum.elim (fun _=>code) (fun _=>flag))
/-- Only the physical syntax and binary template are prepared, no literal answer. -/
def input (code cached : List Bool) : Stack→List Bool := store code (Fit.store [] cached [] [] []) []
/-- Concrete actual source entry before reading any tags. -/
def initial (code cached : List Bool) : C.State Stack Label :=
  ⟨some (ctl .start),none,none,input code cached,[]⟩
/-- Every parser argument/work/result stack is actually distinct. -/
theorem fieldStack_injective : Function.Injective fieldStack := by
  intro i j h
  rcases i with i|i <;> rcases j with j|j
  · cases i <;> cases j <;> simp_all [fieldStack,inputCode,Fit.scratch,Fit.operand]
  · cases i <;> simp_all [fieldStack,inputCode,valid]
  · cases j <;> simp_all [fieldStack,inputCode,valid]
  · cases i;cases j;rfl
/-- One fixed finite literal-reader machine; caller syntax acquisition remains paid separately. -/
def machine : Turing.FinTM2 := SemiprimeD1StackCalls.machine inputCode output (ctl .start) program
/-- Every data and real return-tag alphabet is finite before the original input. -/
theorem all_alphabets_finite : ∀k,Finite (machine.Γ k) :=
  SemiprimeD1StackCalls.all_alphabets_finite inputCode output (ctl .start) program
/-- No syntax tree or decoded natural/list is stored in transient finite control. -/
theorem control_finite : Finite machine.σ :=
  SemiprimeD1StackCalls.control_finite inputCode output (ctl .start) program

end RiemannGaussian.SemiprimeD1StackExprLiteral
