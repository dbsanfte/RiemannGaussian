/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackProcedureTrace
import RiemannGaussian.SemiprimeD1StackReverseWord
/-! # Two-word singleton-record accumulation by physical EOF cancellation
Reverse the acquired singleton stream ONTO the existing history. Its last
FALSE stream terminator is now at the front and is physically popped. The
remaining reversed row is already attached to history without reading that
history, parsing coefficients or constructing another record representation.
-/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackVertexRecordSplice
namespace C
export SemiprimeD1StackCalls (State Instruction)
end C
/-- Exactly the already acquired singleton record and accumulated reversed history. -/
abbrev Stack:=Fin 2
/-- Literal EOF-cancellation control. -/
inductive Control where | start | strip | done | reject deriving DecidableEq
instance controlFintype : Fintype Control := Fintype.ofList [.start,.strip,.done,.reject] (by intro k;cases k <;> simp)
/-- Finite caller and actual consuming-reversal labels. -/
inductive Label where | local (pc : Control) | reverse (pc : Fin 4) deriving Fintype
/-- One real consuming reverse, one actual EOF pop and true halt. -/
def program : Label→C.Instruction Stack Label
  | .local .start=>.call (.reverse 0) (.local .strip)
  | .local .strip=>.base (.pop 1 (.local .reject) (.local .done) (.local .reject))
  | .local .done|.local .reject=>.base .halt
  | .reverse pc=>SemiprimeD1StackMultiplierLink.instruction id Label.reverse (SemiprimeD1StackReverseWord.code pc)
/-- Both complete physical words; an old history is never an opaque machine-control object. -/
def data (record history : List Bool) : Stack→List Bool :=SemiprimeD1StackReverseWord.payload record history
/-- Actual prepared input consumes the acquired singleton record in place. -/
def initial (record history : List Bool) : C.State Stack Label:=⟨some (.local .start),none,none,data record history,[]⟩
/-- Actual halted bank has no remaining singleton-record bits. -/
def done (history : List Bool) : C.State Stack Label:=⟨none,none,none,data [] history,[]⟩
/-- Exact own clock is independent of the accumulated history length. -/
def timeBound (row : List Bool) : ℕ:=2*row.length+7
/-- Two physical words and genuine finite return alphabet. -/
def machine : Turing.FinTM2:=SemiprimeD1StackCalls.machine 0 1 (.local .start) program
/-- No table/row/history payload or native getter appears in finite control. -/
theorem control_finite : Finite machine.σ:=SemiprimeD1StackCalls.control_finite _ _ _ _
end RiemannGaussian.SemiprimeD1StackVertexRecordSplice
