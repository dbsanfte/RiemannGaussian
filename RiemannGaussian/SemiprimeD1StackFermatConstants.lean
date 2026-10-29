/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackTransformBounds
import RiemannGaussian.SemiprimeD1StackValidationLink
import RiemannGaussian.SemiprimeD1StackFermatWords

/-! # Original-input physical Fermat constant production
Actual metadata R/E counters are acquired by the real nested-call transform
program. Literal copy/pop/push loops write modulus and normalizer bit patterns;
no native power, negation, modulo or encoded constant answer is executed.
-/
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 16000
set_option Elab.async false
namespace RiemannGaussian.SemiprimeD1StackFermatConstants
namespace Meta
export SemiprimeD1StackTransform (Stack Label program input initial)
end Meta
namespace C
export SemiprimeD1StackCalls (Instruction State execute step run)
end C
namespace B
export SemiprimeD1StackBytecode (Instruction State execute step run)
end B
namespace LinkB
export SemiprimeD1StackMultiplierLink (instruction DataRel data_unique Rel run_rel)
end LinkB
namespace LinkC
export SemiprimeD1StackValidationLink (instruction Rel run_rel)
end LinkC

/-- Original metadata stacks plus two actual constant-word outputs. -/
abbrev Stack := Meta.Stack⊕Bool

/-- Fixed finite local constant-producing control. -/
inductive Local where
  | start | modStart | modDrop | modHigh | modLoop | modZero | modLow
  | normStart | normDrop | normCopyE | normLoop | normOne | normSubR
  | normZeros | normZero | normLow | halt | bad
  deriving DecidableEq,Repr
/-- Literal finite local-label catalogue. -/
instance : Fintype Local where
  elems:={.start,.modStart,.modDrop,.modHigh,.modLoop,.modZero,.modLow,.normStart,.normDrop,
    .normCopyE,.normLoop,.normOne,.normSubR,.normZeros,.normZero,.normLow,.halt,.bad}
  complete:=by intro k;cases k <;> simp

/-- Fixed local, actual metadata and actual Copy instruction labels. -/
abbrev Label := Local⊕(Meta.Label⊕(Bool×Fin 9))

/-- Actual metadata label inclusion retains all nested source calls. -/
def metaLabel (pc:Meta.Label) : Label := .inr (.inl pc)
/-- Literal source operand of the two included Copy procedures. -/
def copyInput (mode:Bool) : Stack := .inl (if mode then .exponent else .radius)
/-- Literal destination work stack for R or E. -/
def copyOutput (mode:Bool) : Stack := .inl (if mode then .thresholdWork else .squareWork)
/-- Actual Copy operands, using the retained metadata's empty temporary. -/
def copyStack (mode:Bool) (k:Fin 3) : Stack :=
  if k=0 then copyInput mode else if k=1 then copyOutput mode else .inl .temporary
/-- Literal included Copy control labels. -/
def copyLabel (mode:Bool) (pc:Fin 9) : Label := .inr (.inr (mode,pc))

/-- Complete fixed original-input program, including metadata itself and real constant-word loops. -/
def program : Label→C.Instruction Stack Label
  | .inr (.inl pc) => LinkC.instruction Sum.inl metaLabel (Meta.program pc)
  | .inr (.inr (mode,pc)) => LinkB.instruction (copyStack mode) (copyLabel mode) (SemiprimeD1StackCopy.code pc)
  | .inl .start => .call (metaLabel (.inl .start)) (.inl .modStart)
  | .inl .modStart => .call (copyLabel false 0) (.inl .modDrop)
  | .inl .modDrop => .base (.pop (.inl .squareWork) (.inl .bad) (.inl .modHigh) (.inl .modHigh))
  | .inl .modHigh => .base (.push (.inr false) true (.inl .modLoop))
  | .inl .modLoop => .base (.pop (.inl .squareWork) (.inl .modLow) (.inl .modZero) (.inl .modZero))
  | .inl .modZero => .base (.push (.inr false) false (.inl .modLoop))
  | .inl .modLow => .base (.push (.inr false) true (.inl .normStart))
  | .inl .normStart => .call (copyLabel false 0) (.inl .normDrop)
  | .inl .normDrop => .base (.pop (.inl .squareWork) (.inl .bad) (.inl .normCopyE) (.inl .normCopyE))
  | .inl .normCopyE => .call (copyLabel true 0) (.inl .normLoop)
  | .inl .normLoop => .base (.pop (.inl .thresholdWork) (.inl .normZeros) (.inl .normOne) (.inl .normOne))
  | .inl .normOne => .base (.push (.inr true) true (.inl .normSubR))
  | .inl .normSubR => .base (.pop (.inl .squareWork) (.inl .bad) (.inl .normLoop) (.inl .normLoop))
  | .inl .normZeros => .base (.pop (.inl .squareWork) (.inl .normLow) (.inl .normZero) (.inl .normZero))
  | .inl .normZero => .base (.push (.inr true) false (.inl .normZeros))
  | .inl .normLow => .base (.push (.inr true) true (.inl .halt))
  | .inl .halt => .base .halt
  | .inl .bad => .base .halt

/-- One fixed original-input finite machine, before every binary N. -/
def machine : Turing.FinTM2 := SemiprimeD1StackCalls.machine (.inl .input) (.inr true) (.inl .start) program

/-- Only the original binary input is initialized; no metadata/constant word is preloaded. -/
def input (bits:List Bool) : Stack→List Bool := Sum.elim (Meta.input bits) (fun _=>[])
/-- Actual no-continuation original-input start. -/
def initial (bits:List Bool) : C.State Stack Label := ⟨some (.inl .start),none,none,input bits,[]⟩

/-- Both Copy inclusions use distinct actual operands. -/
theorem copyStack_injective (mode:Bool) : Function.Injective (copyStack mode) := by
  cases mode <;> decide
/-- All original metadata and output data stacks are fixed before input. -/
theorem stack_card : Fintype.card Stack=13 := by decide
/-- All metadata/local/copy labels total135 before every input. -/
theorem label_card : Fintype.card Label=135 := by decide
/-- Every stack alphabet is finite, including the fixed real return-tag alphabet. -/
theorem all_alphabets_finite : ∀k,Finite (machine.Γ k) :=
  SemiprimeD1StackCalls.all_alphabets_finite (.inl .input) (.inr true) (.inl .start) program
end RiemannGaussian.SemiprimeD1StackFermatConstants
