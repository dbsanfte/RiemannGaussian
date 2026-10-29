/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackRootPhaseParametersInventory
import RiemannGaussian.SemiprimeD1StackHeapReadBounds
import RiemannGaussian.SemiprimeD1StackProcedureCallsTrace

/-! # Actual phase-cache dereference and complete forty-eight-word restoration
Only an actual physical heap, allocation counter and issued reference enter.
One real heap read and forty-eight real field parsers restore the whole stopped
phase bank. The immutable heap and original reference survive; phase geometry,
metadata and precision are not rerun. This is a prepared cache consumer, whose
caller must supply bytes produced by the actual phase-cache acquisition.
-/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackPhaseBankRestore
namespace C
export SemiprimeD1StackCalls (Instruction State)
end C
namespace P
export SemiprimeD1StackPhaseWorkingPrecision (Stack aux)
end P
namespace H
export SemiprimeD1StackHeapRead (Stack Label program input initial)
export SemiprimeD1StackHeapReadExecution (done)
end H
namespace I
export SemiprimeD1StackRootPhaseParametersInventory (roles role roles_length roles_nodup roles_complete)
end I
namespace Field
export SemiprimeD1TensorTapeFieldBytecode (Stack Label code active)
end Field
/-- All actual forty-eight phase words and ten actual heap-read words. -/
abbrev Stack := P.Stack⊕H.Stack
/-- The complete restored phase bank is directly available to the next real call. -/
def phaseStack : P.Stack→Stack := Sum.inl
/-- The entire actual heap reader, including its heap and issued-reference words. -/
def heapStack : H.Stack→Stack := Sum.inr
/-- Immutable physical heap is the designated input word. -/
def originalInput : Stack := heapStack .heap
/-- Actual binary phase precision, with the whole phase bank retained as well. -/
def output : Stack := phaseStack (P.aux .output)
/-- Literal heap, field-validation and EOF phases; no data index lives in control. -/
inductive Control where
  | start | heapCheck | field (part:Fin 48) | check (part:Fin 48) | eof | done | abort
  deriving DecidableEq,Fintype
/-- Fixed real return labels, independent of every heap, record and original N. -/
abbrev Label := Control⊕(H.Label⊕(Fin 48×Field.Label))
/-- Actual heap-reader label inclusion. -/
def heapLabel (pc:H.Label) : Label := .inr (.inl pc)
/-- Actual field-parser label inclusion; the position is a fixed finite code label. -/
def fieldLabel (part:Fin 48) (pc:Field.Label) : Label := .inr (.inr (part,pc))
local notation "ctl" => (Sum.inl : Control→Label)
/-- Each field parser writes the corresponding physical phase word directly. -/
def fieldStack (part:Fin 48) : Field.Stack→Stack
  | .inl .input=>heapStack .output
  | .inl .scratch=>heapStack .fieldScratch
  | .inl .output=>phaseStack (I.role part)
  | .inr _=>heapStack .valid
/-- Static inverse proves that no field, phase, scratch or validation role aliases. -/
def fieldInverse : Stack→Field.Stack
  | .inl _=>.inl .output
  | .inr .output=>.inl .input
  | .inr .fieldScratch=>.inl .scratch
  | _=>.inr ()
/-- Next field is a fixed successor code location; the final field enters a real EOF test. -/
def next (part:Fin 48) : Label :=
  if h:part.val<47 then ctl (.field ⟨part.val+1,by omega⟩) else ctl .eof
/-- One literal program dereferences and restores the complete cached phase. -/
def program : Label→C.Instruction Stack Label
  | .inl .start=>.call (heapLabel (.inl .start)) (ctl .heapCheck)
  | .inl .heapCheck=>.base (.pop (heapStack .valid) (ctl .abort) (ctl .abort) (ctl (.field 0)))
  | .inl (.field part)=>.call (fieldLabel part (Field.active .tagPop (none,false))) (ctl (.check part))
  | .inl (.check part)=>.base (.pop (heapStack .valid) (ctl .abort) (ctl .abort) (next part))
  | .inl .eof=>.base (.peek (heapStack .output) (ctl .done) (ctl .abort) (ctl .abort))
  | .inl .done|.inl .abort=>.base .halt
  | .inr (.inl pc)=>SemiprimeD1StackValidationLink.instruction heapStack heapLabel (H.program pc)
  | .inr (.inr (part,pc))=>SemiprimeD1StackMultiplierLink.instruction
      (fieldStack part) (fieldLabel part) (Field.code pc)
/-- Exact phase and heap-reader store; bank functions are mathematical state notation only. -/
def data (phase:P.Stack→List Bool) (heap:H.Stack→List Bool) : Stack→List Bool :=Sum.elim phase heap
/-- Actual prepared entry has heap/counter/reference bytes only, with every phase word empty. -/
def initial (heap counter reference:List Bool) : C.State Stack Label :=
  ⟨some (ctl .start),none,none,data (fun _=>[]) (H.input heap counter reference),[]⟩
/-- Fixed phase record codec, matching the producer's forty-eight consecutive frames. -/
def record (bank:P.Stack→List Bool) : List Bool :=
  I.roles.foldr (fun k tail=>SemiprimeSourceHistogramKeyBits.frame (bank k) tail) []
/-- Restored bank and unchanged physical heap/counter/reference, with every reader work word clear. -/
def result (bank:P.Stack→List Bool) (heap counter reference:List Bool) : Stack→List Bool :=
  data bank (H.input heap counter reference)
/-- Actual clean return after all forty-eight fields and the real EOF test. -/
def done (bank:P.Stack→List Bool) (heap counter reference:List Bool) : C.State Stack Label :=
  ⟨none,none,none,result bank heap counter reference,[]⟩
/-- One fixed finite machine; its prepared entry is joined to the actual producer by the caller. -/
def machine : Turing.FinTM2 :=SemiprimeD1StackCalls.machine originalInput output (ctl .start) program
/-- Static parser inverse is exact for every actual position and parser role. -/
theorem field_inverse (part:Fin 48) (k:Field.Stack) :fieldInverse (fieldStack part k)=k :=by
  rcases k with k|k
  · cases k <;> rfl
  · cases k;rfl
/-- Each actual field parser has four physically distinct Boolean operands. -/
theorem field_injective (part:Fin 48) :Function.Injective (fieldStack part) :=by
  intro a b h
  have hh:=congrArg fieldInverse h
  simpa only [field_inverse] using hh
/-- Fifty-eight physical Boolean roles include all actual heap-reader work. -/
theorem stack_card :Fintype.card Stack=58 :=by
  rw [Fintype.card_sum,SemiprimeD1StackPhaseWorkingPrecision.stack_card,SemiprimeD1StackHeapRead.stack_card]
/-- Runtime flags contain only finite Boolean and real-return-label values. -/
theorem control_finite :Finite machine.σ :=SemiprimeD1StackCalls.control_finite _ _ _ _
/-- All data and real return alphabets are fixed finite before every input. -/
theorem alphabets_finite :∀k,Finite (machine.Γ k) :=SemiprimeD1StackCalls.all_alphabets_finite _ _ _ _
end RiemannGaussian.SemiprimeD1StackPhaseBankRestore
