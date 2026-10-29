/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackOwnerLookupOriginal
import RiemannGaussian.SemiprimeD1StackFrame
import RiemannGaussian.SemiprimeD1StackReverseWord
/-! # Physical factor-major owner-fibre filtering
The input is an actually acquired stream of computed owner-ID/scope-ID pairs.
Every numeric equality, payload parse, selected framing and output reversal is
executed by the fixed finite source. Scope IDs retain their original order.
Acquiring this routed stream from original N remains explicit caller work.
-/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1200000
namespace RiemannGaussian.SemiprimeD1StackOwnerFibre
namespace C
export SemiprimeD1StackCalls (Instruction State execute step run)
end C
namespace E
export SemiprimeD1StackWordEqual (Label code)
export SemiprimeD1StackAdder (Stack store)
end E
namespace F
export SemiprimeD1TensorTapeFieldBytecode (Stack Label code active)
end F
/-- Ten fixed caller roles in addition to all four actual equality roles. -/
inductive Aux where | query | reader | fieldScratch | valid | copyScratch | payload | output | frameBuffer | frameScratch | reversed
  deriving DecidableEq
instance : Fintype Aux := Fintype.ofList [.query,.reader,.fieldScratch,.valid,.copyScratch,.payload,.output,.frameBuffer,.frameScratch,.reversed]
  (by intro k;cases k <;> simp)
/-- All fourteen Boolean data roles, independent of original input. -/
abbrev Stack := E.Stack⊕Aux
/-- Only actual one-bit comparison outcomes enter control. -/
inductive Label where
  | loop | parseKey | parsedKey | copyKey | compare | matched
  | parseValue (same:Bool) | parsedValue (same:Bool) | clear | emitTag | frame | reverse
  | finishTag | finishReverse | done | abort
  | field (part:Option Bool) (pc:F.Label) | copy (pc:Fin 9) | equal (pc:E.Label)
  | frameCode (pc:Fin 11) | reverseCode (finish:Bool) (pc:Fin 4)
  deriving Fintype
/-- None parses an owner key; some parses the actual scope-ID payload cache. -/
def fieldOutput : Option Bool→Stack
  | none=>.inl .left
  | some _=>.inr .payload
/-- Actual field parser inclusion; the computed equality selects later emission. -/
def fieldStack (part:Option Bool) : F.Stack→Stack
  | .inl .input=>.inr .reader
  | .inl .scratch=>.inr .fieldScratch
  | .inl .output=>fieldOutput part
  | .inr _=>.inr .valid
/-- Actual query-preserving copy operands. -/
def copyStack (k:Fin 3) : Stack :=
  if k=0 then .inr .query else if k=1 then .inl .right else .inr .copyScratch
/-- Actual preserving payload Frame operands. -/
def frameStack (k:Fin 3) : Stack :=
  if k=0 then .inr .payload else if k=1 then .inr .frameBuffer else .inr .frameScratch
/-- Each row reverses its new frame; finish reverses the entire collector. -/
def reverseStack (finish:Bool) (k:Fin 2) : Stack :=
  if k=0 then (if finish then .inr .reversed else .inr .frameBuffer)
  else if finish then .inr .output else .inr .reversed
/-- Every actual field read and failed-row payload erase executes this table. -/
def program : Label→C.Instruction Stack Label
  | .loop=>.base (.pop (.inr .reader) .finishTag .finishTag .parseKey)
  | .parseKey=>.call (.field none (F.active .tagPop (none,false))) .parsedKey
  | .parsedKey=>.base (.pop (.inr .valid) .abort .abort .copyKey)
  | .copyKey=>.call (.copy 0) .compare
  | .compare=>.call (.equal .loop) .matched
  | .matched=>.base (.pop (.inl .output) .abort (.parseValue false) (.parseValue true))
  | .parseValue same=>.call (.field (some same) (F.active .tagPop (none,false))) (.parsedValue same)
  | .parsedValue same=>.base (.pop (.inr .valid) .abort .abort (if same then .emitTag else .clear))
  | .clear=>.base (.pop (.inr .payload) .loop .clear .clear)
  | .emitTag=>.base (.push (.inr .reversed) true .frame)
  | .frame=>.call (.frameCode 0) .reverse
  | .reverse=>.call (.reverseCode false 0) .clear
  | .finishTag=>.base (.push (.inr .reversed) false .finishReverse)
  | .finishReverse=>.call (.reverseCode true 0) .done
  | .done | .abort=>.base .halt
  | .frameCode pc=>SemiprimeD1StackMultiplierLink.instruction frameStack Label.frameCode (SemiprimeD1StackFrame.code pc)
  | .reverseCode finish pc=>SemiprimeD1StackMultiplierLink.instruction (reverseStack finish) (Label.reverseCode finish) (SemiprimeD1StackReverseWord.code pc)
  | .field part pc=>SemiprimeD1StackMultiplierLink.instruction (fieldStack part) (Label.field part) (F.code pc)
  | .copy pc=>SemiprimeD1StackMultiplierLink.instruction copyStack Label.copy (SemiprimeD1StackCopy.code pc)
  | .equal pc=>SemiprimeD1StackMultiplierLink.instruction Sum.inl Label.equal (E.code pc)
/-- Mathematical view of the physical store, not an instruction-time evaluator. -/
def data (query reader left right comparison valid payload raw buffer output:List Bool) : Stack→List Bool
  | .inl k=>E.store left right [] comparison k
  | .inr .query=>query
  | .inr .reader=>reader
  | .inr .valid=>valid
  | .inr .payload=>payload
  | .inr .reversed=>raw
  | .inr .frameBuffer=>buffer
  | .inr .output=>output
  | .inr .fieldScratch | .inr .copyScratch | .inr .frameScratch=>[]
open SemiprimeSourceHistogramKeyBits (frame)
/-- Same two-field physical format as the owner lookup: owner-ID then scope-ID. -/
abbrev records := SemiprimeD1StackOwnerLookup.records
/-- Proof-side order-preserving selected scope-ID list. -/
def values (query:List Bool) : List (List Bool×List Bool)→List (List Bool)
  | []=>[]
  | (owner,scope)::rows=>if SemiprimeBitArithmetic.bitValue owner=SemiprimeBitArithmetic.bitValue query
      then scope::values query rows else values query rows
/-- Literal emitted row bytes, before the final false vector delimiter. -/
def selected (query:List Bool) (rows:List (List Bool×List Bool)) : List Bool :=
  (values query rows).foldr (fun word tail=>true::frame word tail) []
/-- Only the physically acquired query and catalogue are loaded initially. -/
def initial (query reader:List Bool) : C.State Stack Label :=
  ⟨some .loop,none,none,data query reader [] [] [] [] [] [] [] [],[]⟩
/-- Exact halt state with the original ordered scope-ID fibre and suffix. -/
def done (query:List Bool) (rows:List (List Bool×List Bool)) (tail:List Bool) : C.State Stack Label :=
  ⟨none,none,none,data query tail [] [] [] [] [] [] [] (SemiprimeD1TensorTapeCodec.vectorBits (values query rows)),[]⟩
/-- One fixed finite TM2 for actual scope-ID fibre acquisition. -/
def machine : Turing.FinTM2 := SemiprimeD1StackCalls.machine (.inr .reader) (.inr .output) .loop program
theorem stack_card : Fintype.card Stack=14 := by decide
theorem field_injective (part:Option Bool) : Function.Injective (fieldStack part) := by
  cases part with
  | none=>decide
  | some b=>cases b <;> decide
theorem copy_injective : Function.Injective copyStack := by decide
/-- All actual frame operands are distinct. -/
theorem frame_injective : Function.Injective frameStack := by decide
/-- Both real reversals have distinct source and destination. -/
theorem reverse_injective (finish:Bool) : Function.Injective (reverseStack finish) := by cases finish <;> decide
theorem all_alphabets_finite : ∀k,Finite (machine.Γ k) :=
  SemiprimeD1StackCalls.all_alphabets_finite (.inr .reader) (.inr .output) Label.loop program
theorem control_finite : Finite machine.σ :=
  SemiprimeD1StackCalls.control_finite (.inr .reader) (.inr .output) Label.loop program
end RiemannGaussian.SemiprimeD1StackOwnerFibre
