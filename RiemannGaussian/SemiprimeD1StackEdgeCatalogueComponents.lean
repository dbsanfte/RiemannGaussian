/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackEdgeCatalogue

/-! # Actual component calls of the original edge transducer -/
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 16000
set_option synthInstance.maxSize 8192
set_option Elab.async false
namespace RiemannGaussian.SemiprimeD1StackEdgeCatalogueComponents
open SemiprimeD1StackEdgeCatalogue
open SemiprimeD1StackProcedureFragments (Runs included_call)
open SemiprimeSourceHistogramKeyBits (frame)

/-- Original source stacks embed literally. -/
theorem catStack_injective : Function.Injective catStack := Sum.inl_injective
/-- Parser operands are physically disjoint. -/
theorem fieldStack_injective (part:Fin 5) : Function.Injective (fieldStack part) := by
  intro a b h
  rcases a with a|a <;> rcases b with b|b
  · cases a <;> cases b <;> simp_all [fieldStack,reader,catStack,cache,aux]
  · cases a <;> cases b <;> simp_all [fieldStack,reader,catStack,cache,aux]
  · cases a;cases b <;> simp_all [fieldStack,reader,catStack,cache,aux]
  · cases a;cases b;rfl
/-- The actual framing source is separate from its buffer. -/
theorem frameSource_buffer (part:Fin 6) : frameSource part≠aux .frameBuffer := by
  unfold frameSource
  split <;> simp [aux,cache]
/-- The actual framing source is separate from scratch. -/
theorem frameSource_scratch (part:Fin 6) : frameSource part≠aux .frameScratch := by
  unfold frameSource
  split <;> simp [aux,cache]
/-- Frame operands are physically disjoint. -/
theorem frameStack_injective (part:Fin 6) : Function.Injective (frameStack part) := by
  have h0:=frameSource_buffer part
  have h1:=frameSource_scratch part
  intro a b h
  fin_cases a <;> fin_cases b <;> simp_all [frameStack,aux]
/-- Reversal source and output are distinct in either static mode. -/
theorem reverseStack_injective (finish:Bool) : Function.Injective (reverseStack finish) := by
  cases finish <;> decide
/-- The tag copy has three distinct actual operands. -/
theorem copyStack_injective : Function.Injective copyStack := by decide

/-- An actual parsed field overwrites precisely reader/cache/valid, retaining every other role. -/
theorem field_call (part:Fin 5) (data:Stack→List Bool) (word tail:List Bool)
    (hr:data reader=frame word tail) (hc:data (cache part)=[])
    (hs:data (aux .fieldScratch)=[]) (hv:data (aux .valid)=[]) :
    Runs program (8*word.length+7) (.inl (.field part)) data (.inl (.popValid part))
      (Function.update (Function.update (Function.update data reader tail) (cache part) word) (aux .valid) [true]) := by
  apply included_call program (fieldStack part) (fieldLabel part) (fieldStack_injective part) Field.code
    (Field.active .tagPop (none,false)) (fun _=>rfl) (.inl (.field part)) (.inl (.popValid part)) rfl
    (8*word.length+6) (SemiprimeD1TensorTapeFieldBytecode.initial (frame word tail) [])
    (⟨none,none,Sum.elim (SemiprimeD1TensorTapeFieldMachine.contents tail [] word) (fun _=>[true])⟩:B.State Field.Stack Field.Label)
  · rfl
  · rfl
  · exact SemiprimeD1TensorTapeFieldBytecode.framed_run word tail []
  · constructor
    · intro k
      cases k with
      | inl k => cases k <;> simp [fieldStack,SemiprimeD1TensorTapeFieldBytecode.initial,
          SemiprimeD1TensorTapeFieldMachine.contents,hr,hc,hs]
      | inr k => cases k;simp [fieldStack,SemiprimeD1TensorTapeFieldBytecode.initial,hv]
    · intro k _;rfl
  · have hs':data (.inr (.inr Aux.fieldScratch))=[]:=hs
    constructor
    · intro k
      cases k with
      | inl k => cases k <;> simp [fieldStack,reader,catStack,cache,aux,Function.update,
          SemiprimeD1TensorTapeFieldMachine.contents,hs']
      | inr k => cases k;simp [fieldStack,aux,Function.update]
    · intro k hk
      have h0:k≠reader:=by intro h;exact hk (.inl .input) h.symm
      have h1:k≠cache part:=by intro h;exact hk (.inl .output) h.symm
      have h2:k≠aux .valid:=by intro h;exact hk (.inr ()) h.symm
      simp [Function.update,h0,h1,h2]

/-- Actual framing preserves its cached source and allocates only its physical buffer. -/
theorem frame_call (part:Fin 6) (side:Bool) (data:Stack→List Bool)
    (hb:data (aux .frameBuffer)=[]) (hs:data (aux .frameScratch)=[]) :
    Runs program (6*(data (frameSource part)).length+5) (.inl (.emitFrame side part)) data
      (.inl (.emitReverse side part))
      (Function.update data (aux .frameBuffer) (frame (data (frameSource part)) [])) := by
  apply included_call program (frameStack part) (frameLabel part) (frameStack_injective part)
    SemiprimeD1StackFrame.code 0 (fun _=>rfl) (.inl (.emitFrame side part)) (.inl (.emitReverse side part)) rfl
    (6*(data (frameSource part)).length+4)
    (SemiprimeD1StackFrame.state 0 none (data (frameSource part)) [] [])
    (SemiprimeD1StackFrame.done (data (frameSource part)) (frame (data (frameSource part)) []))
  · rfl
  · rfl
  · exact SemiprimeD1StackFrame.frame_words _ [] none
  · constructor
    · intro k;fin_cases k <;> simp [frameStack,SemiprimeD1StackFrame.state,SemiprimeD1StackFrame.payload,hb,hs]
    · intro k _;rfl
  · have h0:frameSource part≠(.inr (.inr Aux.frameBuffer):Stack):=frameSource_buffer part
    have hs':data (.inr (.inr Aux.frameScratch))=[]:=hs
    constructor
    · intro k
      fin_cases k <;> simp [frameStack,SemiprimeD1StackFrame.done,SemiprimeD1StackFrame.payload,
        Function.update,aux,h0,hs']
    · intro k hk
      have hn:k≠aux .frameBuffer:=by intro h;exact hk 1 h.symm
      exact Function.update_of_ne hn _ _

/-- Literal reversal input for either of the two static roles. -/
def reverseInput (finish:Bool) : Stack := if finish then aux .reversed else aux .frameBuffer
/-- Literal reversal destination for either static role. -/
def reverseOutput (finish:Bool) : Stack := if finish then aux .output else aux .reversed
/-- Both actual reversal operands are distinct. -/
theorem reverse_disjoint (finish:Bool) : reverseInput finish≠reverseOutput finish := by cases finish <;> decide
/-- Actual physical reversal consumes its input and prepends every reversed bit to output. -/
theorem reverse_call (finish:Bool) (data:Stack→List Bool) (pc next:Label)
    (hc:program pc=.call (reverseLabel finish 0) next) :
    Runs program (2*(data (reverseInput finish)).length+3) pc data next
      (Function.update (Function.update data (reverseInput finish) []) (reverseOutput finish)
        ((data (reverseInput finish)).reverse++data (reverseOutput finish))) := by
  apply included_call program (reverseStack finish) (reverseLabel finish) (reverseStack_injective finish)
    SemiprimeD1StackReverseWord.code 0 (fun _=>rfl) pc next hc
    (2*(data (reverseInput finish)).length+2)
    (SemiprimeD1StackReverseWord.state none (data (reverseInput finish)) (data (reverseOutput finish)))
    (SemiprimeD1StackReverseWord.done ((data (reverseInput finish)).reverse++data (reverseOutput finish)))
  · rfl
  · rfl
  · exact SemiprimeD1StackReverseWord.reverse_run _ _ none
  · constructor
    · intro k;fin_cases k <;> rfl
    · intro k _;rfl
  · constructor
    · intro k
      fin_cases k <;> cases finish <;> simp [reverseStack,reverseInput,reverseOutput,aux,
        SemiprimeD1StackReverseWord.done,SemiprimeD1StackReverseWord.payload,Function.update]
    · intro k hk
      have h0:k≠reverseInput finish:=by intro h;exact hk 0 h.symm
      have h1:k≠reverseOutput finish:=by intro h;exact hk 1 h.symm
      simp [Function.update,h0,h1]

/-- The tag-test input is acquired by a real source-preserving Copy call. -/
theorem copy_call (data:Stack→List Bool) (hs:data (aux .copyScratch)=[]) :
    Runs program (5*(data (cache 0)).length+4) (.inl .copyTag) data (.inl (.test 0))
      (Function.update data (aux .tagReader) (data (cache 0)++data (aux .tagReader))) := by
  apply included_call program copyStack copyLabel copyStack_injective SemiprimeD1StackCopy.code 0
    (fun _=>rfl) (.inl .copyTag) (.inl (.test 0)) rfl
    (5*(data (cache 0)).length+3)
    (SemiprimeD1StackCopy.state 0 none (data (cache 0)) (data (aux .tagReader)) [])
    (SemiprimeD1StackCopy.done (data (cache 0)) (data (cache 0)++data (aux .tagReader)))
  · rfl
  · rfl
  · exact SemiprimeD1StackCopy.copy_words _ _ none
  · constructor
    · intro k;fin_cases k <;> simp [copyStack,SemiprimeD1StackCopy.state,SemiprimeD1StackCopy.payload,hs]
    · intro k _;rfl
  · have hs':data (.inr (.inr Aux.copyScratch))=[]:=hs
    constructor
    · intro k;fin_cases k <;> simp [copyStack,SemiprimeD1StackCopy.done,SemiprimeD1StackCopy.payload,
        Function.update,cache,aux,hs']
    · intro k hk
      have hn:k≠aux .tagReader:=by intro h;exact hk 1 h.symm
      exact Function.update_of_ne hn _ _
end RiemannGaussian.SemiprimeD1StackEdgeCatalogueComponents

