/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackPortCatalogueComponents
/-! # Real physical parser/framing/reversal calls of the occurrence catalogue -/
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 32000
set_option synthInstance.maxSize 131072
set_option Elab.async false
namespace RiemannGaussian.SemiprimeD1StackPortCataloguePrimitives
open SemiprimeD1StackPortCatalogue
open SemiprimeD1StackPortCatalogueComponents
open SemiprimeD1StackProcedureFragments (Runs included_call)
open SemiprimeSourceHistogramKeyBits (frame)
/-- An actual parsed field overwrites precisely (aux .reader)/cache/valid, retaining every other role. -/
theorem field_call (part:Fin 5) (data:Stack→List Bool) (word tail:List Bool)
    (hr:data (aux .reader)=frame word tail) (hc:data (cache part)=[])
    (hs:data (oldAux .fieldScratch)=[]) (hv:data (oldAux .valid)=[]) :
    Runs program (8*word.length+7) (.local (.field part)) data (.local (.popValid part))
      (Function.update (Function.update (Function.update data (aux .reader) tail) (cache part) word) (oldAux .valid) [true]) := by
  apply included_call program (fieldStack part) (Label.field part) (fieldStack_injective part) Field.code
    (Field.active .tagPop (none,false)) (fun _=>rfl) (.local (.field part)) (.local (.popValid part)) rfl
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
  · have hs':data (.inl (.inr (.inr SemiprimeD1StackEdgeCatalogue.Aux.fieldScratch)))=[]:=hs
    constructor
    · intro k
      cases k with
      | inl k => cases k <;> simp [fieldStack,oldAux,edgeStack,E.aux,cache,E.cache,aux,Function.update,
          SemiprimeD1TensorTapeFieldMachine.contents,hs']
      | inr k => cases k;simp [fieldStack,oldAux,edgeStack,E.aux,Function.update]
    · intro k hk
      have h0:k≠(aux .reader):=by intro h;exact hk (.inl .input) h.symm
      have h1:k≠cache part:=by intro h;exact hk (.inl .output) h.symm
      have h2:k≠oldAux .valid:=by intro h;exact hk (.inr ()) h.symm
      simp [Function.update,h0,h1,h2]

/-- Actual framing preserves its cached source and allocates only its physical buffer. -/
theorem frame_call (part:Fin 8) (data:Stack→List Bool)
    (hb:data (oldAux .frameBuffer)=[]) (hs:data (oldAux .frameScratch)=[]) :
    Runs program (6*(data (frameSource part)).length+5) (.local (.emitFrame part)) data
      (.local (.emitReverse part))
      (Function.update data (oldAux .frameBuffer) (frame (data (frameSource part)) [])) := by
  apply included_call program (frameStack part) (Label.frame part) (frameStack_injective part)
    SemiprimeD1StackFrame.code 0 (fun _=>rfl) (.local (.emitFrame part)) (.local (.emitReverse part)) rfl
    (6*(data (frameSource part)).length+4)
    (SemiprimeD1StackFrame.state 0 none (data (frameSource part)) [] [])
    (SemiprimeD1StackFrame.done (data (frameSource part)) (frame (data (frameSource part)) []))
  · rfl
  · rfl
  · exact SemiprimeD1StackFrame.frame_words _ [] none
  · constructor
    · intro k;fin_cases k <;> simp [frameStack,SemiprimeD1StackFrame.state,SemiprimeD1StackFrame.payload,hb,hs]
    · intro k _;rfl
  · have h0:frameSource part≠(.inl (.inr (.inr SemiprimeD1StackEdgeCatalogue.Aux.frameBuffer)):Stack):=frameSource_buffer part
    have hs':data (.inl (.inr (.inr SemiprimeD1StackEdgeCatalogue.Aux.frameScratch)))=[]:=hs
    constructor
    · intro k
      fin_cases k <;> simp [frameStack,SemiprimeD1StackFrame.done,SemiprimeD1StackFrame.payload,
        Function.update,oldAux,edgeStack,E.aux,h0,hs']
    · intro k hk
      have hn:k≠oldAux .frameBuffer:=by intro h;exact hk 1 h.symm
      exact Function.update_of_ne hn _ _

/-- Literal reversal input for either of the two static roles. -/
def reverseInput (finish:Bool) : Stack := if finish then oldAux .reversed else oldAux .frameBuffer
/-- Literal reversal destination for either static role. -/
def reverseOutput (finish:Bool) : Stack := if finish then aux .output else oldAux .reversed
/-- Both actual reversal operands are distinct. -/
theorem reverse_disjoint (finish:Bool) : reverseInput finish≠reverseOutput finish := by cases finish <;> decide
/-- Actual physical reversal consumes its input and prepends every reversed bit to output. -/
theorem reverse_call (finish:Bool) (data:Stack→List Bool) (pc next:Label)
    (hc:program pc=.call (Label.reverse finish 0) next) :
    Runs program (2*(data (reverseInput finish)).length+3) pc data next
      (Function.update (Function.update data (reverseInput finish) []) (reverseOutput finish)
        ((data (reverseInput finish)).reverse++data (reverseOutput finish))) := by
  apply included_call program (reverseStack finish) (Label.reverse finish) (reverseStack_injective finish)
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
      fin_cases k <;> cases finish <;> simp [reverseStack,reverseInput,reverseOutput,oldAux,edgeStack,E.aux,aux,
        SemiprimeD1StackReverseWord.done,SemiprimeD1StackReverseWord.payload,Function.update]
    · intro k hk
      have h0:k≠reverseInput finish:=by intro h;exact hk 0 h.symm
      have h1:k≠reverseOutput finish:=by intro h;exact hk 1 h.symm
      simp [Function.update,h0,h1]

/-- The original descriptor tape is physically copied before the edge parser consumes it. -/
theorem copy_call (data:Stack→List Bool) (hs:data (oldAux .copyScratch)=[]) :
    Runs program (5*(data vertexReader).length+4) (.local .copyVertex) data (.local .callEdges)
      (Function.update data (aux .reader) (data vertexReader++data (aux .reader))) := by
  apply included_call program copyStack Label.copy copyStack_injective SemiprimeD1StackCopy.code 0
    (fun _=>rfl) (.local .copyVertex) (.local .callEdges) rfl
    (5*(data vertexReader).length+3)
    (SemiprimeD1StackCopy.state 0 none (data vertexReader) (data (aux .reader)) [])
    (SemiprimeD1StackCopy.done (data vertexReader) (data vertexReader++data (aux .reader)))
  · rfl
  · rfl
  · exact SemiprimeD1StackCopy.copy_words _ _ none
  · constructor
    · intro k;fin_cases k <;> simp [copyStack,SemiprimeD1StackCopy.state,SemiprimeD1StackCopy.payload,hs]
    · intro k _;rfl
  · have hs':data (.inl (.inr (.inr SemiprimeD1StackEdgeCatalogue.Aux.copyScratch)))=[]:=hs
    constructor
    · intro k;fin_cases k <;> simp [copyStack,SemiprimeD1StackCopy.done,SemiprimeD1StackCopy.payload,
        Function.update,vertexReader,vertexStack,edgeStack,E.catStack,aux,oldAux,E.aux,hs']
    · intro k hk
      have hn:k≠aux .reader:=by intro h;exact hk 1 h.symm
      exact Function.update_of_ne hn _ _
end RiemannGaussian.SemiprimeD1StackPortCataloguePrimitives
