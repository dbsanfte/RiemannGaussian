/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackFactorScopePairView
/-! # Actual field calls in the original port/ID stream join -/
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 32000
set_option synthInstance.maxSize 131072
set_option Elab.async false
namespace RiemannGaussian.SemiprimeD1StackFactorScopePairPrimitives
open SemiprimeD1StackFactorScopePairs SemiprimeD1StackFactorScopePairView
open SemiprimeD1StackProcedureFragments (Runs included_call)
open SemiprimeSourceHistogramKeyBits (frame)
/-- Actual field parsing changes precisely its reader, output cache and real validity cell. -/
theorem field_call (part:Fin 9) (data:Stack→List Bool) (word tail:List Bool)
    (hr:data (aux .reader)=frame word tail) (hc:data (cache part)=[])
    (hs:data (aux .fieldScratch)=[]) (hv:data (aux .valid)=[]) :
    Runs program (8*word.length+7) (.local (.field part)) data (.local (.valid part))
      (Function.update (Function.update (Function.update data (aux .reader) tail) (cache part) word) (aux .valid) [true]) := by
  apply included_call program (fieldStack part) (Label.field part) (field_injective part) F.code
    (F.active .tagPop (none,false)) (fun _=>rfl) (.local (.field part)) (.local (.valid part)) rfl
    (8*word.length+6) (SemiprimeD1TensorTapeFieldBytecode.initial (frame word tail) [])
    (⟨none,none,Sum.elim (SemiprimeD1TensorTapeFieldMachine.contents tail [] word) (fun _=>[true])⟩:SemiprimeD1StackBytecode.State F.Stack F.Label)
  · rfl
  · rfl
  · exact SemiprimeD1TensorTapeFieldBytecode.framed_run word tail []
  · constructor
    · intro k
      cases k with
      | inl k =>
        cases k with
        | input => exact hr
        | scratch => exact hs
        | output => exact hc
      | inr k => cases k;exact hv
    · intro k _;rfl
  · constructor
    · intro k
      cases k with
      | inl k =>
        cases k with
        | input =>
          change Function.update (Function.update (Function.update data (aux .reader) tail)
            (cache part) word) (aux .valid) [true] (aux .reader)=tail
          rw [Function.update_of_ne (by decide : aux .reader≠aux .valid),Function.update_of_ne (by simp [aux,cache] : aux .reader≠cache part),Function.update_self]
        | scratch =>
          change Function.update (Function.update (Function.update data (aux .reader) tail)
            (cache part) word) (aux .valid) [true] (aux .fieldScratch)=[]
          rw [Function.update_of_ne (by decide : aux .fieldScratch≠aux .valid),
            Function.update_of_ne (by simp [aux,cache] : aux .fieldScratch≠cache part),
            Function.update_of_ne (by decide : aux .fieldScratch≠aux .reader),hs]
        | output =>
          change Function.update (Function.update (Function.update data (aux .reader) tail)
            (cache part) word) (aux .valid) [true] (cache part)=word
          rw [Function.update_of_ne (by simp [aux,cache] : cache part≠aux .valid),Function.update_self]
      | inr k => cases k;exact Function.update_self _ _ _
    · intro k hk
      have h0:k≠aux .reader:=by intro he;exact hk (.inl .input) he.symm
      have h1:k≠cache part:=by intro he;exact hk (.inl .output) he.symm
      have h2:k≠aux .valid:=by intro he;exact hk (.inr ()) he.symm
      simp only [Function.update_of_ne h0,Function.update_of_ne h1,Function.update_of_ne h2]
/-- Actual framing preserves its cached source and allocates only its physical buffer. -/
theorem frame_call (scope:Bool) (data:Stack→List Bool)
    (hb:data (aux .frameBuffer)=[]) (hs:data (aux .frameScratch)=[]) :
    Runs program (6*(data (frameSource scope)).length+5) (.local (.frame scope)) data
      (.local (.reverse scope))
      (Function.update data (aux .frameBuffer) (frame (data (frameSource scope)) [])) := by
  apply included_call program (frameStack scope) (Label.frame scope) (frame_injective scope)
    SemiprimeD1StackFrame.code 0 (fun _=>rfl) (.local (.frame scope)) (.local (.reverse scope)) rfl
    (6*(data (frameSource scope)).length+4)
    (SemiprimeD1StackFrame.state 0 none (data (frameSource scope)) [] [])
    (SemiprimeD1StackFrame.done (data (frameSource scope)) (frame (data (frameSource scope)) []))
  · rfl
  · rfl
  · exact SemiprimeD1StackFrame.frame_words _ [] none
  · constructor
    · intro k;fin_cases k <;> simp [frameStack,SemiprimeD1StackFrame.state,SemiprimeD1StackFrame.payload,hb,hs]
    · intro k _;rfl
  · have h0:frameSource scope≠(.inr (.inr Aux.frameBuffer):Stack):=by cases scope <;> decide
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
    (hc:program pc=.call (Label.reverse finish 0) next) :
    Runs program (2*(data (reverseInput finish)).length+3) pc data next
      (Function.update (Function.update data (reverseInput finish) []) (reverseOutput finish)
        ((data (reverseInput finish)).reverse++data (reverseOutput finish))) := by
  apply included_call program (reverseStack finish) (Label.reverse finish) (reverse_injective finish)
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

/-- Actual source-preserving copy of the acquired complete scoped-port stream. -/
theorem copy_call (data:Stack→List Bool) (hs:data (aux .copyScratch)=[]) :
    Runs program (5*(data sourceOutput).length+4) (.local .copy) data (.local .loop)
      (Function.update data (aux .reader) (data sourceOutput++data (aux .reader))) := by
  apply included_call program copyStack Label.copy copy_injective SemiprimeD1StackCopy.code 0
    (fun _=>rfl) (.local .copy) (.local .loop) rfl (5*(data sourceOutput).length+3)
    (SemiprimeD1StackCopy.state 0 none (data sourceOutput) (data (aux .reader)) [])
    (SemiprimeD1StackCopy.done (data sourceOutput) (data sourceOutput++data (aux .reader)))
  · rfl
  · rfl
  · exact SemiprimeD1StackCopy.copy_words _ _ none
  · constructor
    · intro k;fin_cases k <;> simp [copyStack,SemiprimeD1StackCopy.state,SemiprimeD1StackCopy.payload,hs]
    · intro k _;rfl
  · have hs' : data (.inr (.inr Aux.copyScratch))=[]:=hs
    constructor
    · intro k
      fin_cases k <;> simp [copyStack,SemiprimeD1StackCopy.done,SemiprimeD1StackCopy.payload,
        Function.update,sourceOutput,sourceStack,aux,hs']
    · intro k hk
      have hn:k≠aux .reader:=by intro h;exact hk 1 h.symm
      exact Function.update_of_ne hn _ _
end RiemannGaussian.SemiprimeD1StackFactorScopePairPrimitives
