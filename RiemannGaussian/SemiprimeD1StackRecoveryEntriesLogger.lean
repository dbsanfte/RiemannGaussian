/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackRecoveryEntriesPrimitives
/-! # Four real Frames and physically reversed entry logging
All raw source sign/magnitude/denominator and selected child bytes are retained.
Per-row work does not rescan old history; one final real reverse restores order.
-/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 65536
namespace RiemannGaussian.SemiprimeD1StackRecoveryEntriesLogger
open SemiprimeD1StackRecoveryEntries SemiprimeD1StackRecoveryEntriesState
open SemiprimeD1StackRecoveryEntriesPrimitives SemiprimeD1StackProcedureTrace
open SemiprimeD1StackRecoveryDenominatorEncoding (Row)
open SemiprimeD1StackRecoveryEntriesEncoding (Entry)
open SemiprimeSourceHistogramKeyBits (frame)
/-- Actual source Aux role at each fixed preserving-frame site. -/
def frameAux (part:Fin 4):Aux:=if part=0 then .child else if part=1 then .denominator else if part=2 then .magnitude else .sign
/-- Every source-frame role is the declared physical byte word. -/
theorem frame_address (part:Fin 4):frameSource part=aux (frameAux part):=by fin_cases part <;> rfl
/-- Every real preserving frame includes all byte traversals, delimiter and real call/return. -/
theorem frame_call (part:Fin 4) (children:List Bool) (w:Aux → List Bool):
    Runs program (6*(w (frameAux part)).length+5) (.local (.frame part)) (data children w) (nextFrame part)
      (data children (Function.update w .frameBuffer (frame (w (frameAux part)) (w .frameBuffer)))):=by
  rw [data_update]
  let before:=SemiprimeD1StackFrame.state 0 none (w (frameAux part)) (w .frameBuffer) []
  let after:=SemiprimeD1StackFrame.done (w (frameAux part)) (frame (w (frameAux part)) (w .frameBuffer))
  have hin:SemiprimeD1StackMultiplierLink.DataRel (frameStack part) (data children w) before.store (data children w):=by
    constructor
    · intro k;fin_cases k
      · change data children w (frameSource part)=w (frameAux part)
        rw [frame_address,data_aux]
      · rfl
      · exact data_scratch children w
    · intro k _;rfl
  have ho:=SemiprimeD1StackMultiplierLink.data_update (frameStack part) (frame_injective part)
    (data children w) before.store (data children w) hin (1:Fin 3) (frame (w (frameAux part)) (w .frameBuffer))
  have he:Function.update before.store 1 (frame (w (frameAux part)) (w .frameBuffer))=after.store:=by funext k;fin_cases k <;> rfl
  rw [he] at ho
  exact included_call program (frameStack part) (Label.frame part) (frame_injective part) SemiprimeD1StackFrame.code 0
    (fun _=>rfl) (.local (.frame part)) (nextFrame part) rfl (6*(w (frameAux part)).length+4)
    before after _ _ rfl rfl (SemiprimeD1StackFrame.frame_words _ _ none) hin ho
/-- Actual input role of each of the two fixed real reversals. -/
def reverseFrom (finish:Bool):Aux:=if finish then .history else .frameBuffer
/-- Actual output role of each fixed real reversal. -/
def reverseTo (finish:Bool):Aux:=if finish then .output else .history
/-- Every reversal source equals its physical role. -/
theorem reverse_source (finish:Bool):reverseStack finish 0=aux (reverseFrom finish):=by cases finish <;> rfl
/-- Every reversal target equals its physical role. -/
theorem reverse_target (finish:Bool):reverseStack finish 1=aux (reverseTo finish):=by cases finish <;> rfl
/-- Both actual reversal operands are distinct. -/
theorem reverse_ne (finish:Bool):aux (reverseFrom finish)≠aux (reverseTo finish):=by cases finish <;> decide
/-- Real reversal consumes its entire source and pays every push plus call/return. -/
theorem reverse_call (finish:Bool) (pc next:Label) (children:List Bool) (w:Aux → List Bool)
    (hp:program pc=.call (.reverse finish 0) next):
    Runs program (2*(w (reverseFrom finish)).length+3) pc (data children w) next
      (data children (Function.update (Function.update w (reverseFrom finish) []) (reverseTo finish)
        ((w (reverseFrom finish)).reverse++w (reverseTo finish)))):=by
  simp only [data_update]
  let before:=SemiprimeD1StackReverseWord.state none (w (reverseFrom finish)) (w (reverseTo finish))
  let after:=SemiprimeD1StackReverseWord.done ((w (reverseFrom finish)).reverse++w (reverseTo finish))
  have hin:SemiprimeD1StackMultiplierLink.DataRel (reverseStack finish) (data children w) before.store (data children w):=by
    constructor
    · intro k;fin_cases k
      · change data children w (reverseStack finish 0)=_;rw [reverse_source,data_aux];rfl
      · change data children w (reverseStack finish 1)=_;rw [reverse_target,data_aux];rfl
    · intro k _;rfl
  have h0:=SemiprimeD1StackMultiplierLink.data_update (reverseStack finish) (reverse_injective finish)
    (data children w) before.store (data children w) hin (0:Fin 2) []
  have h1:=SemiprimeD1StackMultiplierLink.data_update (reverseStack finish) (reverse_injective finish)
    (data children w) _ _ h0 (1:Fin 2) ((w (reverseFrom finish)).reverse++w (reverseTo finish))
  have he:Function.update (Function.update before.store 0 []) 1 ((w (reverseFrom finish)).reverse++w (reverseTo finish))=after.store:=by
    funext k;fin_cases k <;> rfl
  rw [he,reverse_source,reverse_target] at h1
  exact included_call program (reverseStack finish) (Label.reverse finish) (reverse_injective finish) SemiprimeD1StackReverseWord.code 0
    (fun _=>rfl) pc next hp (2*(w (reverseFrom finish)).length+2) before after _ _ rfl rfl
    (SemiprimeD1StackReverseWord.reverse_run _ _ none) hin h1
/-- Actual four payloads logged from this parsed row and physically selected child word. -/
def payload (r:Row) (child:List Bool):Entry:=![r 2,r 3,r 4,child]
/-- Complete literal one-entry chunk before the actual per-row reverse. -/
def chunk (r:Row) (child:List Bool):List Bool:=true::SemiprimeD1StackRecoveryEntriesEncoding.fields (payload r child) []
/-- Exact actual four-frame caller clock, independent of prior history/output length. -/
def frameTime (r:Row) (child:List Bool):Nat:=6*(child.length+(r 4).length+(r 3).length+(r 2).length)+20
/-- All four acquired words are physically framed in their exact original sign/magnitude/D/child order. -/
theorem frame_run (children original reader:List Bool) (r:Row) (row child history buffer out:List Bool):
    Runs program (frameTime r child) (.local (.frame 0))
      (data children (words original reader r row child [] history buffer out)) (.local .tag)
      (data children (words original reader r row child [] history (SemiprimeD1StackRecoveryEntriesEncoding.fields (payload r child) buffer) out)):=by
  have h0:=frame_call 0 children (words original reader r row child [] history buffer out)
  change Runs program (6*child.length+5) (.local (.frame 0))
    (data children (words original reader r row child [] history buffer out)) (.local (.frame 1))
    (data children (Function.update (words original reader r row child [] history buffer out) .frameBuffer (frame child buffer))) at h0
  rw [update_buffer] at h0
  have h1:=frame_call 1 children (words original reader r row child [] history (frame child buffer) out)
  rw [update_buffer] at h1
  change Runs program (6*(r 4).length+5) _ _ _ _ at h1
  have h2:=frame_call 2 children (words original reader r row child [] history (frame (r 4) (frame child buffer)) out)
  rw [update_buffer] at h2
  change Runs program (6*(r 3).length+5) _ _ _ _ at h2
  have h3:=frame_call 3 children (words original reader r row child [] history (frame (r 3) (frame (r 4) (frame child buffer))) out)
  rw [update_buffer] at h3
  change Runs program (6*(r 2).length+5) _ _ _ _ at h3
  have h:=join (join (join h0 h1) h2) h3
  change Runs program _ (.local (.frame 0)) _ (.local .tag) _ at h
  convert h using 1 <;> first | rfl | (unfold frameTime;omega)
/-- Exact physical row logger clock, including true marker and genuine buffer-to-history reversal. -/
def rowTime (r:Row) (child:List Bool):Nat:=frameTime r child+1+(2*(chunk r child).length+3)
/-- One actual entry is logged without rescanning prior history; its source words remain until explicit cleanup. -/
theorem row_run (children original reader:List Bool) (r:Row) (row child history out:List Bool):
    Runs program (rowTime r child) (.local (.frame 0))
      (data children (words original reader r row child [] history [] out)) (.local (.clear 0))
      (data children (words original reader r row child [] ((chunk r child).reverse++history) [] out)):=by
  have h0:=frame_run children original reader r row child history [] out
  have h1:=push_run (.local .tag) (.local .rowReverse) .frameBuffer true children
    (words original reader r row child [] history (SemiprimeD1StackRecoveryEntriesEncoding.fields (payload r child) []) out) rfl
  rw [update_buffer] at h1
  have h2:=reverse_call false (.local .rowReverse) (.local (.clear 0)) children
    (words original reader r row child [] history (chunk r child) out) rfl
  change Runs program (2*(chunk r child).length+3) (.local .rowReverse)
    (data children (words original reader r row child [] history (chunk r child) out)) (.local (.clear 0))
    (data children (Function.update (Function.update (words original reader r row child [] history (chunk r child) out) .frameBuffer []) .history
      ((chunk r child).reverse++history))) at h2
  rw [update_buffer,update_history] at h2
  exact join (join h0 h1) h2
end RiemannGaussian.SemiprimeD1StackRecoveryEntriesLogger
