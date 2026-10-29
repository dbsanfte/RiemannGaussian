/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackNormalizedInverseFinishFields
import RiemannGaussian.SemiprimeD1StackNormalizedInverseReadBuffers
/-! # Actual final two-field row parse, preserving reframe and complete cache drain -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackNormalizedInverseFinishRow
open SemiprimeD1StackNormalizedInverse SemiprimeD1StackNormalizedInverseView
open SemiprimeD1StackNormalizedInversePrimitives SemiprimeD1StackNormalizedInverseFinishBuffers
open SemiprimeD1StackNormalizedInverseFinishFields SemiprimeD1StackProcedureTrace
open SemiprimeSourceHistogramKeyBits (frame)
/-- Actual denominator-then-signed Frames preserve exact raw bytes and prepend the row TRUE tag. -/
theorem frames_run (w : Words) (word : SemiprimeRationalBits.RationalWord) (tail out : List Bool)
    (hs : w.auxiliary .fieldFrameScratch=[]) :
    Runs program (6*((signed word).length+word.denominator.length)+11) (ctl (.finalFrame true))
      (store (finishBuffers (putReg w .left word) tail out)) (ctl (.clearFinalReg false))
      (store (finishBuffers (putReg w .left word) tail (row word out))) := by
  let base:=putReg w .left word
  have h0:=frame_call (.finish true) (ctl (.finalFrame true)) (ctl (.finalFrame false)) rfl
    (store (finishBuffers base tail out)) word.denominator out (putReg_fields w .left word).2 rfl hs
  change Runs program _ _ _ _ (Function.update (store (finishBuffers base tail out)) (aux .output) _) at h0
  rw [update_output] at h0
  have h1:=frame_call (.finish false) (ctl (.finalFrame false)) (ctl .finalRowTag) rfl
    (store (finishBuffers base tail (frame word.denominator out))) (signed word) (frame word.denominator out)
    (putReg_fields w .left word).1 rfl hs
  change Runs program _ _ _ _ (Function.update (store (finishBuffers base tail (frame word.denominator out))) (aux .output) _) at h1
  rw [update_output] at h1
  have h2:=push_run (ctl .finalRowTag) (ctl (.clearFinalReg false)) (aux .output) true
    (store (finishBuffers base tail (frame (signed word) (frame word.denominator out)))) rfl
  change Runs program 1 _ _ _ (Function.update (store (finishBuffers base tail (frame (signed word)
    (frame word.denominator out)))) (aux .output) (true::frame (signed word) (frame word.denominator out))) at h2
  rw [update_output] at h2
  have h:=join (join h0 h1) h2
  convert h using 1 <;> first | rfl | omega
/-- Both real cache drains complete before another final row is read. -/
theorem clear_run (w : Words) (word : SemiprimeRationalBits.RationalWord) (tail out : List Bool)
    (hn : w.registers (.left,false)=[]) (hd : w.registers (.left,true)=[]) :
    Runs program ((signed word).length+word.denominator.length+2) (ctl (.clearFinalReg false))
      (store (finishBuffers (putReg w .left word) tail out)) (ctl .finalTag)
      (store (finishBuffers w tail out)) := by
  let start:=finishBuffers (putReg w .left word) tail out
  let middle : Words := {start with registers:=Function.update start.registers (.left,false) []}
  have h0:=drain_loop (ctl (.clearFinalReg false)) (ctl (.clearFinalReg true)) (reg .left false)
    rfl (store start) (signed word) (putReg_fields w .left word).1
  rw [update_register] at h0
  have h1:=drain_loop (ctl (.clearFinalReg true)) (ctl .finalTag) (reg .left true)
    rfl (store middle) word.denominator (by
      change Function.update (putReg w .left word).registers (.left,false) [] (.left,true)=word.denominator
      simp only [Function.update_apply,Prod.mk.injEq,eq_self,true_and,Bool.true_eq_false,ite_false]
      exact (putReg_fields w .left word).2)
  have he : Function.update (store middle) (reg .left true) []=store (finishBuffers w tail out) := by
    rw [update_register]
    change store (emptyReg (finishBuffers (putReg w .left word) tail out) .left)=_
    rw [empty_finish,SemiprimeD1StackNormalizedInverseReadBuffers.erase_put w .left word hn hd]
  rw [he] at h1
  have h:=join h0 h1
  convert h using 1;omega
/-- A complete physical rational row is parsed, emitted and cleared, preserving every other source/cache field. -/
theorem row_run (w : Words) (word : SemiprimeRationalBits.RationalWord) (tail out : List Bool)
    (hn : w.registers (.left,false)=[]) (hd : w.registers (.left,true)=[])
    (hs : w.auxiliary .fieldFrameScratch=[]) (hv : w.auxiliary .valid=[]) :
    Runs program (15*((signed word).length+word.denominator.length)+30) (ctl .finalTag)
      (store (finishBuffers w (row word tail) out)) (ctl .finalTag) (store (finishBuffers w tail (row word out))) := by
  have h0:=pop_run (ctl .finalTag) (ctl (.abort 0)) (ctl .finalEnd) (ctl (.finalField false)) (aux .prefixReverse)
    (store (finishBuffers w (row word tail) out))
    (true::frame (signed word) (frame word.denominator tail)) rfl rfl
  simp only [List.head?_cons,List.tail_cons,SemiprimeD1StackBytecode.choose] at h0
  rw [update_prefix] at h0
  have h1:=fields_run w word tail out hn hd hs hv
  have h2:=frames_run w word tail out hs
  have h3:=clear_run w word tail (row word out) hn hd
  have h:=join (join (join h0 h1) h2) h3
  convert h using 1;omega
end RiemannGaussian.SemiprimeD1StackNormalizedInverseFinishRow
