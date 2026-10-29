/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackNormalizedInverseReadFields
/-! # Actual cache drains, unread-tail disposal and literal missing-entry ZERO -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackNormalizedInverseReadSteps
open SemiprimeD1StackNormalizedInverse SemiprimeD1StackNormalizedInverseView
open SemiprimeD1StackNormalizedInverseReadBuffers SemiprimeD1StackNormalizedInversePrimitives
open SemiprimeD1StackProcedureTrace
/-- A skipped coefficient is physically drained in full before the next array row. -/
theorem skip_run (part : ReadSite) (w : Words) (word : SemiprimeRationalBits.RationalWord)
    (reader todo : List Bool) (hn : w.registers (readReg part,false)=[])
    (hd : w.registers (readReg part,true)=[]) :
    Runs program ((signed word).length+word.denominator.length+2)
      (.read part .clearSigned) (store (buffers (putReg w (readReg part) word) reader todo))
      (.read part .count) (store (buffers w reader todo)) := by
  let start:=buffers (putReg w (readReg part) word) reader todo
  let middle : Words := {start with registers:=Function.update start.registers (readReg part,false) []}
  have h0:=drain_loop (.read part .clearSigned) (.read part .clearDen) (reg (readReg part) false)
    rfl (store start) (signed word) (putReg_fields w (readReg part) word).1
  rw [update_register] at h0
  have h1:=drain_loop (.read part .clearDen) (.read part .count) (reg (readReg part) true)
    rfl (store middle) word.denominator (by
      change Function.update (putReg w (readReg part) word).registers (readReg part,false) [] (readReg part,true)=word.denominator
      simp only [Function.update_apply,Prod.mk.injEq,eq_self,true_and,Bool.true_eq_false,ite_false]
      exact (putReg_fields w (readReg part) word).2)
  have he:Function.update (store middle) (reg (readReg part) true) []=store (buffers w reader todo) := by
    rw [update_register]
    change store (emptyReg (buffers (putReg w (readReg part) word) reader todo) (readReg part))=_
    rw [empty_buffers,erase_put w (readReg part) word hn hd]
  rw [he] at h1
  have h:=join h0 h1
  convert h using 1; omega
/-- Once a field is selected, the actual entire unread array and copied counter are drained. -/
theorem selected_run (part : ReadSite) (w : Words) (reader todo : List Bool)
    (hv : w.auxiliary .valid=[]) :
    Runs program (reader.length+todo.length+3) (.read part .drainReader)
      (store (buffers w reader todo)) (.read part .return)
      (store (success (buffers w [] []))) := by
  have h0:=drain_loop (.read part .drainReader) (.read part .drainTodo) (aux .reader)
    rfl (store (buffers w reader todo)) reader rfl
  rw [update_reader] at h0
  have h1:=drain_loop (.read part .drainTodo) (.read part .success) (aux .readTodo)
    rfl (store (buffers w [] todo)) todo rfl
  rw [update_todo] at h1
  have h2:=push_run (.read part .success) (.read part .return) (aux .valid) true
    (store (buffers w [] [])) rfl
  change Runs program 1 _ _ _ (Function.update (store (buffers w [] [])) (aux .valid)
    (true::(buffers w [] []).auxiliary .valid)) at h2
  rw [update_success (buffers w [] []) hv] at h2
  have h:=join (join h0 h1) h2
  convert h using 1; omega
/-- Missing input produces the literal unfitted ZERO, including when the W template is empty. -/
theorem missing_run (part : ReadSite) (w : Words) (reader todo : List Bool)
    (hn : w.registers (readReg part,false)=[]) (hd : w.registers (readReg part,true)=[])
    (hv : w.auxiliary .valid=[]) :
    Runs program (reader.length+todo.length+5) (.read part .missingReader)
      (store (buffers w reader todo)) (.read part .return)
      (store (success (buffers (putReg w (readReg part) SemiprimeRationalBits.zeroWord) [] []))) := by
  have h0:=drain_loop (.read part .missingReader) (.read part .missingTodo) (aux .reader)
    rfl (store (buffers w reader todo)) reader rfl
  rw [update_reader] at h0
  have h1:=drain_loop (.read part .missingTodo) (.read part .zeroSigned) (aux .readTodo)
    rfl (store (buffers w [] todo)) todo rfl
  rw [update_todo] at h1
  let clean:=buffers w [] []
  let first : Words := {clean with registers:=Function.update clean.registers (readReg part,false) [false]}
  have h2:=push_run (.read part .zeroSigned) (.read part .zeroDen) (reg (readReg part) false) false
    (store clean) rfl
  change Runs program 1 _ _ _ (Function.update (store clean) (reg (readReg part) false) (false::w.registers (readReg part,false))) at h2
  rw [hn,update_register] at h2
  have h3:=push_run (.read part .zeroDen) (.read part .success) (reg (readReg part) true) true
    (store first) rfl
  have hf:store first (reg (readReg part) true)=[] := by
    change Function.update w.registers (readReg part,false) [false] (readReg part,true)=[]
    simpa only [Function.update_apply,Prod.mk.injEq,eq_self,true_and,Bool.true_eq_false,ite_false] using hd
  rw [hf,update_register] at h3
  have he:({first with registers:=Function.update first.registers (readReg part,true) [true]}:Words)=
      buffers (putReg w (readReg part) SemiprimeRationalBits.zeroWord) [] [] := rfl
  rw [he] at h3
  have h4:=push_run (.read part .success) (.read part .return) (aux .valid) true
    (store (buffers (putReg w (readReg part) SemiprimeRationalBits.zeroWord) [] [])) rfl
  change Runs program 1 _ _ _ (Function.update
    (store (buffers (putReg w (readReg part) SemiprimeRationalBits.zeroWord) [] [])) (aux .valid)
    (true::(buffers (putReg w (readReg part) SemiprimeRationalBits.zeroWord) [] []).auxiliary .valid)) at h4
  rw [update_success (buffers (putReg w (readReg part) SemiprimeRationalBits.zeroWord) [] []) hv] at h4
  have h:=join (join (join (join h0 h1) h2) h3) h4
  convert h using 1; omega
end RiemannGaussian.SemiprimeD1StackNormalizedInverseReadSteps
