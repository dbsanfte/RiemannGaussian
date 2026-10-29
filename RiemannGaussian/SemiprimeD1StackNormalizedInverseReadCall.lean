/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackNormalizedInverseReadLoop
/-! # Complete actual preserving array read with its literal caller, return and marker pop -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackNormalizedInverseReadCall
open SemiprimeD1StackNormalizedInverse SemiprimeD1StackNormalizedInverseView
open SemiprimeD1StackNormalizedInverseReadBuffers SemiprimeD1StackNormalizedInversePrimitives
open SemiprimeD1StackNormalizedInverseReadLoop SemiprimeD1StackNormalizedInverseSpec
open SemiprimeD1StackProcedureTrace
/-- Own exact copies and literal scan cost; no semantic/native execution clock occurs. -/
def helperTime (words : List SemiprimeRationalBits.RationalWord) (n : ℕ) : ℕ :=
  (5*(tape words).length+4)+(5*n+4)+readTime words n
/-- Both paid preserving copies initialize actual reader/index work, then the actual physical scan executes. -/
theorem helper_run (part : ReadSite) (w : Words) (words : List SemiprimeRationalBits.RationalWord) (n : ℕ)
    (ha : store w (readSource part)=tape words) (hi : store w (readIndex part)=unary n)
    (hr : w.auxiliary .reader=[]) (ht : w.auxiliary .readTodo=[])
    (hn : w.registers (readReg part,false)=[]) (hd : w.registers (readReg part,true)=[])
    (hs : w.auxiliary .fieldFrameScratch=[]) (hv : w.auxiliary .valid=[]) (hc : w.auxiliary .copyScratch=[]) :
    Runs program (helperTime words n) (.read part .copyArray) (store w) (.read part .return)
      (store (success (putReg w (readReg part) (readWord words n)))) := by
  have h0:=copy_call (.reader part) (.read part .copyArray) (.read part .copyIndex) rfl
    (store w) (tape words) [] ha hr hc
  change Runs program _ _ _ _ (Function.update (store w) (aux .reader) (tape words++[])) at h0
  rw [List.append_nil,update_aux] at h0
  let first : Words := {w with auxiliary:=Function.update w.auxiliary .reader (tape words)}
  have hfi : store first (readIndex part)=unary n := by cases part <;> exact hi
  have hft : store first (copyStack (.readIndex part) 1)=[] := by
    change Function.update w.auxiliary .reader (tape words) .readTodo=[]
    simpa only [Function.update_of_ne (show Aux.readTodo≠.reader by decide)] using ht
  have h1:=copy_call (.readIndex part) (.read part .copyIndex) (.read part .count) rfl
    (store first) (unary n) [] hfi hft (by exact hc)
  change Runs program _ _ _ _ (Function.update (store first) (aux .readTodo) (unary n++[])) at h1
  rw [List.append_nil,update_aux] at h1
  have he : ({first with auxiliary:=Function.update first.auxiliary .readTodo (unary n)}:Words)=
      buffers w (tape words) (unary n) := by
    dsimp only [first,buffers]
    congr 1
    funext k;cases k <;> simp
  rw [he] at h1
  have h2:=read_loop part w words n hn hd hs hv
  have hb : buffers (putReg w (readReg part) (readWord words n)) [] []=
      putReg w (readReg part) (readWord words n) := by
    have h:=buffers_self (putReg w (readReg part) (readWord words n))
    change buffers _ (w.auxiliary .reader) (w.auxiliary .readTodo)=_ at h
    rw [hr,ht] at h
    exact h
  rw [hb] at h2
  have h:=join (join h0 h1) h2
  simpa only [helperTime,unary,List.length_replicate] using h
/-- A real call plus its real return and actual TRUE pop yields the exact old/default word, all work empty. -/
theorem read_call (part : ReadSite) (pc checked finish failure : Label)
    (hcall : program pc=.call (.read part .copyArray) checked)
    (hpop : program checked=.base (.pop (aux .valid) failure failure finish))
    (w : Words) (words : List SemiprimeRationalBits.RationalWord) (n : ℕ)
    (ha : store w (readSource part)=tape words) (hi : store w (readIndex part)=unary n)
    (hr : w.auxiliary .reader=[]) (ht : w.auxiliary .readTodo=[])
    (hn : w.registers (readReg part,false)=[]) (hd : w.registers (readReg part,true)=[])
    (hs : w.auxiliary .fieldFrameScratch=[]) (hv : w.auxiliary .valid=[]) (hc : w.auxiliary .copyScratch=[]) :
    Runs program (helperTime words n+3) pc (store w) finish
      (store (putReg w (readReg part) (readWord words n))) := by
  let acquired:=putReg w (readReg part) (readWord words n)
  have hh:=helper_run part w words n ha hi hr ht hn hd hs hv hc
  have h0:=local_call pc (.read part .copyArray) (.read part .return) checked hcall rfl
    (helperTime words n) (store w) (store (success acquired)) hh
  have h1:=pop_run checked failure failure finish (aux .valid) (store (success acquired)) [true]
    hpop (by change Function.update w.auxiliary .valid [true] .valid=[true];exact Function.update_self _ _ _)
  simp only [List.head?_cons,List.tail_cons,SemiprimeD1StackBytecode.choose] at h1
  have he:Function.update (store (success acquired)) (aux .valid) []=store acquired := by
    rw [update_aux]
    change store {acquired with auxiliary:=Function.update (Function.update acquired.auxiliary .valid [true]) .valid []}=store acquired
    rw [Function.update_idem,←hv]
    change store {acquired with auxiliary:=Function.update acquired.auxiliary .valid (acquired.auxiliary .valid)}=store acquired
    rw [Function.update_eq_self]
  rw [he] at h1
  have h:=join h0 h1
  convert h using 1
/-- All literal source/index copies, parser calls, EOF drains and returns have a physical linear cap. -/
theorem helperTime_le (words : List SemiprimeRationalBits.RationalWord) (n : ℕ) :
    helperTime words n+3≤40*((tape words).length+n+1) := by
  have h:=readTime_le words n
  have hp:=tape_length_pos words
  unfold helperTime
  omega
end RiemannGaussian.SemiprimeD1StackNormalizedInverseReadCall
