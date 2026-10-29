/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackNormalizedInverseIndices
/-! # Three actual copies of the acquired prefix count, predecessor and literal ZERO seed -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackNormalizedInversePrepare
open SemiprimeD1StackNormalizedInverse SemiprimeD1StackNormalizedInverseView
open SemiprimeD1StackNormalizedInverseReadBuffers SemiprimeD1StackNormalizedInversePrimitives
open SemiprimeD1StackNormalizedInverseIndices SemiprimeD1StackProcedureTrace
/-- All three marker counters are copied from the actual retained built-prefix count, before any operand read. -/
theorem counters_run (w : Words) (n : ℕ) (hb : w.auxiliary .built=unary n)
    (ht : w.auxiliary .terms=[]) (ha : w.auxiliary .aIndex=[]) (hbi : w.auxiliary .bIndex=[])
    (hs : w.auxiliary .copyScratch=[]) :
    Runs program (15*n+12) (ctl .copyTerms) (store w) (ctl .predecessor)
      (store (counters w n n n)) := by
  let w1 : Words := {w with auxiliary:=Function.update w.auxiliary .terms (unary n)}
  let w2 : Words := {w1 with auxiliary:=Function.update w1.auxiliary .aIndex (unary n)}
  have h0:=copy_call .terms (ctl .copyTerms) (ctl .copyAIndex) rfl (store w) (unary n) [] hb ht hs
  change Runs program _ _ _ _ (Function.update (store w) (aux .terms) (unary n++[])) at h0
  rw [List.append_nil,update_aux] at h0
  have h1:=copy_call .aIndex (ctl .copyAIndex) (ctl .copyBIndex) rfl (store w1) (unary n) [] hb ha hs
  change Runs program _ _ _ _ (Function.update (store w1) (aux .aIndex) (unary n++[])) at h1
  rw [List.append_nil,update_aux] at h1
  have h2:=copy_call .bIndex (ctl .copyBIndex) (ctl .predecessor) rfl (store w2) (unary n) [] hb hbi hs
  change Runs program _ _ _ _ (Function.update (store w2) (aux .bIndex) (unary n++[])) at h2
  rw [List.append_nil,update_aux] at h2
  have h:=join (join h0 h1) h2
  convert h using 1 <;> first | rfl | (simp only [unary,List.length_replicate];omega)
/-- The acquired positive prefix count is physically reduced once for the reverse-prefix read index. -/
theorem predecessor_run (w : Words) (n : ℕ) (hn : 0<n) :
    Runs program 1 (ctl .predecessor) (store (counters w n n n)) (ctl (.seedZero false))
      (store (counters w n n (n-1))) := by
  cases n with
  | zero=>omega
  | succ n=>
    have h:=pop_run (ctl .predecessor) (ctl (.abort 0)) (ctl (.abort 0)) (ctl (.seedZero false)) (aux .bIndex)
      (store (counters w (n+1) (n+1) (n+1))) (true::unary n) rfl (by
        change Function.update (Function.update (Function.update w.auxiliary .terms (unary (n+1))) .aIndex (unary (n+1))) .bIndex (unary (n+1)) .bIndex=true::unary n
        rw [Function.update_self]
        exact List.replicate_succ)
    simp only [List.head?_cons,List.tail_cons,SemiprimeD1StackBytecode.choose] at h
    rw [update_b] at h
    exact h
/-- The dot accumulator begins with the literal unfitted ZERO, including W=0. -/
theorem zero_run (w : Words) (hn : w.registers (.acc,false)=[]) (hd : w.registers (.acc,true)=[]) :
    Runs program 2 (ctl (.seedZero false)) (store w) (ctl .terms)
      (store (putReg w .acc SemiprimeRationalBits.zeroWord)) := by
  let middle : Words := {w with registers:=Function.update w.registers (.acc,false) [false]}
  have h0:=push_run (ctl (.seedZero false)) (ctl (.seedZero true)) (reg .acc false) false (store w) rfl
  change Runs program 1 _ _ _ (Function.update (store w) (reg .acc false) (false::w.registers (.acc,false))) at h0
  rw [hn,update_register] at h0
  have h1:=push_run (ctl (.seedZero true)) (ctl .terms) (reg .acc true) true (store middle) rfl
  have he:store middle (reg .acc true)=[] := by
    change Function.update w.registers (.acc,false) [false] (.acc,true)=[]
    simpa only [Function.update_apply,Prod.mk.injEq,eq_self,true_and,Bool.true_eq_false,ite_false] using hd
  rw [he,update_register] at h1
  exact join h0 h1
/-- Whole actual preparation has no supplied pair/index/count answer: all three indices derive from the acquired prefix. -/
theorem prepare_run (w : Words) (n : ℕ) (hn : 0<n) (hb : w.auxiliary .built=unary n)
    (ht : w.auxiliary .terms=[]) (ha : w.auxiliary .aIndex=[]) (hbi : w.auxiliary .bIndex=[])
    (hs : w.auxiliary .copyScratch=[]) (hzero : w.registers (.acc,false)=[]) (hden : w.registers (.acc,true)=[]) :
    Runs program (15*n+15) (ctl .copyTerms) (store w) (ctl .terms)
      (store (indexed w n n (n-1) SemiprimeRationalBits.zeroWord)) := by
  have h0:=counters_run w n hb ht ha hbi hs
  have h1:=predecessor_run w n hn
  have h2:=zero_run (counters w n n (n-1)) hzero hden
  have h:=join (join h0 h1) h2
  convert h using 1
  rfl
end RiemannGaussian.SemiprimeD1StackNormalizedInversePrepare
