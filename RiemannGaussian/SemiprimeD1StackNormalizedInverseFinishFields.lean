/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackNormalizedInversePrimitives
import RiemannGaussian.SemiprimeD1StackNormalizedInverseFinishBuffers
/-! # Two real signed/denominator field parses, with both actual validity pops -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackNormalizedInverseFinishFields
open SemiprimeD1StackNormalizedInverse SemiprimeD1StackNormalizedInverseView
open SemiprimeD1StackNormalizedInverseFinishBuffers SemiprimeD1StackNormalizedInversePrimitives
open SemiprimeD1StackProcedureTrace
open SemiprimeSourceHistogramKeyBits (frame)
/-- Both actual field parsers consume their real TRUE flags, retaining every other physical word. -/
theorem fields_run (w : Words)
    (word : SemiprimeRationalBits.RationalWord) (tail todo : List Bool)
    (hn : w.registers (.left,false)=[]) (hd : w.registers (.left,true)=[])
    (hs : w.auxiliary .fieldFrameScratch=[]) (hv : w.auxiliary .valid=[]) :
    Runs program (8*((signed word).length+word.denominator.length)+16)
      (ctl (.finalField false))
      (store (finishBuffers w (frame (signed word) (frame word.denominator tail)) todo))
      (ctl (.finalFrame true)) (store (finishBuffers (putReg w (.left) word) tail todo)) := by
  let first:=finishBuffers w (frame (signed word) (frame word.denominator tail)) todo
  let middle : Words := finishBuffers {w with registers:=Function.update w.registers (.left,false) (signed word)}
    (frame word.denominator tail) todo
  have h0:=field_read (.finish false) (ctl (.finalField false))
    (ctl (.finalValid false)) (ctl (.finalField true)) (ctl (.abort 0))
    rfl rfl (store first) (signed word) (frame word.denominator tail) rfl hs hn hv
  have he0 : Function.update (Function.update (store first) (fieldInput (.finish false))
      (frame word.denominator tail)) (fieldOutput (.finish false)) (signed word)=store middle := by
    rw [show fieldInput (.finish false)=aux .prefixReverse from rfl,
      show fieldOutput (.finish false)=reg (.left) false from rfl,
      update_prefix,update_register]
    rfl
  rw [he0] at h0
  have h1:=field_read (.finish true) (ctl (.finalField true))
    (ctl (.finalValid true)) (ctl (.finalFrame true)) (ctl (.abort 0))
    rfl rfl (store middle) word.denominator tail rfl hs
    (by
      change Function.update w.registers (.left,false) (signed word) (.left,true)=[]
      simpa only [Function.update_apply,Prod.mk.injEq,eq_self,true_and,Bool.true_eq_false,ite_false] using hd) hv
  have he1 : Function.update (Function.update (store middle) (fieldInput (.finish true)) tail)
      (fieldOutput (.finish true)) word.denominator=
      store (finishBuffers (putReg w (.left) word) tail todo) := by
    rw [show fieldInput (.finish true)=aux .prefixReverse from rfl,
      show fieldOutput (.finish true)=reg (.left) true from rfl,
      update_prefix,update_register]
    rfl
  rw [he1] at h1
  have h:=join h0 h1
  convert h using 1; omega
end RiemannGaussian.SemiprimeD1StackNormalizedInverseFinishFields
