/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackNormalizedInversePrimitives
import RiemannGaussian.SemiprimeD1StackNormalizedInverseReadBuffers
/-! # Two real signed/denominator field parses, with both actual validity pops -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackNormalizedInverseReadFields
open SemiprimeD1StackNormalizedInverse SemiprimeD1StackNormalizedInverseView
open SemiprimeD1StackNormalizedInverseReadBuffers SemiprimeD1StackNormalizedInversePrimitives
open SemiprimeD1StackProcedureTrace
open SemiprimeSourceHistogramKeyBits (frame)
/-- The next instruction is selected only by the static take/skip bit. -/
def next (part : ReadSite) (take : Bool) : Label :=
  .read part (if take then .drainReader else .clearSigned)
/-- Both actual field parsers consume their real TRUE flags, retaining every other physical word. -/
theorem fields_run (part : ReadSite) (take : Bool) (w : Words)
    (word : SemiprimeRationalBits.RationalWord) (tail todo : List Bool)
    (hn : w.registers (readReg part,false)=[]) (hd : w.registers (readReg part,true)=[])
    (hs : w.auxiliary .fieldFrameScratch=[]) (hv : w.auxiliary .valid=[]) :
    Runs program (8*((signed word).length+word.denominator.length)+16)
      (.read part (.field take false))
      (store (buffers w (frame (signed word) (frame word.denominator tail)) todo))
      (next part take) (store (buffers (putReg w (readReg part) word) tail todo)) := by
  let first:=buffers w (frame (signed word) (frame word.denominator tail)) todo
  let middle : Words := buffers {w with registers:=Function.update w.registers (readReg part,false) (signed word)}
    (frame word.denominator tail) todo
  have h0:=field_read (.read part false) (.read part (.field take false))
    (.read part (.valid take false)) (.read part (.field take true)) (.read part .failed)
    rfl rfl (store first) (signed word) (frame word.denominator tail) rfl hs hn hv
  have he0 : Function.update (Function.update (store first) (fieldInput (.read part false))
      (frame word.denominator tail)) (fieldOutput (.read part false)) (signed word)=store middle := by
    rw [show fieldInput (.read part false)=aux .reader from rfl,
      show fieldOutput (.read part false)=reg (readReg part) false from rfl,
      update_reader,update_register]
    rfl
  rw [he0] at h0
  have h1:=field_read (.read part true) (.read part (.field take true))
    (.read part (.valid take true)) (next part take) (.read part .failed)
    rfl (by cases take <;> rfl) (store middle) word.denominator tail rfl hs
    (by
      change Function.update w.registers (readReg part,false) (signed word) (readReg part,true)=[]
      simpa only [Function.update_apply,Prod.mk.injEq,eq_self,true_and,Bool.true_eq_false,ite_false] using hd) hv
  have he1 : Function.update (Function.update (store middle) (fieldInput (.read part true)) tail)
      (fieldOutput (.read part true)) word.denominator=
      store (buffers (putReg w (readReg part) word) tail todo) := by
    rw [show fieldInput (.read part true)=aux .reader from rfl,
      show fieldOutput (.read part true)=reg (readReg part) true from rfl,
      update_reader,update_register]
    rfl
  rw [he1] at h1
  have h:=join h0 h1
  convert h using 1; omega
end RiemannGaussian.SemiprimeD1StackNormalizedInverseReadFields
