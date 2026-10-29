/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackRecoveryAffineReadBuffers
import RiemannGaussian.SemiprimeD1StackRecoveryAffinePrimitives
/-! # Actual skipped coefficient and unread-tail drains -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackRecoveryAffineReadClear
open SemiprimeD1StackRecoveryAffine SemiprimeD1StackRecoveryAffineView
open SemiprimeD1StackRecoveryAffineReadBuffers SemiprimeD1StackProcedureTrace
namespace T
export SemiprimeD1StackRecoveryAffinePrimitives (join drain_loop)
end T
/-- Both skipped signed/denominator words are actually drained before the next byte-index step. -/
theorem skip_run (part:Part) (w:Words) (x:SemiprimeRationalBits.RationalWord) (reader todo:List Bool)
    (hn:w.registers (.numBase,false)=[]) (hd:w.registers (.numBase,true)=[]):
    Runs program ((signed x).length+1+x.denominator.length+1)
      (.local (.clearReadWord part false)) (bank (putReg (buffers w reader todo) .numBase x))
      (.local (.readCount part)) (bank (buffers w reader todo)):=by
  let start:=putReg (buffers w reader todo) .numBase x
  let first:Words:={start with registers:=Function.update start.registers (.numBase,false) []}
  have h0:=T.drain_loop (.local (.clearReadWord part false)) (.local (.clearReadWord part true)) (reg .numBase false) rfl
    (bank start) (signed x) (putReg_fields (buffers w reader todo) .numBase x).1
  rw [update_register] at h0
  change Runs program _ _ _ _ (bank first) at h0
  have hx:first.registers (.numBase,true)=x.denominator:=by
    change Function.update start.registers (.numBase,false) [] (.numBase,true)=_
    simp only [Function.update_of_ne (show ((.numBase,true):SemiprimeD1StackRecoveryGrid.Reg×Bool)≠(.numBase,false) from by decide)]
    exact (putReg_fields (buffers w reader todo) .numBase x).2
  have h1:=T.drain_loop (.local (.clearReadWord part true)) (.local (.readCount part)) (reg .numBase true) rfl
    (bank first) x.denominator hx
  rw [update_register] at h1
  have he:{first with registers:=Function.update first.registers (.numBase,true) []}=buffers w reader todo:=by
    exact erase_put (buffers w reader todo) x hn hd
  rw [he] at h1
  simpa only [Nat.add_assoc] using T.join h0 h1
/-- After a selected physical row, all unread vector bytes are paid and consumed. -/
theorem tail_run (part:Part) (w:Words) (x:SemiprimeRationalBits.RationalWord) (reader todo:List Bool):
    Runs program (reader.length+1) (.local (.clearReadTail part)) (bank (putReg (buffers w reader todo) .numBase x))
      (.local (.factor part)) (bank (putReg (buffers w [] todo) .numBase x)):=by
  rw [put_buffers]
  have h:=T.drain_loop (.local (.clearReadTail part)) (.local (.factor part)) (aux .reader) rfl
    (bank (buffers (putReg w .numBase x) reader todo)) reader rfl
  rw [update_reader] at h
  exact h
end RiemannGaussian.SemiprimeD1StackRecoveryAffineReadClear
