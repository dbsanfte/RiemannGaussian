/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackRecoveryAffineReadBuffers
import RiemannGaussian.SemiprimeD1StackRecoveryAffinePrimitives
/-! # Actual EOF-limited zero extension, including q0 and W0 -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackRecoveryAffineReadMissing
open SemiprimeD1StackRecoveryAffine SemiprimeD1StackRecoveryAffineView
open SemiprimeD1StackRecoveryAffineReadBuffers SemiprimeD1StackProcedureTrace
namespace T
export SemiprimeD1StackRecoveryAffinePrimitives (join drain_loop push_run)
end T
/-- After actual vector EOF, remaining byte markers are consumed and literal legacy ZERO is pushed. -/
theorem missing_run (part:Part) (w:Words) (todo:List Bool)
    (hn:w.registers (.numBase,false)=[]) (hd:w.registers (.numBase,true)=[]):
    Runs program (todo.length+4) (.local (.missingReader part)) (bank (buffers w [] todo))
      (.local (.factor part)) (bank (putReg (buffers w [] []) .numBase SemiprimeRationalBits.zeroWord)):=by
  let w0:=buffers w [] []
  let w1:Words:={w0 with registers:=Function.update w0.registers (.numBase,true) [true]}
  have h0:=T.drain_loop (.local (.missingReader part)) (.local (.missingTodo part)) (aux .reader) rfl
    (bank (buffers w [] todo)) [] rfl
  rw [update_reader] at h0
  have h1:=T.drain_loop (.local (.missingTodo part)) (.local (.missingDen part)) (aux .readTodo) rfl
    (bank (buffers w [] todo)) todo rfl
  rw [update_todo] at h1
  have h2:=T.push_run (.local (.missingDen part)) (.local (.missingSign part)) (reg .numBase true) true (bank w0) rfl
  change Runs program _ _ _ _ (Function.update (bank w0) (reg .numBase true) (true::w.registers (.numBase,true))) at h2
  rw [hd,update_register] at h2
  change Runs program _ _ _ _ (bank w1) at h2
  have h3:=T.push_run (.local (.missingSign part)) (.local (.factor part)) (reg .numBase false) false (bank w1) rfl
  have hx:w1.registers (.numBase,false)=[]:=by
    dsimp only [w1,w0,buffers]
    simp [hn]
  change Runs program _ _ _ _ (Function.update (bank w1) (reg .numBase false) (false::w1.registers (.numBase,false))) at h3
  rw [hx,update_register] at h3
  have he:{w1 with registers:=Function.update w1.registers (.numBase,false) [false]}=
      putReg w0 .numBase SemiprimeRationalBits.zeroWord:=by
    dsimp only [w1,putReg]
    congr 1
    congr 1
    funext slot
    rcases slot with ⟨r,b⟩
    cases r <;> cases b <;> simp [signed,SemiprimeRationalBits.zeroWord]
  rw [he] at h3
  have h:=T.join (T.join (T.join h0 h1) h2) h3
  convert h using 1
  simp only [List.length_nil]
  omega
end RiemannGaussian.SemiprimeD1StackRecoveryAffineReadMissing
