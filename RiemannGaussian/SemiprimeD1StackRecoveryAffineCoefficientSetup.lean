/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackRecoveryAffineCache
import RiemannGaussian.SemiprimeD1StackRecoveryAffinePrimitives
/-! # Paid physical coefficient-index copy and literal dot-ZERO seed -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackRecoveryAffineCoefficientSetup
open SemiprimeD1StackRecoveryAffine SemiprimeD1StackRecoveryAffineView SemiprimeD1StackProcedureTrace
open SemiprimeD1StackRecoveryAffineCache (counter)
open SemiprimeD1StackRecoveryAffineReadCount (unary)
namespace T
export SemiprimeD1StackRecoveryAffinePrimitives (join copy_call push_run)
end T
/-- This actual stage copies the remaining byte index then pushes denominatorONE/signFALSE. -/
theorem source_run (w:Words) (n:Nat) (hr:w.added .remaining=unary n) (hk:w.added .k=[])
    (hc:w.auxiliary .copyScratch=[]) (hn:w.registers (.denPower,false)=[]) (hd:w.registers (.denPower,true)=[]):
    Runs program (5*n+6) (.local .index) (bank w) (.local (.inner .unit))
      (bank (putReg (counter w n) .denPower SemiprimeRationalBits.zeroWord)):=by
  let base:=counter w n
  let first:Words:={base with registers:=Function.update base.registers (.denPower,true) [true]}
  have h0:=T.copy_call .index (.local .index) (.local .zeroDen) rfl (bank w) (unary n) [] hr hk hc
  change Runs program _ _ _ _ (Function.update (bank w) (aux .k) (unary n++[])) at h0
  rw [List.append_nil,update_added] at h0
  change Runs program _ _ _ _ (bank base) at h0
  have h1:=T.push_run (.local .zeroDen) (.local .zeroSign) (reg .denPower true) true (bank base) rfl
  change Runs program _ _ _ _ (Function.update (bank base) (reg .denPower true) (true::w.registers (.denPower,true))) at h1
  rw [hd,update_register] at h1
  change Runs program _ _ _ _ (bank first) at h1
  have hx:first.registers (.denPower,false)=[]:=by simp [first,base,counter,hn]
  have h2:=T.push_run (.local .zeroSign) (.local (.inner .unit)) (reg .denPower false) false (bank first) rfl
  change Runs program _ _ _ _ (Function.update (bank first) (reg .denPower false) (false::first.registers (.denPower,false))) at h2
  rw [hx,update_register] at h2
  have he:{first with registers:=Function.update first.registers (.denPower,false) [false]}=
      putReg base .denPower SemiprimeRationalBits.zeroWord:=by
    dsimp only [first,putReg]
    congr 1
    congr 1
    funext slot
    rcases slot with ⟨r,b⟩
    cases r <;> cases b <;> simp [signed,SemiprimeRationalBits.zeroWord]
  rw [he] at h2
  have h:=T.join (T.join h0 h1) h2
  convert h using 1
  simp only [unary,List.length_replicate]
end RiemannGaussian.SemiprimeD1StackRecoveryAffineCoefficientSetup
