/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackRecoveryGridRegisters
/-! # Literal oneWord power initialization, including W0 and exponent0 -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackRecoveryGridPowerSeed
open SemiprimeD1StackRecoveryGrid SemiprimeD1StackRecoveryGridView SemiprimeD1StackRecoveryGridCalls
open SemiprimeD1StackRecoveryGridOperationOutput SemiprimeD1StackProcedureTrace
/-- Every original accumulator byte is actually drained; the base literal has three actual cells. -/
def seedTime (part:PowerSite) (w:Words) :Nat:=
  (w.registers (powerDestination part,false)).length+1+(w.registers (powerDestination part,true)).length+1+3
/-- The zero-exponent base is literal oneWord, not an advised coefficient or an automatically fitted representation. -/
theorem seed_run (part:PowerSite) (w:Words) :
    Runs program (seedTime part w) (.power part .clearSigned) (bank w) (.power part .loop)
      (bank (putReg w (powerDestination part) SemiprimeJetBits.oneWord)):=by
  let r:=powerDestination part
  let w1:Words:={w with registers:=Function.update w.registers (r,false) []}
  let w2:=emptyReg w r
  let w3:Words:={w2 with registers:=Function.update w2.registers (r,false) [true]}
  let w4:Words:={w3 with registers:=Function.update w3.registers (r,false) [false,true]}
  have h0:=PTrace.drain_loop (.power part .clearSigned) (.power part .clearDen) (reg r false) rfl
    (bank w) (w.registers (r,false)) rfl
  rw [update_registers w (r,false)] at h0
  have hx:w1.registers (r,true)=w.registers (r,true):=by
    change Function.update w.registers (r,false) [] (r,true)=_
    exact Function.update_of_ne (by intro h;have hh:=congrArg Prod.snd h;cases hh) _ _
  have h1:=PTrace.drain_loop (.power part .clearDen) (.power part .oneMagnitude) (reg r true) rfl
    (bank w1) (w.registers (r,true)) hx
  rw [update_registers w1 (r,true)] at h1
  have h2:=PTrace.push_run (.power part .oneMagnitude) (.power part .oneSign) (reg r false) true (bank w2) rfl
  change Runs program 1 _ _ _ (Function.update (bank w2) (reg r false) (true::w2.registers (r,false))) at h2
  rw [(emptyReg_fields w r).1,update_registers w2 (r,false)] at h2
  have h3:=PTrace.push_run (.power part .oneSign) (.power part .oneDen) (reg r false) false (bank w3) rfl
  change Runs program 1 _ _ _ (Function.update (bank w3) (reg r false) (false::w3.registers (r,false))) at h3
  have hread:w3.registers (r,false)=[true]:=Function.update_self _ _ _
  rw [hread,update_registers w3 (r,false)] at h3
  have h4:=PTrace.push_run (.power part .oneDen) (.power part .loop) (reg r true) true (bank w4) rfl
  change Runs program 1 _ _ _ (Function.update (bank w4) (reg r true) (true::w4.registers (r,true))) at h4
  have hden:w4.registers (r,true)=[]:=by
    change Function.update (Function.update w2.registers (r,false) [true]) (r,false) [false,true] (r,true)=[]
    rw [Function.update_idem,Function.update_of_ne (by intro h;have hh:=congrArg Prod.snd h;cases hh)]
    exact (emptyReg_fields w r).2
  rw [hden,update_registers w4 (r,true)] at h4
  have he:{w4 with registers:=Function.update w4.registers (r,true) [true]}=putReg w r SemiprimeJetBits.oneWord:=by
    dsimp only [w4,w3,w2,w1,emptyReg,putReg]
    congr 1
    funext k
    by_cases hk0:k=(r,false)
    · subst k;simp [signed,SemiprimeJetBits.oneWord]
    · by_cases hk1:k=(r,true)
      · subst k;simp [SemiprimeJetBits.oneWord]
      · simp [hk0,hk1]
  have h:=PTrace.join (PTrace.join (PTrace.join (PTrace.join h0 h1) h2) h3) h4
  change Runs program _ _ _ _ (bank _) at h
  rw [he] at h
  convert h using 1
  unfold seedTime
  dsimp only [r]
  omega
end RiemannGaussian.SemiprimeD1StackRecoveryGridPowerSeed
