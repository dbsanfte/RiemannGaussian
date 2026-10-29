/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackRecoveryWeightsCalls
/-! # Both literal ZERO fields are physically seeded before the complete pair loop -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackRecoveryWeightsSeed
open SemiprimeD1StackRecoveryWeights SemiprimeD1StackRecoveryWeightsView
open SemiprimeD1StackRecoveryWeightsCalls SemiprimeD1StackProcedureTrace
/-- The unfitted native ZERO is acquired by two actual pushes, including W0. -/
theorem seed_run (w:Words) (hn:w.registers (.acc,false)=[]) (hd:w.registers (.acc,true)=[]):
    Runs program 2 (.local (.seedZero false)) (bank w) (.local .copyTerms)
      (bank (putReg w .acc SemiprimeRationalBits.zeroWord)):=by
  have h0:=P.push_run (.local (.seedZero false)) (.local (.seedZero true)) (reg .acc false) false (bank w) rfl
  change Runs program 1 _ _ _ (Function.update (bank w) (reg .acc false) (false::w.registers (.acc,false))) at h0
  rw [hn,update_register] at h0
  let first:Words:={w with registers:=Function.update w.registers (.acc,false) [false]}
  have h1:=P.push_run (.local (.seedZero true)) (.local .copyTerms) (reg .acc true) true (bank first) rfl
  change Runs program 1 _ _ _ (Function.update (bank first) (reg .acc true) (true::first.registers (.acc,true))) at h1
  have hd':first.registers (.acc,true)=[]:=by simpa only [first,Function.update_of_ne (show ((.acc:I.Reg),true)≠(.acc,false) by decide)] using hd
  rw [hd',update_register] at h1
  exact P.join h0 h1
end RiemannGaussian.SemiprimeD1StackRecoveryWeightsSeed
