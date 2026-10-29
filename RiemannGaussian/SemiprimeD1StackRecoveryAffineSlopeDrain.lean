/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackRecoveryAffineView
import RiemannGaussian.SemiprimeD1StackRecoveryAffineOperationOutput
import RiemannGaussian.SemiprimeD1StackRecoveryAffinePrimitives
/-! # Actual two-frame row prepending and both scalar-cache drains -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackRecoveryAffineSlopeDrain
open SemiprimeD1StackRecoveryAffine SemiprimeD1StackRecoveryAffineView
open SemiprimeD1StackProcedureTrace
open SemiprimeSourceHistogramKeyBits (frame)
namespace T
export SemiprimeD1StackRecoveryAffinePrimitives (join drain_loop)
end T
/-- Both actual current-slope fields, including their EOF branches, are physically drained. -/
theorem source_run (w:Words):
    Runs program ((w.registers (.slope,false)).length+1+(w.registers (.slope,true)).length+1)
      (.local (.clearSlope true false)) (bank w) (.local .slopeLoop)
      (bank (SemiprimeD1StackRecoveryAffineOperationOutput.emptyReg w .slope)):=by
  let first:Words:={w with registers:=Function.update w.registers (.slope,false) []}
  have h0:=T.drain_loop (.local (.clearSlope true false)) (.local (.clearSlope true true)) (reg .slope false) rfl
    (bank w) (w.registers (.slope,false)) rfl
  rw [update_register] at h0
  change Runs program _ _ _ _ (bank first) at h0
  have hx:first.registers (.slope,true)=w.registers (.slope,true):=by
    change Function.update w.registers (.slope,false) [] (.slope,true)=w.registers (.slope,true)
    exact Function.update_of_ne (by decide) _ _
  have h1:=T.drain_loop (.local (.clearSlope true true)) (.local .slopeLoop) (reg .slope true) rfl
    (bank first) (w.registers (.slope,true)) hx
  rw [update_register] at h1
  simpa only [Nat.add_assoc,first,SemiprimeD1StackRecoveryAffineOperationOutput.emptyReg] using T.join h0 h1
end RiemannGaussian.SemiprimeD1StackRecoveryAffineSlopeDrain
