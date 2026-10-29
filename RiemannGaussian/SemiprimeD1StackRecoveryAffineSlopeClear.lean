/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackRecoveryAffineSlopeParse
/-! # Actual completed backward-slope scalar-cache drains -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackRecoveryAffineSlopeClear
open SemiprimeD1StackRecoveryAffine SemiprimeD1StackRecoveryAffineView
open SemiprimeD1StackRecoveryAffineSlopeBuffers SemiprimeD1StackProcedureTrace
open SemiprimeSourceHistogramKeyBits (frame)
namespace T
export SemiprimeD1StackRecoveryAffinePrimitives (join drain_loop)
end T
/-- The two real signed/denominator drains restore the EMPTY physical scalar cache. -/
theorem clear_run (w:Words) (x:SemiprimeRationalBits.RationalWord) (reader reversed:List Bool)
    (hn:w.registers (.slope,false)=[]) (hd:w.registers (.slope,true)=[]):
    Runs program ((signed x).length+1+x.denominator.length+1)
      (.local (.clearSlope true false)) (bank (putReg (buffers w reader reversed) .slope x))
      (.local .slopeLoop) (bank (buffers w reader reversed)):=by
  let start:=putReg (buffers w reader reversed) .slope x
  let first:Words:={start with registers:=Function.update start.registers (.slope,false) []}
  have h0:=T.drain_loop (.local (.clearSlope true false)) (.local (.clearSlope true true)) (reg .slope false) rfl
    (bank start) (signed x) (putReg_fields (buffers w reader reversed) .slope x).1
  rw [update_register] at h0
  change Runs program _ _ _ _ (bank first) at h0
  have hx:first.registers (.slope,true)=x.denominator:=by
    change Function.update start.registers (.slope,false) [] (.slope,true)=_
    simp only [Function.update_of_ne (show ((.slope,true):SemiprimeD1StackRecoveryGrid.Reg×Bool)≠(.slope,false) from by decide)]
    exact (putReg_fields (buffers w reader reversed) .slope x).2
  have h1:=T.drain_loop (.local (.clearSlope true true)) (.local .slopeLoop) (reg .slope true) rfl
    (bank first) x.denominator hx
  rw [update_register] at h1
  have he:{first with registers:=Function.update first.registers (.slope,true) []}=buffers w reader reversed:=by
    exact erase_put (buffers w reader reversed) x hn hd
  rw [he] at h1
  simpa only [Nat.add_assoc] using T.join h0 h1
end RiemannGaussian.SemiprimeD1StackRecoveryAffineSlopeClear
