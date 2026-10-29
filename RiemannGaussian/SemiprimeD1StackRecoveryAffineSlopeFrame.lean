/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackRecoveryAffineSlopeParse
/-! # Actual two-frame row prepending and both scalar-cache drains -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackRecoveryAffineSlopeFrame
open SemiprimeD1StackRecoveryAffine SemiprimeD1StackRecoveryAffineView
open SemiprimeD1StackRecoveryAffineSlopeBuffers SemiprimeD1StackProcedureTrace
open SemiprimeSourceHistogramKeyBits (frame)
namespace T
export SemiprimeD1StackRecoveryAffinePrimitives (join frame_call push_run drain_loop)
end T
/-- Denominator then signed numerator then TRUE tag prepend one exact row without recopying its tail. -/
theorem frame_run (w:Words) (x:SemiprimeRationalBits.RationalWord) (reader reversed:List Bool)
    (hs:w.auxiliary .frameScratch=[]) :
    Runs program ((6*x.denominator.length+5)+(6*(signed x).length+5)+1)
      (.local (.frame (.slope true))) (bank (putReg (buffers w reader reversed) .slope x))
      (.local (.clearSlope false false))
      (bank (putReg (buffers w reader (SemiprimeD1StackRecoveryGridView.slopeRow x reversed)) .slope x)):=by
  let start:=putReg w .slope x
  rw [put_buffers]
  have h0:=T.frame_call (.slope true) (.local (.frame (.slope true))) (.local (.frame (.slope false))) rfl
    (bank (buffers start reader reversed)) x.denominator reversed (putReg_fields w .slope x).2 rfl hs
  change Runs program _ _ _ _ (Function.update (bank (buffers start reader reversed))
    (aux .reverseSlopes) (frame x.denominator reversed)) at h0
  rw [update_reversed] at h0
  have h1:=T.frame_call (.slope false) (.local (.frame (.slope false))) (.local .slopeTag) rfl
    (bank (buffers start reader (frame x.denominator reversed))) (signed x) (frame x.denominator reversed)
    (putReg_fields w .slope x).1 rfl hs
  change Runs program _ _ _ _ (Function.update (bank (buffers start reader (frame x.denominator reversed)))
    (aux .reverseSlopes) (frame (signed x) (frame x.denominator reversed))) at h1
  rw [update_reversed] at h1
  have h2:=T.push_run (.local .slopeTag) (.local (.clearSlope false false)) (aux .reverseSlopes) true
    (bank (buffers start reader (frame (signed x) (frame x.denominator reversed)))) rfl
  change Runs program _ _ _ _ (Function.update (bank (buffers start reader (frame (signed x) (frame x.denominator reversed))))
    (aux .reverseSlopes) (SemiprimeD1StackRecoveryGridView.slopeRow x reversed)) at h2
  rw [update_reversed] at h2
  simpa only [put_buffers,start] using T.join (T.join h0 h1) h2
/-- The two real signed/denominator drains restore the EMPTY physical scalar cache. -/
theorem clear_run (w:Words) (x:SemiprimeRationalBits.RationalWord) (reader reversed:List Bool)
    (hn:w.registers (.slope,false)=[]) (hd:w.registers (.slope,true)=[]):
    Runs program ((signed x).length+1+x.denominator.length+1)
      (.local (.clearSlope false false)) (bank (putReg (buffers w reader reversed) .slope x))
      (.local .reverseLoop) (bank (buffers w reader reversed)):=by
  let start:=putReg (buffers w reader reversed) .slope x
  let first:Words:={start with registers:=Function.update start.registers (.slope,false) []}
  have h0:=T.drain_loop (.local (.clearSlope false false)) (.local (.clearSlope false true)) (reg .slope false) rfl
    (bank start) (signed x) (putReg_fields (buffers w reader reversed) .slope x).1
  rw [update_register] at h0
  change Runs program _ _ _ _ (bank first) at h0
  have hx:first.registers (.slope,true)=x.denominator:=by
    change Function.update start.registers (.slope,false) [] (.slope,true)=_
    simp only [Function.update_of_ne (show ((.slope,true):SemiprimeD1StackRecoveryGrid.Reg×Bool)≠(.slope,false) from by decide)]
    exact (putReg_fields (buffers w reader reversed) .slope x).2
  have h1:=T.drain_loop (.local (.clearSlope false true)) (.local .reverseLoop) (reg .slope true) rfl
    (bank first) x.denominator hx
  rw [update_register] at h1
  have he:{first with registers:=Function.update first.registers (.slope,true) []}=buffers w reader reversed:=by
    exact erase_put (buffers w reader reversed) x hn hd
  rw [he] at h1
  simpa only [Nat.add_assoc] using T.join h0 h1
end RiemannGaussian.SemiprimeD1StackRecoveryAffineSlopeFrame
