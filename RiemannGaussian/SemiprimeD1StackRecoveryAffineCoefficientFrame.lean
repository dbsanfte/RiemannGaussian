/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackRecoveryAffineCoefficientBuffers
import RiemannGaussian.SemiprimeD1StackRecoveryAffinePrimitives
/-! # Actual two-frame row prepending and both scalar-cache drains -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackRecoveryAffineCoefficientFrame
open SemiprimeD1StackRecoveryAffine SemiprimeD1StackRecoveryAffineView
open SemiprimeD1StackRecoveryAffineCoefficientBuffers SemiprimeD1StackProcedureTrace
open SemiprimeSourceHistogramKeyBits (frame)
namespace T
export SemiprimeD1StackRecoveryAffinePrimitives (join frame_call push_run drain_loop)
end T
/-- Denominator then signed numerator then TRUE tag prepend one exact row without recopying its tail. -/
theorem frame_run (w:Words) (x:SemiprimeRationalBits.RationalWord) (remaining next:List Bool)
    (hs:w.auxiliary .frameScratch=[]) :
    Runs program ((6*x.denominator.length+5)+(6*(signed x).length+5)+1)
      (.local (.frame (.coefficient true))) (bank (putReg (buffers w remaining next) .denPower x))
      (.local (.clearSum false))
      (bank (putReg (buffers w remaining (SemiprimeD1StackRecoveryGridView.slopeRow x next)) .denPower x)):=by
  let start:=putReg w .denPower x
  rw [put_buffers]
  have h0:=T.frame_call (.coefficient true) (.local (.frame (.coefficient true))) (.local (.frame (.coefficient false))) rfl
    (bank (buffers start remaining next)) x.denominator next (putReg_fields w .denPower x).2 rfl hs
  change Runs program _ _ _ _ (Function.update (bank (buffers start remaining next))
    (aux .nextArray) (frame x.denominator next)) at h0
  rw [update_next] at h0
  have h1:=T.frame_call (.coefficient false) (.local (.frame (.coefficient false))) (.local .coefficientTag) rfl
    (bank (buffers start remaining (frame x.denominator next))) (signed x) (frame x.denominator next)
    (putReg_fields w .denPower x).1 rfl hs
  change Runs program _ _ _ _ (Function.update (bank (buffers start remaining (frame x.denominator next)))
    (aux .nextArray) (frame (signed x) (frame x.denominator next))) at h1
  rw [update_next] at h1
  have h2:=T.push_run (.local .coefficientTag) (.local (.clearSum false)) (aux .nextArray) true
    (bank (buffers start remaining (frame (signed x) (frame x.denominator next)))) rfl
  change Runs program _ _ _ _ (Function.update (bank (buffers start remaining (frame (signed x) (frame x.denominator next))))
    (aux .nextArray) (SemiprimeD1StackRecoveryGridView.slopeRow x next)) at h2
  rw [update_next] at h2
  simpa only [put_buffers,start] using T.join (T.join h0 h1) h2
/-- The two real signed/denominator drains restore the EMPTY physical scalar cache. -/
theorem clear_run (w:Words) (x:SemiprimeRationalBits.RationalWord) (remaining next:List Bool)
    (hn:w.registers (.denPower,false)=[]) (hd:w.registers (.denPower,true)=[]):
    Runs program ((signed x).length+1+x.denominator.length+1)
      (.local (.clearSum false)) (bank (putReg (buffers w remaining next) .denPower x))
      (.local .coefficientLoop) (bank (buffers w remaining next)):=by
  let start:=putReg (buffers w remaining next) .denPower x
  let first:Words:={start with registers:=Function.update start.registers (.denPower,false) []}
  have h0:=T.drain_loop (.local (.clearSum false)) (.local (.clearSum true)) (reg .denPower false) rfl
    (bank start) (signed x) (putReg_fields (buffers w remaining next) .denPower x).1
  rw [update_register] at h0
  change Runs program _ _ _ _ (bank first) at h0
  have hx:first.registers (.denPower,true)=x.denominator:=by
    change Function.update start.registers (.denPower,false) [] (.denPower,true)=_
    simp only [Function.update_of_ne (show ((.denPower,true):SemiprimeD1StackRecoveryGrid.Reg×Bool)≠(.denPower,false) from by decide)]
    exact (putReg_fields (buffers w remaining next) .denPower x).2
  have h1:=T.drain_loop (.local (.clearSum true)) (.local .coefficientLoop) (reg .denPower true) rfl
    (bank first) x.denominator hx
  rw [update_register] at h1
  have he:{first with registers:=Function.update first.registers (.denPower,true) []}=buffers w remaining next:=by
    exact erase_put (buffers w remaining next) x hn hd
  rw [he] at h1
  simpa only [Nat.add_assoc] using T.join h0 h1
end RiemannGaussian.SemiprimeD1StackRecoveryAffineCoefficientFrame
