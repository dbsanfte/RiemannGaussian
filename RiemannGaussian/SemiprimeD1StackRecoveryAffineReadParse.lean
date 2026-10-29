/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackRecoveryAffineReadBuffers
import RiemannGaussian.SemiprimeD1StackRecoveryAffinePrimitives
/-! # Two real Field calls acquire one physically reached signed array coefficient -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackRecoveryAffineReadParse
open SemiprimeD1StackRecoveryAffine SemiprimeD1StackRecoveryAffineView
open SemiprimeD1StackRecoveryAffineReadBuffers SemiprimeD1StackProcedureTrace
open SemiprimeSourceHistogramKeyBits (frame)
namespace T
export SemiprimeD1StackRecoveryAffinePrimitives (join pop_run field_read)
end T
/-- Each parser really visits both framed fields and clears both validity flags. -/
theorem fields_run (part:Part) (take:Bool) (w:Words) (x:SemiprimeRationalBits.RationalWord) (tail reversed:List Bool)
    (hn:w.registers (.numBase,false)=[]) (hd:w.registers (.numBase,true)=[])
    (hs:w.auxiliary .frameScratch=[]) (hv:w.auxiliary .scan=[]) :
    Runs program (8*(signed x).length+8+(8*x.denominator.length+8))
      (.local (.field (.coefficient part take false)))
      (bank (buffers w (frame (signed x) (frame x.denominator tail)) reversed))
      (afterField (.coefficient part take true)) (bank (putReg (buffers w tail reversed) .numBase x)):=by
  let before:=buffers w (frame (signed x) (frame x.denominator tail)) reversed
  let first:Words:={buffers w (frame x.denominator tail) reversed with registers:=Function.update w.registers (.numBase,false) (signed x)}
  have h0:=T.field_read (.coefficient part take false) (bank before) (signed x) (frame x.denominator tail) rfl hs hn hv
  change Runs program _ _ _ _ (Function.update (Function.update (bank before) (aux .reader) (frame x.denominator tail)) (reg .numBase false) (signed x)) at h0
  rw [update_reader,update_register] at h0
  change Runs program _ _ _ _ (bank first) at h0
  have he:first.registers (.numBase,true)=[]:=by
    change Function.update w.registers (.numBase,false) (signed x) (.numBase,true)=[]
    simp [hd]
  have h1:=T.field_read (.coefficient part take true) (bank first) x.denominator tail rfl hs he hv
  change Runs program _ _ _ _ (Function.update (Function.update (bank first) (aux .reader) tail) (reg .numBase true) x.denominator) at h1
  have hbuf:Function.update (bank first) (aux .reader) tail=
      bank {buffers w tail reversed with registers:=Function.update w.registers (.numBase,false) (signed x)}:=by
    rw [update_added]
    congr 1
    congr 1
    funext slot
    cases slot <;> simp [first,buffers]
  rw [hbuf,update_register] at h1
  exact T.join h0 h1
end RiemannGaussian.SemiprimeD1StackRecoveryAffineReadParse
