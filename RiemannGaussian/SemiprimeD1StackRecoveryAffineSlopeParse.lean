/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackRecoveryAffineSlopeBuffers
import RiemannGaussian.SemiprimeD1StackRecoveryAffinePrimitives
/-! # Two real Field calls acquire exactly one physical signed slope row -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackRecoveryAffineSlopeParse
open SemiprimeD1StackRecoveryAffine SemiprimeD1StackRecoveryAffineView
open SemiprimeD1StackRecoveryAffineSlopeBuffers SemiprimeD1StackProcedureTrace
open SemiprimeSourceHistogramKeyBits (frame)
namespace T
export SemiprimeD1StackRecoveryAffinePrimitives (join pop_run field_read)
end T
/-- Each parser really visits both framed fields and clears both validity flags. -/
theorem fields_run (w:Words) (x:SemiprimeRationalBits.RationalWord) (tail reversed:List Bool)
    (hn:w.registers (.slope,false)=[]) (hd:w.registers (.slope,true)=[])
    (hs:w.auxiliary .frameScratch=[]) (hv:w.auxiliary .scan=[]) :
    Runs program (8*(signed x).length+8+(8*x.denominator.length+8))
      (.local (.field (.slope false false)))
      (bank (buffers w (frame (signed x) (frame x.denominator tail)) reversed))
      (.local (.frame (.slope true))) (bank (putReg (buffers w tail reversed) .slope x)):=by
  let before:=buffers w (frame (signed x) (frame x.denominator tail)) reversed
  let first:Words:={buffers w (frame x.denominator tail) reversed with registers:=Function.update w.registers (.slope,false) (signed x)}
  have h0:=T.field_read (.slope false false) (bank before) (signed x) (frame x.denominator tail) rfl hs hn hv
  change Runs program _ _ _ _ (Function.update (Function.update (bank before) (aux .reader) (frame x.denominator tail)) (reg .slope false) (signed x)) at h0
  rw [update_reader,update_register] at h0
  change Runs program _ _ _ _ (bank first) at h0
  have he:first.registers (.slope,true)=[]:=by
    change Function.update w.registers (.slope,false) (signed x) (.slope,true)=[]
    simp [hd]
  have h1:=T.field_read (.slope false true) (bank first) x.denominator tail rfl hs he hv
  change Runs program _ _ _ _ (Function.update (Function.update (bank first) (aux .reader) tail) (reg .slope true) x.denominator) at h1
  have hbuf:Function.update (bank first) (aux .reader) tail=
      bank {buffers w tail reversed with registers:=Function.update w.registers (.slope,false) (signed x)}:=by
    rw [update_added]
    congr 1
    congr 1
    funext slot
    cases slot <;> simp [first,buffers]
  rw [hbuf,update_register] at h1
  exact T.join h0 h1
/-- The TRUE occurrence tag is physically consumed before the same two parser calls. -/
theorem tagged_run (w:Words) (x:SemiprimeRationalBits.RationalWord) (tail reversed:List Bool)
    (hn:w.registers (.slope,false)=[]) (hd:w.registers (.slope,true)=[])
    (hs:w.auxiliary .frameScratch=[]) (hv:w.auxiliary .scan=[]) :
    Runs program (1+(8*(signed x).length+8+(8*x.denominator.length+8)))
      (.local .reverseLoop)
      (bank (buffers w (SemiprimeD1StackRecoveryGridView.slopeRow x tail) reversed))
      (.local (.frame (.slope true))) (bank (putReg (buffers w tail reversed) .slope x)):=by
  have h0:=T.pop_run (.local .reverseLoop) (.local .abort) (.local .reverseEOF)
    (.local (.field (.slope false false))) (aux .reader)
    (bank (buffers w (SemiprimeD1StackRecoveryGridView.slopeRow x tail) reversed))
    (SemiprimeD1StackRecoveryGridView.slopeRow x tail) rfl rfl
  change Runs program 1 _ _ (.local (.field (.slope false false)))
    (Function.update (bank (buffers w (SemiprimeD1StackRecoveryGridView.slopeRow x tail) reversed))
      (aux .reader) (frame (signed x) (frame x.denominator tail))) at h0
  rw [update_reader] at h0
  exact T.join h0 (fields_run w x tail reversed hn hd hs hv)
end RiemannGaussian.SemiprimeD1StackRecoveryAffineSlopeParse
