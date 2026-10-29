/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackRecoveryAffineReadParse
import RiemannGaussian.SemiprimeD1StackRecoveryAffineReadClear
/-! # Actual selected/skipped array rows, with raw signed and denominator bytes -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackRecoveryAffineReadRow
open SemiprimeD1StackRecoveryAffine SemiprimeD1StackRecoveryAffineView
open SemiprimeD1StackRecoveryAffineReadBuffers SemiprimeD1StackProcedureTrace
open SemiprimeSourceHistogramKeyBits (frame)
namespace T
export SemiprimeD1StackRecoveryAffinePrimitives (join pop_run)
end T
/-- TRUE row tag consumption precedes the two actual coefficient Field calls. -/
theorem fields_run (part:Part) (take:Bool) (w:Words) (x:SemiprimeRationalBits.RationalWord) (tail todo:List Bool)
    (hn:w.registers (.numBase,false)=[]) (hd:w.registers (.numBase,true)=[])
    (hs:w.auxiliary .frameScratch=[]) (hv:w.auxiliary .scan=[]) :
    Runs program (1+(8*(signed x).length+8+(8*x.denominator.length+8)))
      (.local (.readTag part take))
      (bank (buffers w (SemiprimeD1StackRecoveryGridView.slopeRow x tail) todo))
      (afterField (.coefficient part take true)) (bank (putReg (buffers w tail todo) .numBase x)):=by
  have h0:=T.pop_run (.local (.readTag part take)) (.local .abort) (.local (.missingReader part))
    (.local (.field (.coefficient part take false))) (aux .reader)
    (bank (buffers w (SemiprimeD1StackRecoveryGridView.slopeRow x tail) todo))
    (SemiprimeD1StackRecoveryGridView.slopeRow x tail) rfl rfl
  change Runs program 1 _ _ (.local (.field (.coefficient part take false)))
    (Function.update (bank (buffers w (SemiprimeD1StackRecoveryGridView.slopeRow x tail) todo))
      (aux .reader) (frame (signed x) (frame x.denominator tail))) at h0
  rw [update_reader] at h0
  exact T.join h0 (SemiprimeD1StackRecoveryAffineReadParse.fields_run part take w x tail todo hn hd hs hv)
/-- Taking a reached coefficient still physically consumes the entire unread array suffix. -/
theorem take_run (part:Part) (w:Words) (x:SemiprimeRationalBits.RationalWord) (tail todo:List Bool)
    (hn:w.registers (.numBase,false)=[]) (hd:w.registers (.numBase,true)=[])
    (hs:w.auxiliary .frameScratch=[]) (hv:w.auxiliary .scan=[]) :
    Runs program (8*((signed x).length+x.denominator.length)+18+tail.length)
      (.local (.readTag part true))
      (bank (buffers w (SemiprimeD1StackRecoveryGridView.slopeRow x tail) todo))
      (.local (.factor part)) (bank (putReg (buffers w [] todo) .numBase x)):=by
  have h:=T.join (fields_run part true w x tail todo hn hd hs hv)
    (SemiprimeD1StackRecoveryAffineReadClear.tail_run part w x tail todo)
  convert h using 1
  omega
/-- Skipping one reached coefficient drains both fields before the next actual count pop. -/
theorem skip_run (part:Part) (w:Words) (x:SemiprimeRationalBits.RationalWord) (tail todo:List Bool)
    (hn:w.registers (.numBase,false)=[]) (hd:w.registers (.numBase,true)=[])
    (hs:w.auxiliary .frameScratch=[]) (hv:w.auxiliary .scan=[]) :
    Runs program (9*((signed x).length+x.denominator.length)+19)
      (.local (.readTag part false))
      (bank (buffers w (SemiprimeD1StackRecoveryGridView.slopeRow x tail) todo))
      (.local (.readCount part)) (bank (buffers w tail todo)):=by
  have h:=T.join (fields_run part false w x tail todo hn hd hs hv)
    (SemiprimeD1StackRecoveryAffineReadClear.skip_run part w x tail todo hn hd)
  convert h using 1
  omega
end RiemannGaussian.SemiprimeD1StackRecoveryAffineReadRow
