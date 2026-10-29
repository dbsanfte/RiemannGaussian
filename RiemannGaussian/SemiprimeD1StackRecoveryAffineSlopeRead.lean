/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackRecoveryAffinePrimitives
import RiemannGaussian.SemiprimeD1StackRecoveryAffineView
/-! # Actual reverse-catalogue row consumption before each affine array source -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackRecoveryAffineSlopeRead
open SemiprimeD1StackRecoveryAffine SemiprimeD1StackRecoveryAffineView SemiprimeD1StackProcedureTrace
open SemiprimeSourceHistogramKeyBits (frame)
namespace T
export SemiprimeD1StackRecoveryAffinePrimitives (join pop_run field_read)
end T
/-- The actual unread reversed-row catalogue, with all other111 physical words retained. -/
def tape (w:Words) (bytes:List Bool):Words:={w with added:=Function.update w.added .reverseSlopes bytes}
/-- One real parser/tag consumption changes exactly the reached physical tape suffix. -/
theorem update_tape (w:Words) (before after:List Bool):
    Function.update (bank (tape w before)) (aux .reverseSlopes) after=bank (tape w after):=by
  rw [update_added]
  simp only [tape,Function.update_idem]
/-- Two real parsers acquire the current original slope with all signed/raw denominator padding intact. -/
theorem fields_run (w:Words) (x:SemiprimeRationalBits.RationalWord) (tail:List Bool)
    (hn:w.registers (.slope,false)=[]) (hd:w.registers (.slope,true)=[])
    (hs:w.auxiliary .frameScratch=[]) (hv:w.auxiliary .scan=[]):
    Runs program (8*(signed x).length+8+(8*x.denominator.length+8))
      (.local (.field (.slope true false))) (bank (tape w (frame (signed x) (frame x.denominator tail))))
      (.local .seedNext) (bank (putReg (tape w tail) .slope x)):=by
  let first:Words:={w with registers:=Function.update w.registers (.slope,false) (signed x)}
  have h0:=T.field_read (.slope true false) (bank (tape w (frame (signed x) (frame x.denominator tail))))
    (signed x) (frame x.denominator tail) rfl hs hn hv
  change Runs program _ _ _ _ (Function.update (Function.update
    (bank (tape w (frame (signed x) (frame x.denominator tail)))) (aux .reverseSlopes) (frame x.denominator tail))
    (reg .slope false) (signed x)) at h0
  rw [update_tape,update_register] at h0
  change Runs program _ _ _ _ (bank (tape first (frame x.denominator tail))) at h0
  have he:first.registers (.slope,true)=[]:=by simp [first,hd]
  have h1:=T.field_read (.slope true true) (bank (tape first (frame x.denominator tail))) x.denominator tail rfl hs he hv
  change Runs program _ _ _ _ (Function.update (Function.update (bank (tape first (frame x.denominator tail)))
    (aux .reverseSlopes) tail) (reg .slope true) x.denominator) at h1
  rw [update_tape,update_register] at h1
  exact T.join h0 h1
/-- The next original row's TRUE tag is physically popped before its two real parsers. -/
theorem source_run (w:Words) (x:SemiprimeRationalBits.RationalWord) (tail:List Bool)
    (hn:w.registers (.slope,false)=[]) (hd:w.registers (.slope,true)=[])
    (hs:w.auxiliary .frameScratch=[]) (hv:w.auxiliary .scan=[]):
    Runs program (1+(8*(signed x).length+8+(8*x.denominator.length+8)))
      (.local .slopeLoop) (bank (tape w (SemiprimeD1StackRecoveryGridView.slopeRow x tail)))
      (.local .seedNext) (bank (putReg (tape w tail) .slope x)):=by
  have h0:=T.pop_run (.local .slopeLoop) (.local .abort) (.local .slopeEOF)
    (.local (.field (.slope true false))) (aux .reverseSlopes)
    (bank (tape w (SemiprimeD1StackRecoveryGridView.slopeRow x tail)))
    (SemiprimeD1StackRecoveryGridView.slopeRow x tail) rfl rfl
  change Runs program 1 _ _ (.local (.field (.slope true false)))
    (Function.update (bank (tape w (SemiprimeD1StackRecoveryGridView.slopeRow x tail)))
      (aux .reverseSlopes) (frame (signed x) (frame x.denominator tail))) at h0
  rw [update_tape] at h0
  exact T.join h0 (fields_run w x tail hn hd hs hv)
end RiemannGaussian.SemiprimeD1StackRecoveryAffineSlopeRead
