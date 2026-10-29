/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackRecoveryGridSite
import RiemannGaussian.SemiprimeD1StackRecoveryGridByteBounds
/-! # Own per-operation bounds from actual source-word widths
The included R36 clock depends on its five actual copied words. Foreign slopes
and metadata are retained; their bytes enter only the physical cleanup cap.
-/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackRecoveryGridOperationBounds
open SemiprimeD1StackRecoveryGrid SemiprimeD1StackRecoveryGridView
open SemiprimeD1StackRecoveryGridCleanup SemiprimeD1StackRecoveryGridOperationInput
open SemiprimeD1StackRecoveryGridOperationOutput
namespace Op
export SemiprimeD1StackRecoveryGridOperation (prefixTime timeBound)
end Op
namespace RBound
export SemiprimeD1StackRationalOperationBounds (runBound_le polynomial)
export SemiprimeD1StackRationalOperationExecution (runBound)
export SemiprimeD1StackRationalOperationEncoding (inputSize)
end RBound
attribute [local irreducible] RBound.runBound mass
/-- SAME actual R36 clock has a sixth-degree cap from only its actual signed/magnitude/denominator/template source bytes. -/
theorem rational_le (op:R.Op) (sx:Bool) (xn xd:List Bool) (sy:Bool) (yn yd width:List Bool) (B:Nat)
    (hB:1≤ B) (hxn:xn.length≤ B) (hxd:xd.length≤ B) (hyn:yn.length≤ B) (hyd:yd.length≤ B) (hw:width.length≤ B) :
    RBound.runBound op sx xn xd sy yn yd width≤10^30*B^6:=by
  have h0:=RBound.runBound_le op sx xn xd sy yn yd width
  have hs:RBound.inputSize (sx::xn) xd (sy::yn) yd width≤8*B:=by
    unfold RBound.inputSize
    simp only [List.length_cons]
    omega
  have hp:=Nat.pow_le_pow_left hs 6
  unfold RBound.polynomial at h0
  calc
    _≤100000000000000000000*(RBound.inputSize (sx::xn) xd (sy::yn) yd width)^6:=h0
    _≤100000000000000000000*(8*B)^6:=Nat.mul_le_mul_left _ hp
    _≤10^30*B^6:=by rw [mul_pow];nlinarith
/-- Both actual fitted result fields have exactly W cells; actual sign read/write adds two transitions only. -/
theorem save_le (op:R.Op) (sx:Bool) (xn xd:List Bool) (sy:Bool) (yn yd width:List Bool) (B:Nat)
    (hB:1≤ B) (hw:width.length≤ B) :saveTime (word op sx xn xd sy yn yd width)≤20*B:=by
  have h:=SemiprimeD1StackRecoveryGridByteBounds.operation_lengths
    (SemiprimeD1StackRationalOperation.operation op) (⟨⟨sx,xn⟩,xd⟩:SemiprimeRationalBits.RationalWord) ⟨⟨sy,yn⟩,yd⟩ width
  rw [←word_legacy] at h
  unfold saveTime
  omega
/-- Actual copies, whole source call, old-cache erasure and output/sign acquisition have their own sixth-degree word-width cap. -/
theorem prefix_le (site:Site) (w:Words) (sx:Bool) (xn xd:List Bool) (sy:Bool) (yn yd width:List Bool) (B:Nat)
    (hB:1≤ B) (hxn:xn.length≤ B) (hxd:xd.length≤ B) (hyn:yn.length≤ B) (hyd:yd.length≤ B) (hw:width.length≤ B)
    (holdn:(w.registers (destination site,false)).length≤ B) (holdd:(w.registers (destination site,true)).length≤ B) :
    Op.prefixTime site w sx xn xd sy yn yd width≤10^31*B^6:=by
  have hr:=rational_le (operation site) sx xn xd sy yn yd width B hB hxn hxd hyn hyd hw
  have hs:=save_le (operation site) sx xn xd sy yn yd width B hB hw
  have hp:B≤ B^6:=Nat.le_pow (by decide:0<6)
  unfold Op.prefixTime inputsTime
  simp only [List.length_cons]
  nlinarith
/-- Complete actual site clock, with real35-role cleanup, charges foreign retained bytes additively rather than expanding operands from elapsed time. -/
theorem time_le (site:Site) (w:Words) (sx:Bool) (xn xd:List Bool) (sy:Bool) (yn yd width:List Bool) (B:Nat)
    (hB:1≤ B) (hxn:xn.length≤ B) (hxd:xd.length≤ B) (hyn:yn.length≤ B) (hyd:yd.length≤ B) (hw:width.length≤ B)
    (holdn:(w.registers (destination site,false)).length≤ B) (holdd:(w.registers (destination site,true)).length≤ B) :
    Op.timeBound site w sx xn xd sy yn yd width≤10^35*(mass (bank w)+B^6+1):=by
  have h:=prefix_le site w sx xn xd sy yn yd width B hB hxn hxd hyn hyd hw holdn holdd
  unfold Op.timeBound
  nlinarith
/-- Two genuine call/return transitions fit the same uniform positive physical resource envelope. -/
theorem call_cap (q S:Nat) (hq:q≤10^35*S) (hS:1≤S) :q+2≤10^36*S:=by omega
/-- A genuine caller/return wrapper has the same physical source-word cap, with no native operation-clock transport. -/
theorem site_le (site:Site) (w:Words) (width:List Bool) (B:Nat) (hB:1≤ B) (hw:width.length≤ B)
    (hregs:∀r b,(w.registers (r,b)).length≤ B) :
    SemiprimeD1StackRecoveryGridSite.runBound site w width≤10^36*(mass (bank w)+B^6+1):=by
  have hxn:((getReg w (operand site false)).numerator.magnitude).length≤ B:=by
    change (w.registers (operand site false,false)).tail.length≤B
    rw [List.length_tail]
    exact (Nat.sub_le _ _).trans (hregs _ false)
  have hyn:((getReg w (operand site true)).numerator.magnitude).length≤ B:=by
    change (w.registers (operand site true,false)).tail.length≤B
    rw [List.length_tail]
    exact (Nat.sub_le _ _).trans (hregs _ false)
  have h:=time_le site w (getReg w (operand site false)).numerator.negative
    (getReg w (operand site false)).numerator.magnitude (getReg w (operand site false)).denominator
    (getReg w (operand site true)).numerator.negative (getReg w (operand site true)).numerator.magnitude
    (getReg w (operand site true)).denominator width B hB hxn (hregs _ true) hyn (hregs _ true) hw (hregs _ false) (hregs _ true)
  unfold SemiprimeD1StackRecoveryGridSite.runBound
  dsimp only
  exact call_cap _ _ h (by omega)
end RiemannGaussian.SemiprimeD1StackRecoveryGridOperationBounds
