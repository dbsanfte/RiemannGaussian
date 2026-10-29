/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackRecoveryAffineCoefficientsBounds
/-! # One actual original-slope stage pays every coefficient, array byte and cleanup -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackRecoveryAffineSlopeBounds
open SemiprimeD1StackRecoveryAffineView SemiprimeD1StackRecoveryAffineWordCaps
open SemiprimeD1StackRecoveryAffineByteCaps (Small)
/-- Whole actual coefficient-array stage allowance, fixed before all dimensions. -/
def cap (B L:Nat):Nat:=10^43*(112*L+B^6+1)
/-- One real slope parse plus the full actual stage has the same quadratic q allowance. -/
def rowCap (B L:Nat):Nat:=10^44*(112*L+B^6+1)
/-- Actual final output bytes fit the same paid partial-array framing budget. -/
theorem output_length (xs:List SemiprimeRationalBits.RationalWord) (c:SemiprimeRationalBits.RationalWord)
    (width:List Bool) (q L:Nat) (hb:q*(4*width.length+9)+1≤ L):
    (SemiprimeD1StackRecoveryAffineSlopeStage.bytes xs c width q).length≤ L:=by
  rw [SemiprimeD1StackRecoveryAffineSlopeStage.bytes_original]
  have h:=SemiprimeD1StackRecoveryAffineByteCaps.vector_length width _
    (SemiprimeD1StackRecoveryAffineByteCaps.multiply_small width xs c q)
  rw [SemiprimeD1StackRecoveryAffineByteCaps.multiply_length] at h
  exact h.trans hb
/-- Same physical q copy, full coefficient loop, old-array drain, two real reversals and slope drains. -/
theorem source_le (w:Words) (xs:List SemiprimeRationalBits.RationalWord) (c:SemiprimeRationalBits.RationalWord)
    (width:List Bool) (q B L:Nat)
    (hW:width.length+2≤ B) (hBL:B≤ L) (hr:Registers w B) (hd:Data w L)
    (hxs:∀x∈xs,Small width x) (hc:Small width c)
    (ha:(vector xs).length≤ L) (hq:q≤ L) (hb:q*(4*width.length+9)+1≤ L):
    SemiprimeD1StackRecoveryAffineSlopeStage.runBound w xs c width q≤ (q+1)^2*cap B L:=by
  have hcoef:=SemiprimeD1StackRecoveryAffineCoefficientsBounds.source_le w xs c width q [false] B L hW hBL hr hd hxs hc ha
    (by change 1+q*(4*width.length+9)≤ L;omega)
  have hout:=output_length xs c width q L hb
  have hcn:(signed c).length+c.denominator.length≤ 2*B:=by
    change c.numerator.magnitude.length+1+c.denominator.length≤ 2*B
    have hn:=hc.1
    have hden:=hc.2
    omega
  have hpow:B≤ B^6:=Nat.le_pow (by decide:0<6)
  have hover:1+(5*q+4)+SemiprimeD1StackRecoveryAffineArrayMove.runBound (vector xs)
      (SemiprimeD1StackRecoveryAffineSlopeStage.bytes xs c width q)+((signed c).length+1+c.denominator.length+1)≤
      SemiprimeD1StackRecoveryAffineCoefficientsBounds.cap B L:=by
    unfold SemiprimeD1StackRecoveryAffineArrayMove.runBound SemiprimeD1StackRecoveryAffineCoefficientsBounds.cap
    omega
  have hmul:SemiprimeD1StackRecoveryAffineCoefficientsBounds.cap B L≤
      (q+1)^2*SemiprimeD1StackRecoveryAffineCoefficientsBounds.cap B L:=by
    simpa only [Nat.one_mul] using Nat.mul_le_mul_right
      (SemiprimeD1StackRecoveryAffineCoefficientsBounds.cap B L) (by nlinarith:1≤ (q+1)^2)
  have hcap:2*SemiprimeD1StackRecoveryAffineCoefficientsBounds.cap B L≤ cap B L:=by
    unfold SemiprimeD1StackRecoveryAffineCoefficientsBounds.cap cap
    omega
  calc
    _≤ (q+1)^2*SemiprimeD1StackRecoveryAffineCoefficientsBounds.cap B L+
        SemiprimeD1StackRecoveryAffineCoefficientsBounds.cap B L:=by
      unfold SemiprimeD1StackRecoveryAffineSlopeStage.runBound
      omega
    _≤ (q+1)^2*SemiprimeD1StackRecoveryAffineCoefficientsBounds.cap B L+
        (q+1)^2*SemiprimeD1StackRecoveryAffineCoefficientsBounds.cap B L:=Nat.add_le_add_left hmul _
    _=(q+1)^2*(2*SemiprimeD1StackRecoveryAffineCoefficientsBounds.cap B L):=by ring
    _≤ (q+1)^2*cap B L:=Nat.mul_le_mul_left _ hcap
/-- Actual original tag/two-field parsing overhead is paid without dropping zero terms or raw padding. -/
theorem row_le (w:Words) (xs:List SemiprimeRationalBits.RationalWord) (c:SemiprimeRationalBits.RationalWord)
    (width:List Bool) (q B L:Nat)
    (hW:width.length+2≤ B) (hBL:B≤ L) (hr:Registers w B) (hd:Data w L)
    (hxs:∀x∈xs,Small width x) (hc:Small width c)
    (ha:(vector xs).length≤ L) (hq:q≤ L) (hb:q*(4*width.length+9)+1≤ L):
    (1+(8*(signed c).length+8+(8*c.denominator.length+8)))+
      SemiprimeD1StackRecoveryAffineSlopeStage.runBound w xs c width q≤ (q+1)^2*rowCap B L:=by
  have h:=source_le w xs c width q B L hW hBL hr hd hxs hc ha hq hb
  have hcn:(signed c).length+c.denominator.length≤ 2*B:=by
    change c.numerator.magnitude.length+1+c.denominator.length≤ 2*B
    have hn:=hc.1
    have hden:=hc.2
    omega
  have hpow:B≤ B^6:=Nat.le_pow (by decide:0<6)
  have hp:1+(8*(signed c).length+8+(8*c.denominator.length+8))≤ cap B L:=by unfold cap;omega
  have hm:cap B L≤ (q+1)^2*cap B L:=by
    simpa only [Nat.one_mul] using Nat.mul_le_mul_right (cap B L) (by nlinarith:1≤ (q+1)^2)
  have hcap:2*cap B L≤ rowCap B L:=by unfold cap rowCap;omega
  calc
    _≤ cap B L+(q+1)^2*cap B L:=Nat.add_le_add hp h
    _≤ (q+1)^2*cap B L+(q+1)^2*cap B L:=Nat.add_le_add_right hm _
    _=(q+1)^2*(2*cap B L):=by ring
    _≤ (q+1)^2*rowCap B L:=Nat.mul_le_mul_left _ hcap
end RiemannGaussian.SemiprimeD1StackRecoveryAffineSlopeBounds
