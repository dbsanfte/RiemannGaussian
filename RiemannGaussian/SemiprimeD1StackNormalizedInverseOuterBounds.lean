/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackNormalizedInverseCoefficientBounds
import RiemannGaussian.SemiprimeD1StackNormalizedInverseAcquisition
/-! # Complete original physical-q coefficient loop with a fixed polynomial bit clock -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackNormalizedInverseOuterBounds
open SemiprimeD1StackNormalizedInverse SemiprimeD1StackNormalizedInverseView
open SemiprimeD1StackNormalizedInverseStateBounds SemiprimeD1StackNormalizedInverseCoefficientBounds
open SemiprimeD1StackNormalizedInverseOuter SemiprimeD1StackNormalizedInverseMeaning
open SemiprimeD1StackNormalizedInverseAcquisition
/-- The remaining-q loop sums only complete real coefficient caps plus actual pop/push instructions. -/
theorem outer_steps (a : List SemiprimeRationalBits.RationalWord) (q : ℕ) (width : List Bool) :
    ∀remaining n,0<n→n+remaining ≤ q→
      outerBound a q width remaining n (SemiprimeNormalizedInverseBits.build width a.toArray n).words.toList.reverse ≤
        (remaining+1)*(10^39*(inputSize a q width)^7+2) := by
  intro remaining
  induction remaining with
  | zero=>
    intro n hn hq
    change 1 ≤ (0+1)*(10^39*(inputSize a q width)^7+2)
    omega
  | succ remaining ih=>
    intro n hn hq
    have hc:=original_coefficient a q width remaining n (by omega) (by omega)
    have ht:=ih (n+1) (by omega) (by omega)
    rw [outerBound,←next_prefix a width n hn]
    nlinarith only [hc,ht]
/-- q is physically represented and paid; every coefficient's denominator reads/normalization/fits/framing/cleanup are included. -/
theorem outerBound_le (a : List SemiprimeRationalBits.RationalWord) (q : ℕ) (width : List Bool)
    (remaining n : ℕ) (hn : 0<n) (hq : n+remaining ≤ q) :
    outerBound a q width remaining n (SemiprimeNormalizedInverseBits.build width a.toArray n).words.toList.reverse ≤
      10^40*(inputSize a q width)^8 := by
  let s:=inputSize a q width
  have hs:=inputSize_caps a q width
  have h:=outer_steps a q width remaining n hn hq
  have hr:remaining+1 ≤ 2*s:=by dsimp only [s];omega
  have hm:=Nat.mul_le_mul_right (10^39*s^7+2) hr
  have hs8:s ≤ s^8:=Nat.le_pow (by decide:0<8)
  change _ ≤ 10^40*s^8
  change _ ≤ (remaining+1)*(10^39*s^7+2) at h
  nlinarith only [h,hm,hs8]
/-- Honest array/q/W bootstrap plus COMPLETE actual coefficient loop has one fixed polynomial cap. -/
theorem acquireBound_le (a : List SemiprimeRationalBits.RationalWord) (q : ℕ) (width : List Bool) :
    acquireBound a width q ≤ 10^41*(inputSize a q width)^8 := by
  cases q with
  | zero=>
    have hs:=inputSize_caps a 0 width
    have hp:1 ≤ (inputSize a 0 width)^8:=Nat.one_le_pow _ _ hs.1
    change 7 ≤ _
    omega
  | succ q=>
    have hs:=inputSize_caps a (q+1) width
    have hh:=outerBound_le a (q+1) width q 1 (by decide) (by omega)
    rw [first_original a width] at hh
    have hq:q+1 ≤ (inputSize a (q+1) width)^8 :=
      hs.2.2.1.trans (Nat.le_pow (by decide:0<8))
    have hp:1 ≤ (inputSize a (q+1) width)^8:=Nat.one_le_pow _ _ hs.1
    change 5*(q+1)+17+outerBound a (q+1) width q 1 [SemiprimeJetBits.oneWord] ≤ _
    nlinarith only [hh,hq,hp]
end RiemannGaussian.SemiprimeD1StackNormalizedInverseOuterBounds
