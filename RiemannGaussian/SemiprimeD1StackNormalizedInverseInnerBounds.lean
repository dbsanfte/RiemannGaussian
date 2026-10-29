/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackNormalizedInversePairBounds
import RiemannGaussian.SemiprimeD1StackNormalizedInverseInner
/-! # Whole actual descending-dot clock from physical input/cache capacities -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackNormalizedInverseInnerBounds
open SemiprimeD1StackNormalizedInverse SemiprimeD1StackNormalizedInverseView
open SemiprimeD1StackNormalizedInverseWidths SemiprimeD1StackNormalizedInverseBankBounds
open SemiprimeD1StackNormalizedInverseStateBounds SemiprimeD1StackNormalizedInversePairBounds
open SemiprimeD1StackNormalizedInverseInner SemiprimeD1StackNormalizedInverseIndices
open SemiprimeD1StackNormalizedInverseSpec
/-- All n physical pair iterations and the final actual EOF branch have their own summed clock. -/
theorem inner_steps (w : Words) (a reversed : List SemiprimeRationalBits.RationalWord) (width : List Bool)
    (s : ℕ) (hs : 1 ≤ s) (hw : width.length ≤ s) (ha : (tape a).length ≤ s)
    (hp : (tape reversed).length ≤ 14*s^2) (hbank : BoundedBank w s (5*s) (14*s^2))
    (hprefix : ∀word∈reversed,bytes word ≤ 5*s) :
    ∀n,n ≤ s→∀acc,bytes acc ≤ 5*s→innerBound w a reversed width n acc ≤ (n+1)*(10^37*s^6+3) := by
  intro n
  induction n with
  | zero=>
    intro hn acc hacc
    change 1 ≤ (0+1)*(10^37*s^6+3)
    omega
  | succ n ih=>
    intro hn acc hacc
    have hidx:=indexed_bound w s hs hbank n (n+1) n (by omega) hn (by omega) acc hacc
    have hpair:=pairBound_le (indexed w n (n+1) n acc) a reversed n width s hs hw ha hp (by omega) hidx hprefix
    have hnext : bytes (combine width (SemiprimeD1StackNormalizedInverseSpec.readWord a (n+1),
        SemiprimeD1StackNormalizedInverseSpec.readWord reversed n) acc) ≤ 5*s := by
      rw [combine_bytes]
      omega
    have htail:=ih (by omega) _ hnext
    change 1+SemiprimeD1StackNormalizedInversePair.pairBound (indexed w n (n+1) n acc) a reversed n width+2+
      innerBound w a reversed width n _ ≤ _
    nlinarith only [hpair,htail]
/-- Decreasing native loop notation records only SAME-source real pair caps, never an old semantic report clock. -/
theorem innerBound_le (w : Words) (a reversed : List SemiprimeRationalBits.RationalWord) (width : List Bool)
    (s : ℕ) (hs : 1 ≤ s) (hw : width.length ≤ s) (ha : (tape a).length ≤ s)
    (hp : (tape reversed).length ≤ 14*s^2) (hbank : BoundedBank w s (5*s) (14*s^2))
    (hprefix : ∀word∈reversed,bytes word ≤ 5*s) (n : ℕ) (hn : n ≤ s)
    (acc : SemiprimeRationalBits.RationalWord) (hacc : bytes acc ≤ 5*s) :
    innerBound w a reversed width n acc ≤ 10^38*s^7 := by
  have hh:=inner_steps w a reversed width s hs hw ha hp hbank hprefix n hn acc hacc
  have hn1:n+1 ≤ 2*s:=by omega
  have hm:=Nat.mul_le_mul_right (10^37*s^6+3) hn1
  have hs7:s ≤ s^7:=Nat.le_pow (by decide:0<7)
  nlinarith only [hh,hm,hs7]
end RiemannGaussian.SemiprimeD1StackNormalizedInverseInnerBounds
