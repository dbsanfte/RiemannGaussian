/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackRecoveryWeightsBankBounds
/-! # SAME actual descending pair-loop clock from physical cache widths, never elapsed-prefix widths -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackRecoveryWeightsInnerBounds
open SemiprimeD1StackRecoveryWeights SemiprimeD1StackRecoveryWeightsView
open SemiprimeD1StackRecoveryWeightsWidths SemiprimeD1StackRecoveryWeightsBankBounds
open SemiprimeD1StackNormalizedInverseBankBounds
open SemiprimeRationalBits (RationalWord)
/-- Each actual pair has its own paid physical scans and fitted arithmetic cap. -/
theorem inner_bound (w:Words) (inverse powers:List RationalWord) (width:List Bool) (j n s:Nat)
    (hs:1 ≤ s) (hw:width.length ≤ s)
    (hi:(SemiprimeD1StackNormalizedInverse.tape inverse).length ≤ s)
    (hp:(SemiprimeD1StackNormalizedInverse.tape powers).length ≤ s)
    (hbank:BoundedBank w.toWords s (5*s) (14*s^2)) (hn:j+n ≤ s)
    (acc:RationalWord) (hacc:B.bytes acc ≤ 5*s):
    SemiprimeD1StackRecoveryWeightsInner.timeBound w inverse powers width j n acc ≤ (n+1)*(10^38*s^6):=by
  induction n generalizing acc with
  | zero=>
    have h16:1 ≤ s^6:=Nat.one_le_pow _ _ hs
    change 1 ≤ 1*(10^38*s^6)
    omega
  | succ n ih=>
    have hidx:=indexed_bound w s hs hbank n n (j+n) (by omega) (by omega) (by omega) acc hacc
    have hpair:=pairBound_le (SemiprimeD1StackRecoveryWeightsIndices.indexed w n n (j+n) acc)
      inverse powers n (j+n) width s hs hw hi hp (by omega) (by omega) hidx
    have hnext:B.bytes (Spec.combine width inverse powers j (j+n) acc) ≤ 5*s:=by rw [combine_bytes];omega
    have htail:=ih (by omega) _ hnext
    have h16:1 ≤ s^6:=Nat.one_le_pow _ _ hs
    change 1+SemiprimeD1StackRecoveryWeightsPair.timeBound _ _ _ _ _ _+2+_ ≤ _
    nlinarith only [hpair,htail,h16]
end RiemannGaussian.SemiprimeD1StackRecoveryWeightsInnerBounds
