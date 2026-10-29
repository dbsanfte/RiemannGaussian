/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackRecoveryWeightsCoefficientBounds
/-! # Complete chronological output tail and every actual outer iteration are paid by the same loop clock -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackRecoveryWeightsOuterBounds
open SemiprimeD1StackRecoveryWeights SemiprimeD1StackRecoveryWeightsView
open SemiprimeD1StackRecoveryWeightsWidths
open SemiprimeRationalBits (RationalWord)
/-- SAME actual outer-source budget, including every decreasing coefficient and the final EOF. -/
theorem outer_bound (inverse powers:List RationalWord) (scalar:RationalWord) (q:Nat) (width:List Bool) (r:Nat) (out:List Bool) (s:Nat)
    (hs:1 ≤ s) (hw:width.length ≤ s)
    (hi:(SemiprimeD1StackNormalizedInverse.tape inverse).length ≤ s)
    (hp:(SemiprimeD1StackNormalizedInverse.tape powers).length ≤ s)
    (hscalar:B.bytes scalar ≤ s) (hq:q ≤ s) (hr:r ≤ q)
    (ho:out.length+r*(4*width.length+5) ≤ 14*s^2):
    SemiprimeD1StackRecoveryWeightsOuter.timeBound inverse powers scalar q width r out ≤ (r+1)*(10^41*s^7):=by
  induction r generalizing out with
  | zero=>
    have h17:1 ≤ s^7:=Nat.one_le_pow _ _ hs
    change 1 ≤ 1*(10^41*s^7)
    omega
  | succ r ih=>
    have hqeq:r+(q-(r+1)+1)=q:=by omega
    have hc:=SemiprimeD1StackRecoveryWeightsCoefficientBounds.coefficient_bound inverse powers scalar r (q-(r+1)) width out s hs hw hi hp hscalar (by omega) (by omega)
    have hrow:(SemiprimeD1StackNormalizedInverse.row (Spec.weight width q r scalar inverse powers) out).length=4*width.length+out.length+5:=by
      rw [B.row_bytes,weight_bytes]
      omega
    have ho':(SemiprimeD1StackNormalizedInverse.row (Spec.weight width q r scalar inverse powers) out).length+r*(4*width.length+5) ≤ 14*s^2:=by
      rw [hrow]
      rw [Nat.add_mul] at ho
      omega
    have ht:=ih _ (by omega) ho'
    have h17:1 ≤ s^7:=Nat.one_le_pow _ _ hs
    change 1+SemiprimeD1StackRecoveryWeightsCoefficient.timeBound inverse powers scalar r (q-(r+1)) width out+_ ≤ _
    nlinarith only [hc,ht,h17]
end RiemannGaussian.SemiprimeD1StackRecoveryWeightsOuterBounds
