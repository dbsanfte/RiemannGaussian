/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackNormalizedInverseFramedBounds
import RiemannGaussian.SemiprimeD1StackNormalizedInversePairBounds
/-! # Complete real final-negation/frame/drain clock with no fit or validity advice -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackNormalizedInverseNegateBounds
open SemiprimeD1StackNormalizedInverse SemiprimeD1StackNormalizedInverseView
open SemiprimeD1StackNormalizedInverseWidths SemiprimeD1StackNormalizedInverseBankBounds
open SemiprimeD1StackNormalizedInverseFramedBounds SemiprimeD1StackNormalizedInversePairBounds
open SemiprimeD1StackNormalizedInverseNegate
/-- Actual coefficient negation includes literal ZERO, whole R36 call, both Frames and all8 drains. -/
theorem negateBound_le (w : Words) (width : List Bool) (s : ℕ) (hs : 1 ≤ s) (hw : width.length ≤ s)
    (hbank : BoundedBank w s (5*s) (14*s^2)) : negateBound w width ≤ 10^37*s^6 := by
  have hseed:=put_bound w _ _ _ hbank .right SemiprimeRationalBits.zeroWord (by rw [zero_bytes];omega)
  have hcall:=small_call .negate _ width s hs hw hseed
  have hm:=beforeClear_mass w width s hs hw hbank
  have hout : bytes (output w width)=2*width.length+1 := execute_bytes .neg _ _ width
  have hs6:s ≤ s^6:=Nat.le_pow (by decide:0<6)
  have hs26:s^2 ≤ s^6:=Nat.pow_le_pow_right hs (by decide:2≤6)
  have hp6:1 ≤ s^6:=Nat.one_le_pow _ _ hs
  change 2+SemiprimeD1StackNormalizedInverseOperationCall.callBound .negate
    (putReg w .right SemiprimeRationalBits.zeroWord) width+(6*bytes (output w width)+11)+
      8*(SemiprimeD1StackNormalizedInverseCleanup.mass (store (beforeClear w width))+1) ≤ _
  rw [hout]
  nlinarith only [hcall,hm,hw,hs6,hs26,hp6]
end RiemannGaussian.SemiprimeD1StackNormalizedInverseNegateBounds
