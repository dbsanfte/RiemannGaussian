/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackRecoveryWeightsInnerBounds
import RiemannGaussian.SemiprimeD1StackRecoveryWeightsScalarBounds
/-! # Whole actual coefficient clock from its own physical inputs and fitted cache lengths -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackRecoveryWeightsCoefficientBounds
open SemiprimeD1StackRecoveryWeights SemiprimeD1StackRecoveryWeightsView
open SemiprimeD1StackRecoveryWeightsWidths SemiprimeD1StackRecoveryWeightsBankBounds
open SemiprimeD1StackRecoveryWeightsOuterView SemiprimeD1StackNormalizedInverseBankBounds
open SemiprimeRationalBits (RationalWord zeroWord)
/-- A fixed cap covers every actual paid setup/pair/scalar/frame/drain of ONE whole coefficient. -/
theorem coefficient_bound (inverse powers:List RationalWord) (scalar:RationalWord) (j n:Nat) (width out:List Bool) (s:Nat)
    (hs:1 ≤ s) (hw:width.length ≤ s)
    (hi:(SemiprimeD1StackNormalizedInverse.tape inverse).length ≤ s)
    (hp:(SemiprimeD1StackNormalizedInverse.tape powers).length ≤ s)
    (hscalar:B.bytes scalar ≤ s) (hq:j+(n+1) ≤ s) (ho:out.length ≤ 14*s^2):
    SemiprimeD1StackRecoveryWeightsCoefficient.timeBound inverse powers scalar j n width out ≤ 10^40*s^7:=by
  let w:=outer inverse powers scalar (j+(n+1)) width j out
  let total:=Spec.dotLoop width inverse powers j (n+1) zeroWord
  have hb:BoundedBank w.toWords s (5*s) (14*s^2):=outer_bound inverse powers scalar _ width j out s hs hw hi hp hq (by omega) ho
  have hz:B.bytes zeroWord ≤ 5*s:=by rw [B.zero_bytes];omega
  have ht:B.bytes total ≤ 5*s:=by
    have hh:=dot_bytes width inverse powers j (n+1) zeroWord (by rw [B.zero_bytes];omega)
    dsimp only [total]
    omega
  have hinner:=SemiprimeD1StackRecoveryWeightsInnerBounds.inner_bound w inverse powers width j (n+1) s hs hw hi hp hb hq zeroWord hz
  have hput:BoundedBank (putReg w .acc total).toWords s (5*s) (14*s^2):=put_bound _ _ _ _ hb .acc total ht
  have hscalarTime:=SemiprimeD1StackRecoveryWeightsScalarBounds.scalar_bound (putReg w .acc total) scalar total width s hs hw hput (by omega) ht
  have hc:SemiprimeD1StackRecoveryWeightsCounterInput.timeBound j n ≤ 100*s+100:=by
    unfold SemiprimeD1StackRecoveryWeightsCounterInput.timeBound
    omega
  have hs6:s ≤ s^6:=Nat.le_pow (by decide:0<6)
  have h16:1 ≤ s^6:=Nat.one_le_pow _ _ hs
  have hprod:(n+2)*s^6 ≤ 2*s^7:=by
    have hm:=Nat.mul_le_mul_right (s^6) (show n+2 ≤ 2*s by omega)
    simpa only [pow_succ,Nat.mul_assoc,Nat.mul_comm,Nat.mul_left_comm] using hm
  have hs67:s^6 ≤ s^7:=Nat.pow_le_pow_right hs (by decide:6≤7)
  unfold SemiprimeD1StackRecoveryWeightsCoefficient.timeBound
  change 2+SemiprimeD1StackRecoveryWeightsCounterInput.timeBound j n+
    SemiprimeD1StackRecoveryWeightsInner.timeBound w inverse powers width j (n+1) zeroWord+
    (j-1)+2+SemiprimeD1StackRecoveryWeightsScalar.timeBound (putReg w .acc total) scalar total width ≤ _
  nlinarith only [hinner,hscalarTime,hc,hprod,hs67,hs6,h16,hq,Nat.sub_le j 1]
end RiemannGaussian.SemiprimeD1StackRecoveryWeightsCoefficientBounds
