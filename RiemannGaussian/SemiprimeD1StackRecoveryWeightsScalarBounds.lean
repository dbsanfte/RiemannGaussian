/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackRecoveryWeightsBankBounds
/-! # Own final-scalar/copies/frame/drain clock, with the full retained output physically charged -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackRecoveryWeightsScalarBounds
open SemiprimeD1StackRecoveryWeights SemiprimeD1StackRecoveryWeightsView
open SemiprimeD1StackRecoveryWeightsWidths
open SemiprimeD1StackRecoveryWeightsScalar SemiprimeD1StackRecoveryWeightsScalarInput
open SemiprimeD1StackNormalizedInverseBankBounds
open SemiprimeRationalBits (RationalWord)
/-- Actual final inputs, the fitted product and both preserving frames retain bounded complete-bank mass. -/
theorem beforeClear_bound (w:Words) (scalar total:RationalWord) (width:List Bool) (s:Nat)
    (hs:1 ≤ s) (hw:width.length ≤ s) (hbank:BoundedBank w.toWords s (5*s) (14*s^2))
    (hscalar:B.bytes scalar ≤ 5*s) (htotal:B.bytes total ≤ 5*s):
    BoundedBank (beforeClear w scalar total width).toWords s (5*s) (30*s^2):=by
  have hf:BoundedBank (filled w scalar total).toWords s (5*s) (14*s^2):=
    put_bound _ _ _ _ (put_bound _ _ _ _ hbank .left scalar hscalar) .right total htotal
  have ha:BoundedBank (SemiprimeD1StackRecoveryWeightsCalls.afterOperation .product (filled w scalar total) width).toWords s (5*s) (14*s^2):=
    after_bound .product _ width _ _ _ hf (by omega)
  have hs2:s ≤ s^2:=Nat.le_pow (by decide:0<2)
  refine ⟨ha.1,ha.2.1,?_⟩
  intro k
  by_cases he:k=.output
  · subst k
    change (SemiprimeD1StackNormalizedInverse.row (output scalar total width) (w.auxiliary .output)).length ≤ _
    rw [B.row_bytes]
    have hb:B.bytes (output scalar total width)=2*width.length+1:=B.execute_bytes .mul scalar total width
    have ho:=hbank.2.2 .output
    nlinarith only [hb,ho,hw,hs,hs2]
  · change (Function.update w.auxiliary .output _ k).length ≤ _
    rw [Function.update_of_ne he]
    have hh:=hbank.2.2 k
    omega
/-- Pure numerical accounting avoids reducing any rational payload in the clock proof. -/
private theorem scalar_arithmetic (s width x y z call mass:Nat) (hs:1 ≤ s) (hw:width ≤ s)
    (hx:x ≤ 5*s) (hy:y ≤ 5*s) (hz:z=2*width+1)
    (hc:call ≤ 10^36*s^6) (hm:mass ≤ 36*s+8*(5*s)+14*(30*s^2)):
    5*(x+y)+16+call+(6*z+11)+8*(mass+1) ≤ 10^38*s^6:=by
  have hs6:s ≤ s^6:=Nat.le_pow (by decide:0<6)
  have hs26:s^2 ≤ s^6:=Nat.pow_le_pow_right hs (by decide:2≤6)
  have h16:1 ≤ s^6:=Nat.one_le_pow _ _ hs
  nlinarith only [hc,hm,hz,hx,hy,hw,hs6,hs26,h16]
/-- Every actual four-copy/whole-R36/two-frame/eight-drain step has a fixed physical-bit cap. -/
theorem scalar_bound (w:Words) (scalar total:RationalWord) (width:List Bool) (s:Nat)
    (hs:1 ≤ s) (hw:width.length ≤ s) (hbank:BoundedBank w.toWords s (5*s) (14*s^2))
    (hscalar:B.bytes scalar ≤ 5*s) (htotal:B.bytes total ≤ 5*s):
    SemiprimeD1StackRecoveryWeightsScalar.timeBound w scalar total width ≤ 10^38*s^6:=by
  have hf:BoundedBank (filled w scalar total).toWords s (5*s) (14*s^2):=
    put_bound _ _ _ _ (put_bound _ _ _ _ hbank .left scalar hscalar) .right total htotal
  have hc:=SemiprimeD1StackNormalizedInversePairBounds.small_call .product (filled w scalar total).toWords width s hs hw hf
  have hm:=mass_le (beforeClear w scalar total width).toWords s (5*s) (30*s^2)
    (beforeClear_bound w scalar total width s hs hw hbank hscalar htotal)
  have hb:B.bytes (output scalar total width)=2*width.length+1:=B.execute_bytes .mul scalar total width
  have hinputs:SemiprimeD1StackRecoveryWeightsScalarInput.timeBound scalar total=5*(B.bytes scalar+B.bytes total)+16:=by
    unfold SemiprimeD1StackRecoveryWeightsScalarInput.timeBound SemiprimeD1StackNormalizedInverseWidths.bytes
    omega
  unfold SemiprimeD1StackRecoveryWeightsScalar.timeBound
  rw [hinputs]
  exact scalar_arithmetic s width.length (B.bytes scalar) (B.bytes total) (B.bytes (output scalar total width)) _ _ hs hw hscalar htotal hb hc hm
end RiemannGaussian.SemiprimeD1StackRecoveryWeightsScalarBounds
