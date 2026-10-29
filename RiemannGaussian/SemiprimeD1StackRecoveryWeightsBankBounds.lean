/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackRecoveryWeightsWidths
import RiemannGaussian.SemiprimeD1StackNormalizedInversePairBounds
/-! # All58 reused physical word lengths at actual caller boundaries, with scalar2 retained -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackRecoveryWeightsBankBounds
open SemiprimeD1StackRecoveryWeights SemiprimeD1StackRecoveryWeightsView
open SemiprimeD1StackRecoveryWeightsOuterView SemiprimeD1StackRecoveryWeightsIndices
open SemiprimeD1StackNormalizedInverseBankBounds
open SemiprimeD1StackRecoveryWeightsWidths
open SemiprimeRationalBits (RationalWord)
/-- All actual boundary words are bounded independently; large retained output is explicitly charged. -/
theorem outer_bound (inverse powers:List RationalWord) (scalar:RationalWord) (q:Nat) (width:List Bool)
    (remaining:Nat) (out:List Bool) (s:Nat) (_hs:1 ≤ s) (hw:width.length ≤ s)
    (hi:(SemiprimeD1StackNormalizedInverse.tape inverse).length ≤ s)
    (hp:(SemiprimeD1StackNormalizedInverse.tape powers).length ≤ s) (hq:q ≤ s) (hr:remaining ≤ s)
    (ho:out.length ≤ 14*s^2):BoundedBank (outer inverse powers scalar q width remaining out).toWords s (5*s) (14*s^2):=by
  have hs2:s ≤ s^2:=Nat.le_pow (by decide:0<2)
  refine ⟨?_,fun _ _=>Nat.zero_le _,?_⟩
  · intro k
    change (if k=SemiprimeD1StackRationalOperation.aux .template then width else []).length ≤ s
    split
    · exact hw
    · exact Nat.zero_le _
  · intro k
    cases k <;> simp only [outer,unary,List.length_replicate,List.length_nil] <;> nlinarith only [hs2,hi,hp,hq,hr,ho]
/-- The actual three copied/decreasing counters remain bounded; accumulator widths come only from real fits/literal ZERO. -/
theorem indexed_bound (w:Words) (s:Nat) (hs:1 ≤ s) (h:BoundedBank w.toWords s (5*s) (14*s^2))
    (terms a b:Nat) (ht:terms ≤ s) (ha:a ≤ s) (hb:b ≤ s) (word:RationalWord) (hw:B.bytes word ≤ 5*s):
    BoundedBank (indexed w terms a b word).toWords s (5*s) (14*s^2):=
  SemiprimeD1StackNormalizedInverseStateBounds.indexed_bound w.toWords s hs h terms a b ht ha hb word hw
/-- Uniform own two-read/two-arithmetic/six-drain cap for arbitrary actual array positions. -/
theorem pairBound_le (w:Words) (inverse powers:List RationalWord) (a b:Nat) (width:List Bool)
    (s:Nat) (hs:1 ≤ s) (hw:width.length ≤ s)
    (hi:(SemiprimeD1StackNormalizedInverse.tape inverse).length ≤ s)
    (hp:(SemiprimeD1StackNormalizedInverse.tape powers).length ≤ s) (ha:a ≤ s) (hb:b ≤ s)
    (hbank:BoundedBank w.toWords s (5*s) (14*s^2)):
    SemiprimeD1StackRecoveryWeightsPair.timeBound w inverse powers a b width ≤ 10^37*s^6:=by
  let x:=SemiprimeD1StackNormalizedInverseSpec.readWord inverse a
  let y:=SemiprimeD1StackNormalizedInverseSpec.readWord powers b
  have hx:B.bytes x ≤ 5*s:=by have h:=B.read_bytes inverse a;dsimp only [x];omega
  have hy:B.bytes y ≤ 5*s:=by have h:=B.read_bytes powers b;dsimp only [y];omega
  have hboth:BoundedBank (SemiprimeD1StackNormalizedInversePairSpec.readPair w.toWords x y) s (5*s) (14*s^2):=
    put_bound _ _ _ _ (put_bound w.toWords _ _ _ hbank .left x hx) .right y hy
  have hproduct:BoundedBank (SemiprimeD1StackNormalizedInversePairSpec.multiplied w.toWords x y width) s (5*s) (14*s^2):=
    after_bound .product _ width _ _ _ hboth (by omega)
  have hsum:BoundedBank (SemiprimeD1StackNormalizedInversePairSpec.added w.toWords x y width) s (5*s) (14*s^2):=
    after_bound .sum _ width _ _ _ hproduct (by omega)
  have hc0:=SemiprimeD1StackNormalizedInversePairBounds.small_call .product _ width s hs hw hboth
  have hc1:=SemiprimeD1StackNormalizedInversePairBounds.small_call .sum _ width s hs hw hproduct
  have hm:=SemiprimeD1StackNormalizedInverseStateBounds.mass_small _ s hs hsum
  have hr0:=SemiprimeD1StackNormalizedInverseReadCall.helperTime_le inverse a
  have hr1:=SemiprimeD1StackNormalizedInverseReadCall.helperTime_le powers b
  have hs6:s ≤ s^6:=Nat.le_pow (by decide:0<6)
  have hs26:s^2 ≤ s^6:=Nat.pow_le_pow_right hs (by decide:2 ≤ 6)
  have h16:1 ≤ s^6:=Nat.one_le_pow _ _ hs
  change (_+3)+(_+3)+SemiprimeD1StackNormalizedInverseOperationCall.callBound .product
    (SemiprimeD1StackNormalizedInversePairSpec.readPair w.toWords x y) width+
    SemiprimeD1StackNormalizedInverseOperationCall.callBound .sum
    (SemiprimeD1StackNormalizedInversePairSpec.multiplied w.toWords x y width) width+
    6*(SemiprimeD1StackNormalizedInverseCleanup.mass (Old.store
      (SemiprimeD1StackNormalizedInversePairSpec.added w.toWords x y width))+1) ≤ _
  nlinarith only [hc0,hc1,hm,hr0,hr1,hi,hp,ha,hb,hs6,hs26,h16]
end RiemannGaussian.SemiprimeD1StackRecoveryWeightsBankBounds
