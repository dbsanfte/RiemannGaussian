/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackNormalizedInverseStateBounds
import RiemannGaussian.SemiprimeD1StackNormalizedInversePair
/-! # Uniform physical pair-loop bit clock, with all repeated scans and real arithmetic paid -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackNormalizedInversePairBounds
open SemiprimeD1StackNormalizedInverse SemiprimeD1StackNormalizedInverseView
open SemiprimeD1StackNormalizedInverseWidths SemiprimeD1StackNormalizedInverseBankBounds
open SemiprimeD1StackNormalizedInverseStateBounds SemiprimeD1StackNormalizedInverseOperationBounds
open SemiprimeD1StackNormalizedInverseOperationCall SemiprimeD1StackNormalizedInversePairSpec
open SemiprimeD1StackNormalizedInverseReadCall SemiprimeD1StackNormalizedInversePair
open SemiprimeD1StackNormalizedInverseSpec
open SemiprimeD1StackNormalizedInverseCleanup (mass)
/-- Both fitted/ordinary cache fields are charged; foreign prefix bytes remain LINEAR in actual mass. -/
theorem small_call (site : Site) (w : Words) (width : List Bool) (s : ℕ) (hs : 1 ≤ s)
    (hw : width.length ≤ s) (hbank : BoundedBank w s (5*s) (14*s^2)) :
    callBound site w width ≤ 10^36*s^6 := by
  have hc:=callBound_le site w width (5*s) (by omega) (by omega) hbank.2.1
  have hm:=mass_small w s hs hbank
  have hs26:s^2 ≤ s^6:=Nat.pow_le_pow_right hs (by decide:2≤6)
  rw [Nat.mul_pow] at hc
  norm_num at hc ⊢
  nlinarith only [hc,hm,hs26]
/-- Complete actual pair cap includes BOTH physical array scans, two whole R36 calls and six full field drains. -/
theorem pairBound_le (w : Words) (a reversed : List SemiprimeRationalBits.RationalWord) (i : ℕ) (width : List Bool)
    (s : ℕ) (hs : 1 ≤ s) (hw : width.length ≤ s) (ha : (tape a).length ≤ s)
    (hp : (tape reversed).length ≤ 14*s^2) (hi : i ≤ s)
    (hbank : BoundedBank w s (5*s) (14*s^2))
    (hprefix : ∀word∈reversed,bytes word ≤ 5*s) :
    pairBound w a reversed i width ≤ 10^37*s^6 := by
  let x:=readWord a (i+1)
  let y:=readWord reversed i
  have hx : bytes x ≤ 5*s := by
    have hh:=read_bytes a (i+1)
    dsimp only [x]
    omega
  have hy : bytes y ≤ 5*s := read_uniform reversed i (5*s) (by omega) hprefix
  have hboth : BoundedBank (readPair w x y) s (5*s) (14*s^2) :=
    put_bound _ _ _ _ (put_bound w _ _ _ hbank .left x hx) .right y hy
  have hproduct : BoundedBank (multiplied w x y width) s (5*s) (14*s^2) :=
    after_bound .product _ width _ _ _ hboth (by omega)
  have hsum : BoundedBank (added w x y width) s (5*s) (14*s^2) :=
    after_bound .sum _ width _ _ _ hproduct (by omega)
  have hc0:=small_call .product (readPair w x y) width s hs hw hboth
  have hc1:=small_call .sum (multiplied w x y width) width s hs hw hproduct
  have hm:=mass_small (added w x y width) s hs hsum
  have hread0:=helperTime_le a (i+1)
  have hread1:=helperTime_le reversed i
  have hs6:s ≤ s^6:=Nat.le_pow (by decide:0<6)
  have hs26:s^2 ≤ s^6:=Nat.pow_le_pow_right hs (by decide:2≤6)
  have hp6:1 ≤ s^6:=Nat.one_le_pow _ _ hs
  change (helperTime a (i+1)+3)+(helperTime reversed i+3)+callBound .product (readPair w x y) width+
    callBound .sum (multiplied w x y width) width+6*(mass (store (added w x y width))+1) ≤ _
  nlinarith only [hc0,hc1,hm,hread0,hread1,ha,hp,hi,hs6,hs26,hp6]
end RiemannGaussian.SemiprimeD1StackNormalizedInversePairBounds
