/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackNormalizedInverseInnerBounds
import RiemannGaussian.SemiprimeD1StackNormalizedInverseNegateBounds
import RiemannGaussian.SemiprimeD1StackNormalizedInverseCoefficient
/-! # Whole actual inverse-coefficient clock from only source byte and marker capacities -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackNormalizedInverseCoefficientBounds
open SemiprimeD1StackNormalizedInverse SemiprimeD1StackNormalizedInverseView
open SemiprimeD1StackNormalizedInverseWidths SemiprimeD1StackNormalizedInverseBankBounds
open SemiprimeD1StackNormalizedInverseStateBounds SemiprimeD1StackNormalizedInverseInnerBounds
open SemiprimeD1StackNormalizedInverseNegateBounds SemiprimeD1StackNormalizedInverseCoefficient
open SemiprimeD1StackNormalizedInverseRecurrence
/-- Actual three count copies, n real pair steps, negation, both Frames and all register drains have one fixed-degree cap. -/
theorem coefficientBound_le (w : Words) (a reversed : List SemiprimeRationalBits.RationalWord) (width : List Bool)
    (s : ℕ) (hs : 1 ≤ s) (hw : width.length ≤ s) (ha : (tape a).length ≤ s)
    (hp : (tape reversed).length ≤ 14*s^2) (hbank : BoundedBank w s (5*s) (14*s^2))
    (hprefix : ∀word∈reversed,bytes word ≤ 5*s) (n : ℕ) (hn : n ≤ s) :
    coefficientBound w a reversed width n ≤ 10^39*s^7 := by
  have hinner:=innerBound_le w a reversed width s hs hw ha hp hbank hprefix n hn SemiprimeRationalBits.zeroWord
    (by rw [zero_bytes];omega)
  let dot:=dotLoop width a.toArray reversed n SemiprimeRationalBits.zeroWord
  have hdot : bytes dot ≤ 5*s := by
    have hh:=dotLoop_bytes width a.toArray reversed n SemiprimeRationalBits.zeroWord (by rw [zero_bytes];omega)
    dsimp only [dot]
    omega
  have hreg:=put_bound w _ _ _ hbank .acc dot hdot
  have hneg:=negateBound_le (putReg w .acc dot) width s hs hw hreg
  have hs7:s ≤ s^7:=Nat.le_pow (by decide:0<7)
  have hs67:s^6 ≤ s^7:=Nat.pow_le_pow_right hs (by decide:6≤7)
  have hp7:1 ≤ s^7:=Nat.one_le_pow _ _ hs
  unfold coefficientBound
  change 15*n+15+SemiprimeD1StackNormalizedInverseInner.innerBound w a reversed width n SemiprimeRationalBits.zeroWord+
    SemiprimeD1StackNormalizedInverseNegate.negateBound (putReg w .acc dot) width ≤ _
  nlinarith only [hinner,hneg,hn,hs7,hs67,hp7]
/-- Instantiate the actual cached-prefix invariant; no cached answer, fits or q budget is an extra source operand. -/
theorem original_coefficient (a : List SemiprimeRationalBits.RationalWord) (q : ℕ) (width : List Bool)
    (remaining n : ℕ) (hr : remaining ≤ q) (hn : n ≤ q) :
    coefficientBound (SemiprimeD1StackNormalizedInverseOuterView.outer a q width remaining n
      (SemiprimeNormalizedInverseBits.build width a.toArray n).words.toList.reverse) a
      (SemiprimeNormalizedInverseBits.build width a.toArray n).words.toList.reverse width n ≤
        10^39*(inputSize a q width)^7 := by
  let s:=inputSize a q width
  have hs:=inputSize_caps a q width
  have hs2:s ≤ s^2:=Nat.le_pow (by decide:0<2)
  have hprefix:=prefix_le a q width n hn
  have hbank:=outer_bound a q width remaining n
    (SemiprimeNormalizedInverseBits.build width a.toArray n).words.toList.reverse s (5*s) (14*s^2)
    hs.2.2.2 (by nlinarith only [hs.2.1,hs2]) (by nlinarith only [hs.2.2.1,hs2])
    (by nlinarith only [hr,hs.2.2.1,hs2]) (by nlinarith only [hn,hs.2.2.1,hs2]) hprefix
    (by nlinarith only [hs.1,hs2])
  exact coefficientBound_le _ a _ width s hs.1 hs.2.2.2 hs.2.1 hprefix hbank
    (cached_words a q width n) n (hn.trans hs.2.2.1)
end RiemannGaussian.SemiprimeD1StackNormalizedInverseCoefficientBounds
