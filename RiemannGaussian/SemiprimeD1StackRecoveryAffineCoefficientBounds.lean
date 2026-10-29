/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackRecoveryAffineInnerBounds
import RiemannGaussian.SemiprimeD1StackRecoveryAffineLoopCaps
/-! # Same actual complete coefficient source has a bounded physical-index clock -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackRecoveryAffineCoefficientBounds
open SemiprimeD1StackRecoveryAffineView SemiprimeD1StackRecoveryAffineWordCaps
open SemiprimeD1StackRecoveryAffineByteCaps (Small)
/-- One complete coefficient uses its actual (n+1) ordered pairs with the same fixed resource cap. -/
def cap (B L:Nat):Nat:=10^40*(112*L+B^6+1)
/-- Actual copied index, every dot step, retained-source frames and both drains are charged by the same source budget. -/
theorem source_le (w:Words) (xs:List SemiprimeRationalBits.RationalWord) (c:SemiprimeRationalBits.RationalWord)
    (width:List Bool) (n:Nat) (next:List Bool) (B L:Nat)
    (hW:width.length+2≤ B) (hBL:B≤ L) (hr:Registers w B) (hd:Data w L)
    (hxs:∀x∈xs,Small width x) (hc:Small width c)
    (ha:(vector xs).length≤ L) (hn:n≤ L) (ht:next.length≤ L):
    SemiprimeD1StackRecoveryAffineCoefficient.runBound w xs c width n next≤ (n+1)*cap B L:=by
  let base:=SemiprimeD1StackRecoveryAffineCoefficientBuffers.buffers w
    (SemiprimeD1StackRecoveryAffineReadCount.unary n) next
  have hb:Data base L:=SemiprimeD1StackRecoveryAffineLoopCaps.coefficient_data w _ next L hd
    (by simpa only [SemiprimeD1StackRecoveryAffineReadCount.unary,List.length_replicate] using hn) ht
  have hi:=SemiprimeD1StackRecoveryAffineInnerBounds.loop_le .unit base xs n c SemiprimeRationalBits.zeroWord width B L
    hW hBL hr hb hxs hc (SemiprimeD1StackRecoveryAffineByteCaps.zero_small width) ha hn
  have hsmall:=SemiprimeD1StackRecoveryAffineByteCaps.coefficient_small width xs c n
  have ha0:(signed (SemiprimeD1StackRecoveryAffineCoefficient.answer xs c width n)).length+
      (SemiprimeD1StackRecoveryAffineCoefficient.answer xs c width n).denominator.length≤ 2*B:=by
    change (SemiprimeD1StackRecoveryAffineCoefficient.answer xs c width n).numerator.magnitude.length+1+
      (SemiprimeD1StackRecoveryAffineCoefficient.answer xs c width n).denominator.length≤ 2*B
    have hn0:=hsmall.1
    have hd0:=hsmall.2
    omega
  have hpow:B≤ B^6:=Nat.le_pow (by decide:0<6)
  have hover:(5*n+6)+7*((signed (SemiprimeD1StackRecoveryAffineCoefficient.answer xs c width n)).length+
      (SemiprimeD1StackRecoveryAffineCoefficient.answer xs c width n).denominator.length)+13≤
      SemiprimeD1StackRecoveryAffineInnerBounds.cap B L:=by
    unfold SemiprimeD1StackRecoveryAffineInnerBounds.cap
    omega
  have hmul:SemiprimeD1StackRecoveryAffineInnerBounds.cap B L≤ (n+1)*SemiprimeD1StackRecoveryAffineInnerBounds.cap B L:=by
    simpa only [Nat.one_mul] using Nat.mul_le_mul_right (SemiprimeD1StackRecoveryAffineInnerBounds.cap B L) (by omega:1≤ n+1)
  have hcap:2*SemiprimeD1StackRecoveryAffineInnerBounds.cap B L≤ cap B L:=by
    unfold SemiprimeD1StackRecoveryAffineInnerBounds.cap cap
    omega
  calc
    _≤ (n+1)*SemiprimeD1StackRecoveryAffineInnerBounds.cap B L+
        SemiprimeD1StackRecoveryAffineInnerBounds.cap B L:=by
      dsimp only [base] at hi
      unfold SemiprimeD1StackRecoveryAffineCoefficient.runBound
      omega
    _≤ (n+1)*SemiprimeD1StackRecoveryAffineInnerBounds.cap B L+
        (n+1)*SemiprimeD1StackRecoveryAffineInnerBounds.cap B L:=Nat.add_le_add_left hmul _
    _=(n+1)*(2*SemiprimeD1StackRecoveryAffineInnerBounds.cap B L):=by ring
    _≤ (n+1)*cap B L:=Nat.mul_le_mul_left _ hcap
end RiemannGaussian.SemiprimeD1StackRecoveryAffineCoefficientBounds
