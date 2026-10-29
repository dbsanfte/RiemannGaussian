/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackRecoveryAffinePair
/-! # Exact ordered scalar bytes after the same actual convolution pair -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackRecoveryAffinePairMeaning
open SemiprimeD1StackRecoveryAffine SemiprimeD1StackRecoveryAffineView
open SemiprimeD1StackRecoveryGrid (Reg)
/-- Replacing a different physical cache does not change the decoded raw word. -/
theorem getReg_other (w:Words) (r q:Reg) (x:SemiprimeRationalBits.RationalWord) (hne:q≠r):
    getReg (putReg w r x) q=getReg w q:=by
  unfold getReg SemiprimeD1StackRecoveryGridView.getReg
  rw [SemiprimeD1StackRecoveryAffineRegisters.putReg_other w r q x false hne,
    SemiprimeD1StackRecoveryAffineRegisters.putReg_other w r q x true hne]
/-- Actual acquired signed operands and suffix, in their fixed physical cache roles. -/
def loaded (w:Words) (x y suffix:SemiprimeRationalBits.RationalWord):Words:=
  putReg (putReg (putReg w .numBase x) .denBase y) .denPower suffix
/-- Exact legacy convolution step retains product FIRST and suffix SECOND, including every zero term. -/
def step (width:List Bool) (x y suffix:SemiprimeRationalBits.RationalWord):SemiprimeRationalBits.RationalWord:=
  (SemiprimeRationalBits.executeOperation .add (SemiprimeRationalBits.executeOperation .mul x y width).word suffix width).word
/-- The physical product site reads exactly the acquired FIRST and SECOND raw word operands. -/
theorem product_answer (w:Words) (x y suffix:SemiprimeRationalBits.RationalWord) (width:List Bool):
    SemiprimeD1StackRecoveryAffineSite.answer .product (loaded w x y suffix) width=
      (SemiprimeRationalBits.executeOperation .mul x y width).word:=by
  simp [SemiprimeD1StackRecoveryAffineSite.answer,loaded,operand,operation,
    getReg_other,getReg_putReg,SemiprimeD1StackRationalOperation.operation]
/-- The physical sum site reads actual product FIRST and retained suffix SECOND. -/
theorem sum_answer (w:Words) (x y suffix:SemiprimeRationalBits.RationalWord) (width:List Bool):
    SemiprimeD1StackRecoveryAffineSite.answer .sum
      (SemiprimeD1StackRecoveryAffineSite.result .product (loaded w x y suffix) width) width=step width x y suffix:=by
  simp [SemiprimeD1StackRecoveryAffineSite.answer,SemiprimeD1StackRecoveryAffineSite.result,
    loaded,operand,operation,destination,getReg_other,getReg_putReg,step,
    SemiprimeD1StackRationalOperation.operation]
/-- After all six actual drains, the complete physical bank differs only by the actual fitted suffix. -/
theorem result_exact (w:Words) (x y suffix:SemiprimeRationalBits.RationalWord) (width:List Bool)
    (hx:∀b,w.registers (.numBase,b)=[]) (hy:∀b,w.registers (.denBase,b)=[])
    (hp:∀b,w.registers (.numPower,b)=[]):
    SemiprimeD1StackRecoveryAffinePair.result (loaded w x y suffix) width=
      putReg w .denPower (step width x y suffix):=by
  unfold SemiprimeD1StackRecoveryAffinePair.result
  change SemiprimeD1StackRecoveryAffineInnerClear.result
    (putReg (SemiprimeD1StackRecoveryAffineSite.result .product (loaded w x y suffix) width) .denPower
      (SemiprimeD1StackRecoveryAffineSite.answer .sum
        (SemiprimeD1StackRecoveryAffineSite.result .product (loaded w x y suffix) width) width))=_
  rw [sum_answer]
  change SemiprimeD1StackRecoveryAffineInnerClear.result
    (putReg (putReg (loaded w x y suffix) .numPower
      (SemiprimeD1StackRecoveryAffineSite.answer .product (loaded w x y suffix) width)) .denPower (step width x y suffix))=_
  rw [product_answer]
  dsimp only [SemiprimeD1StackRecoveryAffineInnerClear.result,SemiprimeD1StackRecoveryAffineOperationOutput.emptyReg,loaded,putReg]
  congr 1
  congr 1
  funext slot
  rcases slot with ⟨r,b⟩
  cases r <;> cases b <;> simp [hx,hy,hp]
end RiemannGaussian.SemiprimeD1StackRecoveryAffinePairMeaning
