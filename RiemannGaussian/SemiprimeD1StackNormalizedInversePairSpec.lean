/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackNormalizedInverseOperationCall
import RiemannGaussian.SemiprimeD1StackNormalizedInverseRegisterAlgebra
import RiemannGaussian.SemiprimeD1StackNormalizedInverseRegisterClear
import RiemannGaussian.SemiprimeD1StackNormalizedInverseSpec
/-! # Exact byte lineage of two parsed operands, product FIRST and the suffix SECOND -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackNormalizedInversePairSpec
open SemiprimeD1StackNormalizedInverse SemiprimeD1StackNormalizedInverseView
open SemiprimeD1StackNormalizedInverseOperationCall SemiprimeD1StackNormalizedInverseRegisterAlgebra
open SemiprimeD1StackNormalizedInverseRegisterClear SemiprimeD1StackNormalizedInverseSpec
/-- Actual register states after paid left and right array reads. -/
def readPair (w : Words) (x y : SemiprimeRationalBits.RationalWord) : Words := putReg (putReg w .left x) .right y
/-- Actual product cache acquired by the real R36 call. -/
def multiplied (w : Words) (x y : SemiprimeRationalBits.RationalWord) (width : List Bool) : Words :=
  after .product (readPair w x y) width
/-- Actual suffix replacement acquired by the second real R36 call. -/
def added (w : Words) (x y : SemiprimeRationalBits.RationalWord) (width : List Bool) : Words :=
  after .sum (multiplied w x y width) width
/-- The physical product uses the exact acquired left/right pair, including arbitrary raw padding. -/
theorem product_bytes (w : Words) (x y : SemiprimeRationalBits.RationalWord) (width : List Bool) :
    acquired .product (readPair w x y) width=(SemiprimeRationalBits.executeOperation .mul x y width).word := by
  change (SemiprimeRationalBits.executeOperation .mul (getReg (readPair w x y) .left)
    (getReg (readPair w x y) .right) width).word=_
  rw [readPair,getReg_put,getReg_other _ .right .left y (by decide),getReg_put]
/-- The actual old suffix is retained through both reads and product acquisition. -/
theorem suffix_bytes (w : Words) (x y : SemiprimeRationalBits.RationalWord) (width : List Bool) :
    getReg (multiplied w x y width) .acc=getReg w .acc := by
  dsimp only [multiplied,after,destination]
  rw [getReg_other _ .product .acc _ (by decide)]
  unfold readPair
  rw [getReg_other _ .right .acc _ (by decide),getReg_other _ .left .acc _ (by decide)]
/-- No add associativity or rational-value substitution is used: product-FIRST and suffix-SECOND bytes are exact. -/
theorem sum_bytes (w : Words) (x y : SemiprimeRationalBits.RationalWord) (width : List Bool) :
    acquired .sum (multiplied w x y width) width=combine width (x,y) (getReg w .acc) := by
  change (SemiprimeRationalBits.executeOperation .add (getReg (multiplied w x y width) .product)
    (getReg (multiplied w x y width) .acc) width).word=_
  rw [suffix_bytes]
  change (SemiprimeRationalBits.executeOperation .add
    (getReg (putReg (readPair w x y) .product (acquired .product (readPair w x y) width)) .product)
    (getReg w .acc) width).word=_
  rw [getReg_put,product_bytes]
  rfl
/-- The six real field drains preserve the acquired accumulator and restore all originally empty parsed/product caches. -/
theorem pair_clear_bytes (w : Words) (x y : SemiprimeRationalBits.RationalWord) (width : List Bool)
    (he : ∀r≠Reg.acc,∀den,w.registers (r,den)=[]) :
    pairClear (added w x y width)=putReg w .acc (combine width (x,y) (getReg w .acc)) := by
  unfold added after
  rw [sum_bytes]
  apply congrArg (fun registers=>({w with registers:=registers}:Words))
  funext k
  rcases k with ⟨r,den⟩
  by_cases hr:r=.acc
  · subst r;cases den <;> simp only [destination,putReg,Function.update_apply,Prod.mk.injEq,
      eq_self,true_and,Bool.false_eq_true,Bool.true_eq_false,ite_true,ite_false]
  · have hw:=he r hr den
    cases den <;> simp only [putReg,Function.update_apply,Prod.mk.injEq,hr,false_and,
      ite_false,hw]
end RiemannGaussian.SemiprimeD1StackNormalizedInversePairSpec
