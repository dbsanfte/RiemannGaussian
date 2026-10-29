/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackRecoveryWeightsCleanup
import RiemannGaussian.SemiprimeD1StackNormalizedInversePairSpec
/-! # Actual two-source reads, inverse-FIRST power-SECOND product, suffix-SECOND sum
Both actual source arrays are preserved, including every raw padding byte.
The six real parsed/product drains finish before either actual index is popped.
-/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackRecoveryWeightsPair
open SemiprimeD1StackRecoveryWeights SemiprimeD1StackRecoveryWeightsView
open SemiprimeD1StackRecoveryWeightsCalls SemiprimeD1StackProcedureTrace
namespace Spec
export SemiprimeD1StackNormalizedInverseSpec (readWord combine)
end Spec
namespace Pair
export SemiprimeD1StackNormalizedInversePairSpec (readPair multiplied added product_bytes suffix_bytes sum_bytes pair_clear_bytes)
end Pair
/-- Own summed actual trace cap for BOTH full reads, two complete arithmetic calls and six drains. -/
def timeBound (w:Words) (inverse powers:List SemiprimeRationalBits.RationalWord) (a b:Nat) (width:List Bool):Nat:=
  let x:=Spec.readWord inverse a
  let y:=Spec.readWord powers b
  (SemiprimeD1StackNormalizedInverseReadCall.helperTime inverse a+3)+
    (SemiprimeD1StackNormalizedInverseReadCall.helperTime powers b+3)+
    SemiprimeD1StackNormalizedInverseOperationCall.callBound .product (Pair.readPair w.toWords x y) width+
    SemiprimeD1StackNormalizedInverseOperationCall.callBound .sum (Pair.multiplied w.toWords x y width) width+
    6*(SemiprimeD1StackNormalizedInverseCleanup.mass (Old.store (Pair.added w.toWords x y width))+1)
/-- Entire actual pair execution acquires exact raw right-fold result and physically clears every parsed/product field. -/
theorem pair_run (w:Words) (inverse powers:List SemiprimeRationalBits.RationalWord) (a b:Nat) (width:List Bool)
    (hi:w.auxiliary .denominator=SemiprimeD1StackNormalizedInverse.tape inverse)
    (hp:w.auxiliary .prefixReverse=SemiprimeD1StackNormalizedInverse.tape powers)
    (ha:w.auxiliary .aIndex=List.replicate a true) (hb:w.auxiliary .bIndex=List.replicate b true)
    (hr:w.rational=Old.emptyRational width)
    (he:∀r≠SemiprimeD1StackNormalizedInverse.Reg.acc,∀den,w.registers (r,den)=[])
    (hn:w.registers (.acc,false)≠[])
    (hreader:w.auxiliary .reader=[]) (htodo:w.auxiliary .readTodo=[])
    (hs:w.auxiliary .fieldFrameScratch=[]) (hv:w.auxiliary .valid=[]) (hc:w.auxiliary .copyScratch=[]):
    ∃time ≤ timeBound w inverse powers a b width,
      Runs program time (.local .readInverse) (bank w) (.local .decrementA)
        (bank (replace w (Old.putReg w.toWords .acc
          (Spec.combine width (Spec.readWord inverse a,Spec.readWord powers b) (Old.getReg w.toWords .acc))))):=by
  let x:=Spec.readWord inverse a
  let y:=Spec.readWord powers b
  let first:=replace w (Old.putReg w.toWords .left x)
  let both:=replace w (Pair.readPair w.toWords x y)
  let product:=replace w (Pair.multiplied w.toWords x y width)
  let sum:=replace w (Pair.added w.toWords x y width)
  have h0:=read_call .denominator (.local .readInverse) (.local .checkedInverse) (.local .readPower) rfl rfl
    w inverse a hi ha hreader htodo (he .left (by decide) false) (he .left (by decide) true) hs hv hc
  have h1:=read_call .prefix (.local .readPower) (.local .checkedPower) (.local .product) rfl rfl
    first powers b hp hb hreader htodo
    (by change (Old.putReg w.toWords .left x).registers (.right,false)=[]
        rw [SemiprimeD1StackNormalizedInverseView.putReg_other _ .left .right x false (by decide)];exact he .right (by decide) false)
    (by change (Old.putReg w.toWords .left x).registers (.right,true)=[]
        rw [SemiprimeD1StackNormalizedInverseView.putReg_other _ .left .right x true (by decide)];exact he .right (by decide) true) hs hv hc
  have hx:both.registers (.left,false)≠[]:=by
    change (Pair.readPair w.toWords x y).registers (.left,false)≠[]
    rw [Pair.readPair,SemiprimeD1StackNormalizedInverseView.putReg_other _ .right .left y false (by decide),
      (SemiprimeD1StackNormalizedInverseView.putReg_fields w.toWords .left x).1]
    exact List.cons_ne_nil _ _
  have hy:both.registers (.right,false)≠[]:=by
    change (Old.putReg (Old.putReg w.toWords .left x) .right y).registers (.right,false)≠[]
    rw [(SemiprimeD1StackNormalizedInverseView.putReg_fields (Old.putReg w.toWords .left x) .right y).1]
    exact List.cons_ne_nil _ _
  obtain ⟨m,hm,h2⟩:=operation_call .product (.local .product) (.local .checkedProduct) (.local .sum) rfl rfl both width hr hc hv hx hy
  have hproduct:product.registers (.product,false)≠[]:=by
    change (Old.putReg (Pair.readPair w.toWords x y) .product (SemiprimeD1StackNormalizedInverseOperationCall.acquired .product (Pair.readPair w.toWords x y) width)).registers (.product,false)≠[]
    rw [(SemiprimeD1StackNormalizedInverseView.putReg_fields (Pair.readPair w.toWords x y) .product _).1]
    exact List.cons_ne_nil _ _
  have hacc:product.registers (.acc,false)≠[]:=by
    change (Pair.multiplied w.toWords x y width).registers (.acc,false)≠[]
    change (Old.putReg (Pair.readPair w.toWords x y) .product (SemiprimeD1StackNormalizedInverseOperationCall.acquired .product (Pair.readPair w.toWords x y) width)).registers (.acc,false)≠[]
    rw [SemiprimeD1StackNormalizedInverseView.putReg_other _ .product .acc _ false (by decide)]
    unfold Pair.readPair
    rw [SemiprimeD1StackNormalizedInverseView.putReg_other _ .right .acc y false (by decide),
      SemiprimeD1StackNormalizedInverseView.putReg_other _ .left .acc x false (by decide)]
    exact hn
  obtain ⟨n,hnb,h3⟩:=operation_call .sum (.local .sum) (.local .checkedSum) (.local (.clearPair 0)) rfl rfl product width hr hc hv hproduct hacc
  obtain ⟨z,hz,h4⟩:=SemiprimeD1StackRecoveryWeightsCleanup.pair_run sum
  have hclear:replace sum (SemiprimeD1StackNormalizedInverseRegisterClear.pairClear sum.toWords)=
      replace w (Old.putReg w.toWords .acc (Spec.combine width (x,y) (Old.getReg w.toWords .acc))):=by
    change replace w (SemiprimeD1StackNormalizedInverseRegisterClear.pairClear (Pair.added w.toWords x y width))=_
    rw [Pair.pair_clear_bytes w.toWords x y width he]
  rw [hclear] at h4
  have hh:=P.join (P.join (P.join (P.join h0 h1) h2) h3) h4
  refine ⟨_,?_,hh⟩
  dsimp only [timeBound]
  dsimp only [both,replace] at hm
  dsimp only [product,replace] at hnb
  dsimp only [sum,replace] at hz
  dsimp only [x,y] at hm hnb hz ⊢
  omega
end RiemannGaussian.SemiprimeD1StackRecoveryWeightsPair
