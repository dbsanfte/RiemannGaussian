/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackNormalizedInverseOperationCall
import RiemannGaussian.SemiprimeD1StackNormalizedInverseWidths
/-! # Own uniform arithmetic-call bit clock with foreign cache mass charged linearly -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackNormalizedInverseOperationBounds
open SemiprimeD1StackNormalizedInverse SemiprimeD1StackNormalizedInverseView
open SemiprimeD1StackNormalizedInverseOperation SemiprimeD1StackNormalizedInverseOperationInput
open SemiprimeD1StackNormalizedInverseOperationOutput SemiprimeD1StackNormalizedInverseOperationCall
open SemiprimeD1StackNormalizedInverseWidths
open SemiprimeD1StackNormalizedInverseCleanup (mass)
/-- The actual output copies always pay both physically fitted fields and the real sign pop/push. -/
theorem saveTime_le (site : Site) (sx : Bool) (xn xd : List Bool) (sy : Bool) (yn yd width : List Bool) :
    saveTime (word (operation site) sx xn xd sy yn yd width) ≤ 10*width.length+10 := by
  have h : bytes (word (operation site) sx xn xd sy yn yd width)=2*width.length+1 := by
    rw [word_legacy]
    exact execute_bytes _ _ _ width
  simp only [bytes,signed,List.length_cons] at h
  unfold saveTime
  omega
/-- The frozen complete R36 source is used with its OWN proved bit clock; every input copy/drain is added here. -/
theorem prefixTime_le (site : Site) (w : Words) (sx : Bool) (xn xd : List Bool) (sy : Bool) (yn yd width : List Bool)
    (s : ℕ) (hs : 1 ≤ s) (hxn : xn.length ≤ s) (hxd : xd.length ≤ s) (hyn : yn.length ≤ s) (hyd : yd.length ≤ s)
    (hw : width.length ≤ s) (hdn : (w.registers (destination site,false)).length ≤ s)
    (hdd : (w.registers (destination site,true)).length ≤ s) :
    prefixTime site w sx xn xd sy yn yd width ≤ 10^27*s^6 := by
  have hr:=SemiprimeD1StackRationalOperationBounds.runBound_le (operation site) sx xn xd sy yn yd width
  have hsize : SemiprimeD1StackRationalOperationEncoding.inputSize (sx::xn) xd (sy::yn) yd width ≤ 8*s := by
    simp only [SemiprimeD1StackRationalOperationEncoding.inputSize,List.length_cons]
    omega
  have hp : (SemiprimeD1StackRationalOperationEncoding.inputSize (sx::xn) xd (sy::yn) yd width)^6 ≤ (8*s)^6 :=
    Nat.pow_le_pow_left hsize 6
  have hr2 : SemiprimeD1StackRationalOperationExecution.runBound (operation site) sx xn xd sy yn yd width ≤ 10^26*s^6 := by
    unfold SemiprimeD1StackRationalOperationBounds.polynomial at hr
    have hh:=Nat.mul_le_mul_left 100000000000000000000 hp
    rw [Nat.mul_pow] at hh
    norm_num at hh ⊢
    omega
  have hf:=saveTime_le site sx xn xd sy yn yd width
  have hs6:s ≤ s^6:=Nat.le_pow (by decide:0<6)
  have hp6:1 ≤ s^6:=Nat.one_le_pow _ _ hs
  unfold prefixTime inputsTime
  simp only [List.length_cons]
  nlinarith only [hr2,hf,hxn,hxd,hyn,hyd,hw,hdn,hdd,hs6,hp6]
/-- Arithmetic bits are bounded by physical cache widths; foreign prefix/source bytes are charged only linearly. -/
theorem callBound_le (site : Site) (w : Words) (width : List Bool) (s : ℕ)
    (hs : 1 ≤ s) (hw : width.length ≤ s) (hc : ∀r den,(w.registers (r,den)).length ≤ s) :
    callBound site w width ≤ 10^31*(mass (store w)+s^6) := by
  let x:=getReg w (operand site false)
  let y:=getReg w (operand site true)
  have hxn:x.numerator.magnitude.length ≤ s := by
    change (w.registers (operand site false,false)).tail.length ≤ s
    rw [List.length_tail]
    exact (Nat.sub_le _ _).trans (hc _ _)
  have hyn:y.numerator.magnitude.length ≤ s := by
    change (w.registers (operand site true,false)).tail.length ≤ s
    rw [List.length_tail]
    exact (Nat.sub_le _ _).trans (hc _ _)
  have hp:=prefixTime_le site w x.numerator.negative x.numerator.magnitude x.denominator
    y.numerator.negative y.numerator.magnitude y.denominator width s hs hxn (hc _ _) hyn (hc _ _) hw (hc _ _) (hc _ _)
  have hp6:1 ≤ s^6:=Nat.one_le_pow _ _ hs
  change 2100*(mass (store w)+prefixTime site w x.numerator.negative x.numerator.magnitude x.denominator
    y.numerator.negative y.numerator.magnitude y.denominator width+1)+1+3 ≤ _
  nlinarith only [hp,hp6,Nat.zero_le (mass (store w))]
end RiemannGaussian.SemiprimeD1StackNormalizedInverseOperationBounds
