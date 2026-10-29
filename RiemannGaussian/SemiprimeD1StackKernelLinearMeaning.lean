/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackKernelLinearNormalize
/-! # Byte-exact original normalized-factor identification
No old report clock is used. The signed constant, dyadic content and quotient
are identified individually before any interpreted integer equality.
-/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackKernelLinearMeaning
open SemiprimeD1StackKernelLinearView
open SemiprimeBitArithmetic SemiprimeBitDivision SemiprimeBitIndexClipping
open SemiprimeD1RecoveryIntegerBits
namespace Spec
export SemiprimeD1StackKernelLinearSpec
  (factor magnitude negative odd power difference_word strip_bytes content_positive quotient_bytes odd_empty_iff negative_zero)
end Spec
namespace Norm
export SemiprimeD1StackKernelLinearNormalize (Clean result mag signed scanned zeroed prepared divided)
end Norm
/-- Physical nonzero testing is fixed by the actual stripped suffix, not supplied advice. -/
theorem nonzero_of_suffix (xs:List Bool) (h:Spec.odd xs≠[]):(nonzeroBits xs).nonzero=true:=by
  apply (nonzeroBits_correct xs).mpr
  have hn:bitValue xs≠0:=fun hz=>h ((Spec.odd_empty_iff xs).mpr hz)
  omega
/-- Physical all-zero testing sees every original padding bit. -/
theorem zero_of_suffix (xs:List Bool) (h:Spec.odd xs=[]):(nonzeroBits xs).nonzero=false:=by
  have hz:bitValue xs=0:=(Spec.odd_empty_iff xs).mp h
  cases hn:(nonzeroBits xs).nonzero with
  | false=>rfl
  | true=>have hp:=(nonzeroBits_correct xs).mp hn;omega
/-- Literal original zero-normalization branch, including exact signed zero and ONE slope. -/
theorem native_zero (exponent:Nat) (j d:List Bool) (hz:Spec.odd (Spec.magnitude j d)=[]):
    (Spec.factor exponent j d).content=(SemiprimeD1NormalizedLinearBits.alpha exponent).bits ∧
    (Spec.factor exponent j d).constant=positive [] ∧ (Spec.factor exponent j d).slope=[true]:=by
  have ht:=zero_of_suffix (Spec.magnitude j d) hz
  dsimp only [Spec.factor,SemiprimeD1NormalizedLinearBits.acquire]
  rw [Spec.difference_word]
  simp only [ht,Bool.false_eq_true,ite_false,and_self]
/-- Literal original nonzero branch retains the exact padded odd suffix and full quotient. -/
theorem native_nonzero (exponent:Nat) (j d:List Bool) (hn:Spec.odd (Spec.magnitude j d)≠[]):
    (Spec.factor exponent j d).content=Spec.power (SemiprimeD1StackKernelLinearSpec.leading (Spec.magnitude j d)) ∧
    (Spec.factor exponent j d).constant=⟨Spec.negative j d,Spec.odd (Spec.magnitude j d)⟩ ∧
    (Spec.factor exponent j d).slope=
      (divideLoop (SemiprimeD1NormalizedLinearBits.alpha exponent).bits
        (Spec.power (SemiprimeD1StackKernelLinearSpec.leading (Spec.magnitude j d)))).quotient:=by
  have ht:=nonzero_of_suffix (Spec.magnitude j d) hn
  have hc:=Spec.content_positive (Spec.magnitude j d)
  have hd:=Spec.quotient_bytes (SemiprimeD1NormalizedLinearBits.alpha exponent).bits
    (SemiprimeD1RecoveryStripBits.acquire (Spec.magnitude j d)).content hc
  dsimp only [Spec.factor,SemiprimeD1NormalizedLinearBits.acquire]
  rw [Spec.difference_word]
  simp only [ht,ite_true]
  rw [hd,(Spec.strip_bytes (Spec.magnitude j d)).1,(Spec.strip_bytes (Spec.magnitude j d)).2]
  exact ⟨rfl,rfl,rfl⟩
/-- All four observed raw factor fields agree with the original acquire routine.
The only alpha premise describes the actual acquired binary shifted-one cache. -/
theorem factor_fields (w:Words) (hc:Norm.Clean w) (exponent:Nat)
    (ha:w.alpha=(SemiprimeD1NormalizedLinearBits.alpha exponent).bits):
    (Norm.result w).content=(Spec.factor exponent w.j w.displacement).content ∧
    (Norm.result w).sign=[(Spec.factor exponent w.j w.displacement).constant.negative] ∧
    (Norm.result w).constant=(Spec.factor exponent w.j w.displacement).constant.magnitude ∧
    (Norm.result w).slope=(Spec.factor exponent w.j w.displacement).slope:=by
  have hconstant:w.constant=[]:=hc .constant (by simp)
  by_cases hz:Spec.odd (Norm.mag w)=[]
  · have hf:=native_zero exponent w.j w.displacement hz
    have hs:=Spec.negative_zero w.j w.displacement ((Spec.odd_empty_iff (Norm.mag w)).mp hz)
    simp only [Norm.result,hz,ite_true]
    rw [hf.1,hf.2.1,hf.2.2]
    simp only [Norm.zeroed,Norm.scanned,Norm.signed,SemiprimeD1StackKernelLinearScan.result,
      SemiprimeD1StackKernelLinearFinish.result,Norm.mag,hs,hconstant,positive,ha,and_self]
  · have hf:=native_nonzero exponent w.j w.displacement hz
    simp only [Norm.result,hz,ite_false]
    rw [hf.1,hf.2.1,hf.2.2]
    simp only [Norm.divided,Norm.prepared,Norm.scanned,Norm.signed,SemiprimeD1StackKernelLinearScan.result,
      SemiprimeD1StackKernelLinearFinish.result,SemiprimeD1StackKernelLinearTail.quotient,Norm.mag,ha,and_self]
end RiemannGaussian.SemiprimeD1StackKernelLinearMeaning
