/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackKernelLinearExecution
import RiemannGaussian.SemiprimeD1StackKernelLinearMeaning
import RiemannGaussian.SemiprimeD1WireKernelOriginal
/-! # Actual original-grid words and exact cancelled normalized-factor bytes -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackKernelLinearOriginalFields
open SemiprimeD1StackKernelLinear SemiprimeBitArithmetic
namespace Acq
export SemiprimeD1StackKernelLinearAcquisition (readyWords sumWords displacementWords gridWords)
end Acq
namespace Spec
export SemiprimeD1StackKernelLinearSpec (fit_digits cancelled_digits alpha_word factor)
end Spec
namespace Exec
export SemiprimeD1StackKernelLinearExecution (result ready_clean)
end Exec
/-- The original cancelled factor used by kernel-entry and mode-scalar acquisition. -/
def originalFactor (a:Nat) (t:Fin (2^(a+1))) (x y:Fin (2^a)):SemiprimeD1NormalizedLinearBits.Run:=
  Spec.factor (a+1) (SemiprimeEncodedRowSelection.digits (a+1) t.val).bits
    (SemiprimeEncodedRowSelection.digits (a+1) (SemiprimeD1WireKernelOriginal.displacement a x y).val).bits
/-- All three physical normalization operands are the exact original acquired words. -/
theorem ready_fields (a:Nat) (t:Fin (2^(a+1))) (x y:Fin (2^a)) (tw xw yw:List Bool)
    (ht:bitValue tw=t.val) (hx:bitValue xw=x.val) (hy:bitValue yw=y.val):
    (Acq.readyWords (List.replicate a true) tw xw yw).j=(SemiprimeEncodedRowSelection.digits (a+1) t.val).bits ∧
    (Acq.readyWords (List.replicate a true) tw xw yw).displacement=
      (SemiprimeEncodedRowSelection.digits (a+1) (SemiprimeD1WireKernelOriginal.displacement a x y).val).bits ∧
    (Acq.readyWords (List.replicate a true) tw xw yw).alpha=(SemiprimeD1NormalizedLinearBits.alpha (a+1)).bits:=by
  constructor
  · change SemiprimeD1StackKernelLinearSpec.fit tw (a+1)=_
    simpa only [ht] using Spec.fit_digits tw (a+1) (by rw [ht];exact t.isLt)
  · constructor
    · have h:=Spec.cancelled_digits a xw yw (by rw [hx];exact x.isLt) (by rw [hy];exact y.isLt)
      rw [hx,hy] at h
      simpa only [Acq.readyWords,Acq.gridWords,Acq.displacementWords,Acq.sumWords,
        SemiprimeD1StackKernelLinearPower.result,SemiprimeD1StackKernelLinearView.sourceWords,
        SemiprimeD1StackKernelLinearFit.displacement,SemiprimeD1StackWordFitExecution.result,
        SemiprimeD1StackKernelLinearSum.value,SemiprimeD1StackKernelLinearSpec.cancelled,
        SemiprimeD1StackKernelLinearSpec.displaced,SemiprimeD1StackKernelLinearSpec.sum,
        SemiprimeD1StackKernelLinearSpec.fit,SemiprimeD1StackKernelLinearSpec.width,List.length_replicate,List.replicate_succ,
        SemiprimeD1WireKernelOriginal.displacement] using h
    · change (false::SemiprimeD1StackKernelLinearSpec.power (List.replicate a true).length)=_
      rw [List.length_replicate,Spec.alpha_word]
      rfl
/-- EACH observed raw factor field matches the original routine, prior to any integer interpretation. -/
theorem output_fields (a:Nat) (t:Fin (2^(a+1))) (x y:Fin (2^a)) (tw xw yw:List Bool)
    (ht:bitValue tw=t.val) (hx:bitValue xw=x.val) (hy:bitValue yw=y.val):
    Exec.result (List.replicate a true) tw xw yw (aux .content)=(originalFactor a t x y).content ∧
    Exec.result (List.replicate a true) tw xw yw (aux .sign)=[(originalFactor a t x y).constant.negative] ∧
    Exec.result (List.replicate a true) tw xw yw (aux .constant)=(originalFactor a t x y).constant.magnitude ∧
    Exec.result (List.replicate a true) tw xw yw (aux .slope)=(originalFactor a t x y).slope:=by
  have h:=ready_fields a t x y tw xw yw ht hx hy
  have hf:=SemiprimeD1StackKernelLinearMeaning.factor_fields
    (Acq.readyWords (List.replicate a true) tw xw yw) (Exec.ready_clean _ _ _ _) (a+1) h.2.2
  rw [h.1,h.2.1] at hf
  exact hf
/-- All four original physical source words survive the entire actual routine literally. -/
theorem originals_retained (a t x y:List Bool):
    Exec.result a t x y (aux .a)=a ∧ Exec.result a t x y (aux .t)=t ∧
    Exec.result a t x y (aux .x)=x ∧ Exec.result a t x y (aux .y)=y:=by
  unfold Exec.result SemiprimeD1StackKernelLinearNormalize.result
  split <;> exact ⟨rfl,rfl,rfl,rfl⟩
end RiemannGaussian.SemiprimeD1StackKernelLinearOriginalFields
