/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackKernelLinearStorage
import RiemannGaussian.SemiprimeD1StackKernelLinearOriginalFields
/-! # Same physical original-factor run and interpreted original normalization
The exact individual raw fields are established before interpreting them. Both
entries use their own clocks; the child jet and entire kernel remain later work.
-/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackKernelLinearOriginal
open SemiprimeD1StackKernelLinear SemiprimeD1StackKernelLinearExecution
open SemiprimeD1StackKernelLinearBounds SemiprimeD1StackKernelLinearOriginalFields
open SemiprimeBitArithmetic SemiprimeD1WireKernelFactors
/-- The original normalized constant is interpreted only after its exact acquired bytes. -/
theorem constant_value (a:Nat) (t:Fin (2^(a+1))) (x y:Fin (2^a)):
    (originalFactor a t x y).constant.value=
      (normalizedFactor (a+1) t.val (SemiprimeD1WireKernelOriginal.displacement a x y).val).constant:=by
  have h:=SemiprimeD1NormalizedLinearBits.acquire_constant (a+1)
    (SemiprimeEncodedRowSelection.digits (a+1) t.val).bits
    (SemiprimeEncodedRowSelection.digits (a+1) (SemiprimeD1WireKernelOriginal.displacement a x y).val).bits
  rw [SemiprimeEncodedRowSelection.digits_value _ _ t.isLt,
    SemiprimeEncodedRowSelection.digits_value _ _ (SemiprimeD1WireKernelOriginal.displacement a x y).isLt] at h
  exact h
/-- The actual padded quotient has the original exact slope value. -/
theorem slope_value (a:Nat) (t:Fin (2^(a+1))) (x y:Fin (2^a)):
    (bitValue (originalFactor a t x y).slope:ℤ)=
      (normalizedFactor (a+1) t.val (SemiprimeD1WireKernelOriginal.displacement a x y).val).slope:=by
  have ht:=SemiprimeEncodedRowSelection.digits_value (a+1) t.val t.isLt
  have hd:=SemiprimeEncodedRowSelection.digits_value (a+1)
    (SemiprimeD1WireKernelOriginal.displacement a x y).val (SemiprimeD1WireKernelOriginal.displacement a x y).isLt
  have h:=SemiprimeD1NormalizedLinearBits.acquire_slope (a+1)
    (SemiprimeEncodedRowSelection.digits (a+1) t.val).bits
    (SemiprimeEncodedRowSelection.digits (a+1) (SemiprimeD1WireKernelOriginal.displacement a x y).val).bits
    (by rw [ht];exact t.isLt) (by rw [hd];exact (SemiprimeD1WireKernelOriginal.displacement a x y).isLt)
  rw [ht,hd] at h
  exact h
/-- Acquired dyadic content has the exact original normalization exponent. -/
theorem content_value (a:Nat) (t:Fin (2^(a+1))) (x y:Fin (2^a)):
    bitValue (originalFactor a t x y).content=
      2^factorOrder (a+1) t.val (SemiprimeD1WireKernelOriginal.displacement a x y).val:=by
  have h:=SemiprimeD1NormalizedLinearBits.acquire_content (a+1)
    (SemiprimeEncodedRowSelection.digits (a+1) t.val).bits
    (SemiprimeEncodedRowSelection.digits (a+1) (SemiprimeD1WireKernelOriginal.displacement a x y).val).bits
  rw [SemiprimeEncodedRowSelection.digits_value _ _ t.isLt,
    SemiprimeEncodedRowSelection.digits_value _ _ (SemiprimeD1WireKernelOriginal.displacement a x y).isLt] at h
  exact h
/-- The literal accepted marker is produced on every original valid grid input. -/
theorem accepted (a t x y:List Bool):result a t x y (aux .valid)=[true]:=by
  unfold result SemiprimeD1StackKernelLinearNormalize.result
  split <;> rfl
/-- All real divider roles are physically empty after either normalization branch. -/
theorem divider_clear (a t x y:List Bool) (role:SemiprimeD1StackDivider.Stack):result a t x y (divider role)=[]:=rfl
/-- Original-only physical source, exact four raw factor fields and source retention hold together. -/
theorem source_run_original (a:Nat) (t:Fin (2^(a+1))) (x y:Fin (2^a)) (tw xw yw:List Bool)
    (ht:bitValue tw=t.val) (hx:bitValue xw=x.val) (hy:bitValue yw=y.val):
    ∃q ≤ polynomial (List.replicate a true) tw xw yw,
      SemiprimeD1StackCalls.run program q (initial (List.replicate a true) tw xw yw)=
        some (done (List.replicate a true) tw xw yw) ∧
      result (List.replicate a true) tw xw yw (aux .content)=(originalFactor a t x y).content ∧
      result (List.replicate a true) tw xw yw (aux .sign)=[(originalFactor a t x y).constant.negative] ∧
      result (List.replicate a true) tw xw yw (aux .constant)=(originalFactor a t x y).constant.magnitude ∧
      result (List.replicate a true) tw xw yw (aux .slope)=(originalFactor a t x y).slope:=by
  obtain ⟨q,hq,hr⟩:=source_run_bounded (List.replicate a true) tw xw yw
    (by rw [List.length_replicate,hx];exact x.isLt)
  exact ⟨q,hq,hr,output_fields a t x y tw xw yw ht hx hy⟩
/-- SAME actually acquired-cache continuation has identical raw original fields with no frontdoor replay. -/
theorem ready_run_original (a:Nat) (t:Fin (2^(a+1))) (x y:Fin (2^a)) (tw xw yw:List Bool)
    (ht:bitValue tw=t.val) (hx:bitValue xw=x.val) (hy:bitValue yw=y.val):
    ∃q ≤ polynomial (List.replicate a true) tw xw yw,
      SemiprimeD1StackCalls.run program q (ready (List.replicate a true) tw xw yw)=
        some (done (List.replicate a true) tw xw yw) ∧
      result (List.replicate a true) tw xw yw (aux .content)=(originalFactor a t x y).content ∧
      result (List.replicate a true) tw xw yw (aux .sign)=[(originalFactor a t x y).constant.negative] ∧
      result (List.replicate a true) tw xw yw (aux .constant)=(originalFactor a t x y).constant.magnitude ∧
      result (List.replicate a true) tw xw yw (aux .slope)=(originalFactor a t x y).slope:=by
  obtain ⟨q,hq,hr⟩:=ready_run_bounded (List.replicate a true) tw xw yw
  exact ⟨q,hq,hr,output_fields a t x y tw xw yw ht hx hy⟩
end RiemannGaussian.SemiprimeD1StackKernelLinearOriginal
