/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackRecoveryAffineWordCaps
import RiemannGaussian.SemiprimeD1StackRecoveryAffineSite
/-! # Semantic fitted cache and actual foreign-word caps across arithmetic/cleanup boundaries -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackRecoveryAffineStateCaps
open SemiprimeD1StackRecoveryAffine SemiprimeD1StackRecoveryAffineView
open SemiprimeD1StackRecoveryAffineWordCaps
open SemiprimeD1StackRecoveryGrid (Reg)
/-- Every actual scalar-site answer has exactly the two physically fitted W-byte fields. -/
theorem answer_lengths (site:Site) (w:Words) (width:List Bool):
    (SemiprimeD1StackRecoveryAffineSite.answer site w width).numerator.magnitude.length=width.length ∧
    (SemiprimeD1StackRecoveryAffineSite.answer site w width).denominator.length=width.length:=
  SemiprimeD1StackRecoveryGridByteBounds.operation_lengths _ _ _ width
/-- Actual written scalar caches preserve the same semantic register bound; high old metadata is untouched. -/
theorem site_registers (site:Site) (w:Words) (width:List Bool) (B:Nat)
    (hw:Registers w B) (hW:width.length+1≤B):Registers (SemiprimeD1StackRecoveryAffineSite.result site w width) B:=by
  obtain ⟨hn,hd⟩:=answer_lengths site w width
  exact put_registers w _ _ B hw (by omega) (by omega)
/-- Every foreign tape, shadow and retained array remains within the same physical data cap. -/
theorem site_data (site:Site) (w:Words) (width:List Bool) (L:Nat)
    (hw:Data w L) (hW:width.length+1≤L):Data (SemiprimeD1StackRecoveryAffineSite.result site w width) L:=by
  obtain ⟨hn,hd⟩:=answer_lengths site w width
  exact put_data w _ _ L hw (by omega) (by omega)
/-- Physical EOF drains only shrink the selected actual cache pair. -/
theorem empty_registers (w:Words) (r:Reg) (B:Nat) (hw:Registers w B):
    Registers (SemiprimeD1StackRecoveryAffineOperationOutput.emptyReg w r) B:=by
  intro q b
  by_cases he:q=r
  · subst q
    cases b <;> simp [SemiprimeD1StackRecoveryAffineOperationOutput.emptyReg]
  · change (Function.update (Function.update w.registers (r,false) []) (r,true) [] (q,b)).length≤B
    simp only [Function.update_apply,Prod.mk.injEq,he,false_and,ite_false]
    exact hw q b
/-- The two actual signed/denominator drains preserve every complete112-word cap. -/
theorem empty_data (w:Words) (r:Reg) (L:Nat) (hw:Data w L):
    Data (SemiprimeD1StackRecoveryAffineOperationOutput.emptyReg w r) L:=by
  have h0:=update_le (bank w) (reg r false) [] L hw (Nat.zero_le _)
  rw [update_register] at h0
  have h1:=update_le _ (reg r true) [] L h0 (Nat.zero_le _)
  rw [update_register] at h1
  exact h1
end RiemannGaussian.SemiprimeD1StackRecoveryAffineStateCaps
