/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackRecoveryAffineCleanup
import RiemannGaussian.SemiprimeD1StackRecoveryAffineCache
import RiemannGaussian.SemiprimeD1StackRecoveryGridWordCaps
/-! # Actual112-word boundary caps preserve semantic register widths and all foreign bytes -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackRecoveryAffineWordCaps
open SemiprimeD1StackRecoveryAffine SemiprimeD1StackRecoveryAffineView
open SemiprimeD1StackRecoveryGrid (Reg)
/-- Every original or borrowed signed rational cache has its actual semantic byte cap. -/
def Registers (w:Words) (B:Nat):Prop:=∀r b,(w.registers (r,b)).length≤B
/-- Every112 allocated actual tape, including all added arrays and shadow roles, is counted. -/
def Data (w:Words) (L:Nat):Prop:=∀slot,(bank w slot).length≤L
/-- One actual field write retains the cap of every other111 physical word. -/
theorem update_le (before:Stack→List Bool) (slot:Stack) (xs:List Bool) (L:Nat)
    (h:∀k,(before k).length≤L) (hx:xs.length≤L):∀k,(Function.update before slot xs k).length≤L:=by
  intro k
  by_cases he:k=slot
  · subst k
    simpa only [Function.update_self] using hx
  · rw [Function.update_of_ne he]
    exact h k
/-- Two actual cache writes preserve every unrelated original/additional role. -/
theorem bank_putReg (w:Words) (r:Reg) (x:SemiprimeRationalBits.RationalWord):
    Function.update (Function.update (bank w) (reg r false) (signed x)) (reg r true) x.denominator=bank (putReg w r x):=by
  rw [update_register,update_register]
  rfl
/-- Fitted/literal word widths, rather than elapsed execution, bound each updated scalar register. -/
theorem put_registers (w:Words) (r:Reg) (x:SemiprimeRationalBits.RationalWord) (B:Nat)
    (hw:Registers w B) (hn:x.numerator.magnitude.length+1≤B) (hd:x.denominator.length≤B):Registers (putReg w r x) B:=
  SemiprimeD1StackRecoveryGridWordCaps.put_registers w.toWords r x B hw hn hd
/-- The actual new signed and denominator bytes preserve the complete112-tape cap. -/
theorem put_data (w:Words) (r:Reg) (x:SemiprimeRationalBits.RationalWord) (L:Nat)
    (hw:Data w L) (hn:x.numerator.magnitude.length+1≤L) (hd:x.denominator.length≤L):Data (putReg w r x) L:=by
  have h0:=update_le (bank w) (reg r false) (signed x) L hw hn
  have h1:=update_le (Function.update (bank w) (reg r false) (signed x)) (reg r true) x.denominator L h0 hd
  rw [bank_putReg] at h1
  exact h1
/-- Any actual added-word replacement retains all old104 register fields. -/
theorem added_registers (w:Words) (slot:Aux) (xs:List Bool) (B:Nat) (hw:Registers w B):
    Registers {w with added:=Function.update w.added slot xs} B:=hw
/-- Every newly stored actual counter/vector byte is charged explicitly. -/
theorem added_data (w:Words) (slot:Aux) (xs:List Bool) (L:Nat) (hw:Data w L) (hx:xs.length≤L):
    Data {w with added:=Function.update w.added slot xs} L:=by
  have h:=update_le (bank w) (aux slot) xs L hw hx
  rw [update_added] at h
  exact h
/-- Literal byte-count word replacement preserves the actual whole bank cap. -/
theorem counter_data (w:Words) (n L:Nat) (hw:Data w L) (hn:n≤L):Data (SemiprimeD1StackRecoveryAffineCache.counter w n) L:=by
  apply added_data w .k _ L hw
  simpa only [SemiprimeD1StackRecoveryAffineReadCount.unary,List.length_replicate] using hn
/-- Actual112-word mass pays every allocated data role, with no omitted alias shadow. -/
theorem mass_le (w:Words) (L:Nat) (hw:Data w L):SemiprimeD1StackRecoveryAffineCleanup.mass (bank w)≤112*L:=
  SemiprimeD1StackRecoveryAffineCleanup.word_sum (bank w) L hw
end RiemannGaussian.SemiprimeD1StackRecoveryAffineWordCaps
