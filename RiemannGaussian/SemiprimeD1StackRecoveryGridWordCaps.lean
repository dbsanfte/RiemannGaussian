/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackRecoveryGridByteBounds
import RiemannGaussian.SemiprimeD1StackRecoveryGridRegisters
/-! # Semantic physical-word caps at actual grid arithmetic boundaries
No operand width is derived from elapsed execution. Fitted words have W bytes,
literal one has one magnitude byte even W0, and all untouched tapes retain
their actual previous byte caps.
-/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackRecoveryGridWordCaps
open SemiprimeD1StackRecoveryGrid SemiprimeD1StackRecoveryGridView SemiprimeD1StackRecoveryGridRegisters
open SemiprimeD1StackRecoveryGridCleanup
/-- Every actual register field, including signs and raw node padding, fits the semantic cache-width cap. -/
def Registers (w:Words) (B:Nat) :Prop:=∀r b,(w.registers (r,b)).length≤ B
/-- Every104 actual data word, including foreign retained slopes and metadata, has an actual physical-byte cap. -/
def Data (w:Words) (L:Nat) :Prop:=∀k,(bank w k).length≤ L
/-- A literal physical write preserves a uniform actual word cap. -/
theorem update_le (data:Stack→List Bool) (k:Stack) (xs:List Bool) (L:Nat)
    (hdata:∀j,(data j).length≤ L) (hx:xs.length≤ L) :∀j,(Function.update data k xs j).length≤ L:=by
  intro j
  by_cases he:j=k
  · subst j
    simpa only [Function.update_self] using hx
  · rw [Function.update_of_ne he]
    exact hdata j
/-- Exact two actual signed/denominator register writes, with every other physical role unchanged. -/
theorem bank_putReg (w:Words) (r:Reg) (x:SemiprimeRationalBits.RationalWord) :
    Function.update (Function.update (bank w) (reg r false) (signed x)) (reg r true) x.denominator=bank (putReg w r x):=by
  rw [update_registers w (r,false),update_registers _ (r,true)]
  rfl
/-- Semantic word widths, rather than prefix-clock estimates, bound every updated register field. -/
theorem put_registers (w:Words) (r:Reg) (x:SemiprimeRationalBits.RationalWord) (B:Nat)
    (hw:Registers w B) (hn:x.numerator.magnitude.length+1≤ B) (hd:x.denominator.length≤ B) :Registers (putReg w r x) B:=by
  intro q b
  by_cases he:q=r
  · subst q
    cases b
    · rw [(putReg_fields w r x).1]
      exact hn
    · rw [(putReg_fields w r x).2]
      exact hd
  · rw [putReg_other w r q x b he]
    exact hw q b
/-- The same two physically updated fields preserve the global104-word cap, including foreign tapes. -/
theorem put_data (w:Words) (r:Reg) (x:SemiprimeRationalBits.RationalWord) (L:Nat)
    (hw:Data w L) (hn:x.numerator.magnitude.length+1≤ L) (hd:x.denominator.length≤ L) :Data (putReg w r x) L:=by
  have h0:=update_le (bank w) (reg r false) (signed x) L hw hn
  have h1:=update_le (Function.update (bank w) (reg r false) (signed x)) (reg r true) x.denominator L h0 hd
  rw [bank_putReg] at h1
  exact h1
/-- A real actual counter/cache write leaves all rational register words intact. -/
theorem auxiliary_registers (w:Words) (k:Aux) (xs:List Bool) (B:Nat) (hw:Registers w B) :
    Registers {w with auxiliary:=Function.update w.auxiliary k xs} B:=hw
/-- Only actual newly emitted auxiliary bytes can enlarge an actual word. -/
theorem auxiliary_data (w:Words) (k:Aux) (xs:List Bool) (L:Nat) (hw:Data w L) (hx:xs.length≤ L) :
    Data {w with auxiliary:=Function.update w.auxiliary k xs} L:=by
  have h:=update_le (bank w) (aux k) xs L hw hx
  rw [update_auxiliary] at h
  exact h
/-- Counted total104-role mass follows from actual retained word caps. -/
theorem mass_le (w:Words) (L:Nat) (hw:Data w L) :mass (bank w)≤104*L:=word_sum _ L hw
/-- Actual power outputs use W bytes per fitted field or the one-byte literal seed; neither expands numerically. -/
theorem power_width (width:List Bool) (x:SemiprimeRationalBits.RationalWord) (n B:Nat) (hB:width.length+2≤ B) :
    (SemiprimeD1RecoveryPowerBits.power width x n).word.numerator.magnitude.length+1≤ B ∧
    (SemiprimeD1RecoveryPowerBits.power width x n).word.denominator.length≤ B:=by
  have h:=SemiprimeD1StackRecoveryGridByteBounds.power_lengths width x n
  omega
end RiemannGaussian.SemiprimeD1StackRecoveryGridWordCaps
