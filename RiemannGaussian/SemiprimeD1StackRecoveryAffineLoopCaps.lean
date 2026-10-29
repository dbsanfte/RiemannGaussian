/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackRecoveryAffineStateCaps
import RiemannGaussian.SemiprimeD1StackRecoveryAffineLoopView
import RiemannGaussian.SemiprimeD1StackRecoveryAffineByteCaps
/-! # Actual array/remaining/tail word caps at the physical affine-loop boundaries -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackRecoveryAffineLoopCaps
open SemiprimeD1StackRecoveryAffine SemiprimeD1StackRecoveryAffineView
open SemiprimeD1StackRecoveryAffineWordCaps
open SemiprimeD1StackRecoveryAffineByteCaps (Small)
/-- The fixed two-role coefficient view is exactly two literal physical writes. -/
theorem coefficient_bank (w:Words) (remaining next:List Bool):
    Function.update (Function.update (bank w) (aux .remaining) remaining) (aux .nextArray) next=
      bank (SemiprimeD1StackRecoveryAffineCoefficientBuffers.buffers w remaining next):=by
  rw [update_added,update_added]
  congr 1
  congr 1
  funext slot
  cases slot <;> simp
/-- All actual fields of the full coefficient caller retain a fixed actual data cap. -/
theorem coefficient_data (w:Words) (remaining next:List Bool) (L:Nat) (hw:Data w L)
    (hr:remaining.length≤ L) (hn:next.length≤ L):
    Data (SemiprimeD1StackRecoveryAffineCoefficientBuffers.buffers w remaining next) L:=by
  have h0:=update_le (bank w) (aux .remaining) remaining L hw hr
  have h1:=update_le _ (aux .nextArray) next L h0 hn
  rw [coefficient_bank] at h1
  exact h1
/-- Array and unread-slope changes do not alter any original104 rational register. -/
theorem state_registers (w:Words) (xs slopes:List SemiprimeRationalBits.RationalWord) (B:Nat) (hw:Registers w B):
    Registers (SemiprimeD1StackRecoveryAffineLoopView.state w xs slopes) B:=hw
/-- Actual current array/tail tape byte caps preserve all original104 and other added words. -/
theorem state_data (w:Words) (xs slopes:List SemiprimeRationalBits.RationalWord) (L:Nat) (hw:Data w L)
    (hx:(vector xs).length≤ L) (hs:(vector slopes).length≤ L):
    Data (SemiprimeD1StackRecoveryAffineLoopView.state w xs slopes) L:=
  added_data _ .reverseSlopes _ L (added_data w .array _ L hw hx) hs
/-- A scalar update on the physically acquired slope still uses only fitted/literal input bytes. -/
theorem small_put_registers (w:Words) (r:SemiprimeD1StackRecoveryGrid.Reg) (x:SemiprimeRationalBits.RationalWord)
    (width:List Bool) (B:Nat) (hw:Registers w B) (hx:Small width x) (hW:width.length+2≤ B):Registers (putReg w r x) B:=
  put_registers w r x B hw (by have h:=hx.1;omega) (by have h:=hx.2;omega)
/-- Current slope acquisition charges only its actual signed and raw denominator fields. -/
theorem small_put_data (w:Words) (r:SemiprimeD1StackRecoveryGrid.Reg) (x:SemiprimeRationalBits.RationalWord)
    (width:List Bool) (B L:Nat) (hw:Data w L) (hx:Small width x) (hW:width.length+2≤ B) (hBL:B≤ L):Data (putReg w r x) L:=
  put_data w r x L hw (by have h:=hx.1;omega) (by have h:=hx.2;omega)
/-- One actually framed fitted coefficient has a fixed linear raw row-byte budget, including signs and delimiters. -/
theorem coefficient_row_length (xs:List SemiprimeRationalBits.RationalWord) (c:SemiprimeRationalBits.RationalWord)
    (width tail:List Bool) (n:Nat):
    (SemiprimeD1StackRecoveryGridView.slopeRow (SemiprimeD1StackRecoveryAffineCoefficient.answer xs c width n) tail).length≤
      tail.length+(4*width.length+9):=by
  have h:=SemiprimeD1StackRecoveryAffineByteCaps.coefficient_small width xs c n
  rw [SemiprimeD1StackRecoveryGridByteBounds.slopeRow_length]
  have hn:=h.1
  have hd:=h.2
  omega
end RiemannGaussian.SemiprimeD1StackRecoveryAffineLoopCaps
