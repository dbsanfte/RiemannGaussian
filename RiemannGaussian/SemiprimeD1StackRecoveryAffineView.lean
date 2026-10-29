/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackRecoveryAffineInventory
/-! # Complete112-word affine source views and literal physical updates
These are proof invariants over the actual finite stores, never coefficient,
array, multiplicity, list or evaluator operands of the runtime program.
-/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackRecoveryAffineView
open SemiprimeD1StackRecoveryAffine
/-- Every original Grid104 field and all eight additional words are explicit. -/
structure Words extends SemiprimeD1StackRecoveryGridView.Words where
  /-- Actual additional count, scan and chronological array buffers. -/
  added:Aux→List Bool:=fun _=>[]
/-- All112 actual physical words, with the complete original Grid bank retained. -/
def bank (w:Words):Stack→List Bool:=Sum.elim (SemiprimeD1StackRecoveryGridView.bank w.toWords) w.added
/-- Source rational codec retains the actual sign and all raw magnitude/denominator padding. -/
def signed (x:SemiprimeRationalBits.RationalWord):List Bool:=x.numerator.negative::x.numerator.magnitude
/-- Rational vectors use exactly the acquired Grid slope ABI. -/
def vector (xs:List SemiprimeRationalBits.RationalWord):List Bool:=SemiprimeD1StackRecoveryGridView.slopeTape xs
/-- One actual additional-word write preserves all original104 cells. -/
theorem update_added (w:Words) (slot:Aux) (xs:List Bool) :
    Function.update (bank w) (aux slot) xs=bank {w with added:=Function.update w.added slot xs}:=by
  funext role
  rcases role with role|role
  · rfl
  · simp only [bank,aux,Function.update_apply,Sum.elim_inr,Sum.inr.injEq]
/-- A physical original-grid write preserves every additional word. -/
theorem update_grid (w:Words) (slot:Q.Stack) (xs:List Bool) :
    Function.update (bank w) (grid slot) xs=Sum.elim (Function.update (SemiprimeD1StackRecoveryGridView.bank w.toWords) slot xs) w.added:=by
  funext role
  rcases role with role|role
  · simp only [bank,grid,Function.update_apply,Sum.elim_inl,Sum.inl.injEq]
  · rfl
/-- Only one actual rational-helper word changes. -/
theorem update_rational (w:Words) (slot:R.Stack) (xs:List Bool) :
    Function.update (bank w) (rational slot) xs=bank {w with rational:=Function.update w.rational slot xs}:=by
  rw [show rational slot=grid (Q.rationalStack slot) from rfl,update_grid,
    SemiprimeD1StackRecoveryGridView.update_rational]
  rfl
/-- Only one actual geometry/shadow word changes. -/
theorem update_geometry (w:Words) (slot:SemiprimeD1StackPhaseGeometry.Aux) (xs:List Bool) :
    Function.update (bank w) (grid (Q.geometryAux slot)) xs=bank {w with geometry:=Function.update w.geometry slot xs}:=by
  rw [update_grid,SemiprimeD1StackRecoveryGridView.update_geometry]
  rfl
/-- Only one actual unary-product word changes. -/
theorem update_product (w:Words) (slot:P.Stack) (xs:List Bool) :
    Function.update (bank w) (product slot) xs=bank {w with product:=Function.update w.product slot xs}:=by
  rw [show product slot=grid (Q.productStack slot) from rfl,update_grid,
    SemiprimeD1StackRecoveryGridView.update_product]
  rfl
/-- One original metadata/scratch write leaves every other111 word intact. -/
theorem update_oldAux (w:Words) (slot:SemiprimeD1StackRecoveryGrid.Aux) (xs:List Bool) :
    Function.update (bank w) (oldAux slot) xs=bank {w with auxiliary:=Function.update w.auxiliary slot xs}:=by
  rw [show oldAux slot=grid (Q.aux slot) from rfl,update_grid,
    SemiprimeD1StackRecoveryGridView.update_auxiliary]
  rfl
/-- One actual signed/denominator cache field changes. -/
theorem update_register (w:Words) (r:SemiprimeD1StackRecoveryGrid.Reg) (den:Bool) (xs:List Bool) :
    Function.update (bank w) (reg r den) xs=bank {w with registers:=Function.update w.registers (r,den) xs}:=by
  rw [show reg r den=grid (Q.reg r den) from rfl,update_grid,
    SemiprimeD1StackRecoveryGridView.update_registers w.toWords (r,den)]
  rfl
/-- The exact actual rational cache interpretation, with no compact-padding shortcut. -/
def getReg (w:Words) (r:SemiprimeD1StackRecoveryGrid.Reg):SemiprimeRationalBits.RationalWord:=
  SemiprimeD1StackRecoveryGridView.getReg w.toWords r
/-- Exact two physical cache writes corresponding to one completed real operation. -/
def putReg (w:Words) (r:SemiprimeD1StackRecoveryGrid.Reg) (x:SemiprimeRationalBits.RationalWord):Words:=
  {w with registers:=Function.update (Function.update w.registers (r,false) (signed x)) (r,true) x.denominator}
/-- Both actual cache fields are exactly the normalized/fitted bytes. -/
theorem putReg_fields (w:Words) (r:SemiprimeD1StackRecoveryGrid.Reg) (x:SemiprimeRationalBits.RationalWord) :
    (putReg w r x).registers (r,false)=signed x ∧(putReg w r x).registers (r,true)=x.denominator:=by
  constructor <;> simp [putReg]
/-- Reading a just-written actual cache recovers its exact sign and raw field bytes. -/
theorem getReg_putReg (w:Words) (r:SemiprimeD1StackRecoveryGrid.Reg) (x:SemiprimeRationalBits.RationalWord) :getReg (putReg w r x) r=x:=by
  change SemiprimeD1StackRecoveryGridView.getReg (SemiprimeD1StackRecoveryGridView.putReg w.toWords r x) r=x
  exact SemiprimeD1StackRecoveryGridRegisters.getReg_putReg w.toWords r x
end RiemannGaussian.SemiprimeD1StackRecoveryAffineView
