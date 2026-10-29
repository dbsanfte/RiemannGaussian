/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackRecoveryWeights
/-! # Exact complete60-word boundary views for the actual six-input source
Every function here specifies an actual physical store, never a runtime getter.
The complete reused58 bank and both original scalar tapes remain explicit.
-/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackRecoveryWeightsView
open SemiprimeD1StackRecoveryWeights
namespace Old
export SemiprimeD1StackNormalizedInverseView (Words store getReg putReg emptyReg emptyRational)
end Old
/-- All58 reused arithmetic/cache/controller words plus both actual scalar inputs. -/
structure Words extends Old.Words where
  /-- Two retained original Ezero tapes; never filled from native rational fields. -/
  scalarInputs:Scalar→List Bool:=fun _=>[]
/-- Every physical role, including unused helper shadows, is counted. -/
def bank (w:Words):Stack→List Bool:=Sum.elim (Old.store w.toWords) w.scalarInputs
/-- Exact whole helper-bank replacement preserves both original scalar words. -/
def replace (w:Words) (old:Old.Words):Words:=⟨old,w.scalarInputs⟩
/-- One actual helper-role update retains every original scalar byte. -/
theorem update_helper (w:Words) (slot:I.Stack) (xs:List Bool):
    Function.update (bank w) (helper slot) xs=Sum.elim (Function.update (Old.store w.toWords) slot xs) w.scalarInputs:=by
  exact Sum.update_elim_inl
/-- One physical controller word changes and all59 other tapes are retained. -/
theorem update_aux (w:Words) (slot:I.Aux) (xs:List Bool):
    Function.update (bank w) (aux slot) xs=bank {w with auxiliary:=Function.update w.auxiliary slot xs}:=by
  rw [show aux slot=helper (SemiprimeD1StackNormalizedInverse.aux slot) from rfl,update_helper,
    SemiprimeD1StackNormalizedInverseView.update_aux]
  rfl
/-- One physical rational cache field changes while both original scalars are retained. -/
theorem update_register (w:Words) (slot:I.Reg) (den:Bool) (xs:List Bool):
    Function.update (bank w) (reg slot den) xs=bank {w with registers:=Function.update w.registers (slot,den) xs}:=by
  rw [show reg slot den=helper (SemiprimeD1StackNormalizedInverse.reg slot den) from rfl,update_helper,
    SemiprimeD1StackNormalizedInverseView.update_register]
  rfl
/-- Actual normalized cache updates preserve the full caller bank. -/
def putReg (w:Words) (slot:I.Reg) (word:SemiprimeRationalBits.RationalWord):Words:=replace w (Old.putReg w.toWords slot word)
/-- Actual two-field cache clearing preserves every foreign retained input. -/
def emptyReg (w:Words) (slot:I.Reg):Words:=replace w (Old.emptyReg w.toWords slot)
/-- Exact mathematical view of six original physical words and54 actual EMPTY work tapes. -/
def originals (inverse powers signed den q width:List Bool):Words:=
  {rational:=Old.emptyRational width,
   auxiliary:=fun slot=>match slot with | .denominator=>inverse | .prefixReverse=>powers | .originalQ=>q | _=>[],
   scalarInputs:=fun slot=>match slot with | .signed=>signed | .den=>den}
/-- Honest source bytes coincide with the complete physical view, including nonempty retained powers. -/
theorem originals_bank (inverse powers signed den q width:List Bool):
    bank (originals inverse powers signed den q width)=input inverse powers signed den q width:=rfl
end RiemannGaussian.SemiprimeD1StackRecoveryWeightsView
