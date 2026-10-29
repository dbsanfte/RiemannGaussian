/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackRecoveryNodeInputs
/-! # Static physical alias injectivity and complete140-role bank projection -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackRecoveryNodeInputsInventory
open SemiprimeD1StackRecoveryNodeInputs
/-- The whole old112 bank has a literal injective physical inclusion. -/
theorem affine_injective : Function.Injective affine := Sum.inl_injective
/-- All inverse58 source/cache/work aliases are distinct within that actual real call. -/
theorem inverse_injective : Function.Injective inverse := by
  intro x y h
  rcases x with x|x
  · rcases y with y|y
    · simpa only [inverse,affine,SemiprimeD1StackRecoveryAffine.rational,
        SemiprimeD1StackRecoveryAffine.grid,SemiprimeD1StackRecoveryGrid.rationalStack,Sum.inl.injEq] using h
    · rcases y with y|y
      · simp [inverse,affine,inverseReg] at h
      · cases y <;> simp [inverse,affine,inverseWork,SemiprimeD1StackRecoveryAffine.rational,
          SemiprimeD1StackRecoveryAffine.grid,SemiprimeD1StackRecoveryAffine.aux,
          SemiprimeD1StackRecoveryGrid.rationalStack] at h
  · rcases y with y|y
    · rcases x with x|x
      · simp [inverse,affine,inverseReg] at h
      · cases x <;> simp [inverse,affine,inverseWork,SemiprimeD1StackRecoveryAffine.rational,
          SemiprimeD1StackRecoveryAffine.grid,SemiprimeD1StackRecoveryAffine.aux,
          SemiprimeD1StackRecoveryGrid.rationalStack] at h
    · rcases x with x|x <;> rcases y with y|y
      · simpa only [inverse,inverseReg,Sum.inr.injEq,Sum.inl.injEq] using h
      · cases y <;> simp [inverse,inverseReg,inverseWork,affine] at h
      · cases x <;> simp [inverse,inverseReg,inverseWork,affine] at h
      · cases x <;> cases y <;> simp_all [inverse,affine,inverseWork,SemiprimeD1StackRecoveryAffine.aux]
/-- All powers47 aliases, including actual argument/q sources, are distinct in the real source inclusion. -/
theorem powers_injective : Function.Injective powers := by
  intro x y h
  rcases x with x|x <;> rcases y with y|y
  · simpa only [powers,affine,SemiprimeD1StackRecoveryAffine.rational,
      SemiprimeD1StackRecoveryAffine.grid,SemiprimeD1StackRecoveryGrid.rationalStack,Sum.inl.injEq] using h
  · cases y <;> simp [powers,affine,powersWork,SemiprimeD1StackRecoveryAffine.rational,
      SemiprimeD1StackRecoveryAffine.grid,SemiprimeD1StackRecoveryAffine.aux,
      SemiprimeD1StackRecoveryGrid.rationalStack,SemiprimeD1StackRecoveryGrid.reg] at h
  · cases x <;> simp [powers,affine,powersWork,SemiprimeD1StackRecoveryAffine.rational,
      SemiprimeD1StackRecoveryAffine.grid,SemiprimeD1StackRecoveryAffine.aux,
      SemiprimeD1StackRecoveryGrid.rationalStack,SemiprimeD1StackRecoveryGrid.reg] at h
  · cases x <;> cases y <;> simp_all [powers,affine,powersWork,SemiprimeD1StackRecoveryAffine.grid,
      SemiprimeD1StackRecoveryAffine.aux,SemiprimeD1StackRecoveryGrid.reg]
/-- The physical template is shared directly by all three actual calls. -/
theorem inverse_template : inverse (I.rational (SemiprimeD1StackRationalOperation.aux .template))=widthWord := rfl
/-- Powers does not receive a copied/supplied width answer. -/
theorem powers_template : powers SemiprimeD1StackRecoveryPowers.template=widthWord := rfl
/-- The actual unary count is shared directly, without a decoded control index. -/
theorem inverse_q : inverse (I.aux .originalQ)=qWord := rfl
/-- Powers reads exactly the SAME acquired unary multiplicity. -/
theorem powers_q : powers (P.aux .q)=qWord := rfl
end RiemannGaussian.SemiprimeD1StackRecoveryNodeInputsInventory
