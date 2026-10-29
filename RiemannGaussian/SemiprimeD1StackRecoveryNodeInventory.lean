/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackRecoveryNode
/-! # Static injectivity of all sixty actual operand/helper aliases -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackRecoveryNodeInventory
open SemiprimeD1StackRecoveryNode
/-- All original140 data roles have distinct physical images. -/
theorem node_injective:Function.Injective node:=Sum.inl_injective
/-- Complete actual58 helper image has no hidden physical overlaps. -/
theorem weightHelper_injective:Function.Injective weightHelper:=by
  intro x y h
  rcases x with x|x|x <;> rcases y with y|y|y
  all_goals first
    | (simpa [weightHelper,node,SemiprimeD1StackRecoveryNodeInputs.inverse,
        SemiprimeD1StackRecoveryNodeInputs.affine,SemiprimeD1StackRecoveryAffine.rational,
        SemiprimeD1StackRecoveryAffine.grid,SemiprimeD1StackRecoveryGrid.rationalStack] using h)
    | skip
  all_goals try cases x
  all_goals try cases y
  all_goals simp_all [weightHelper,node,output,SemiprimeD1StackRecoveryNodeInputs.inverse,
    SemiprimeD1StackRecoveryNodeInputs.inverseReg,SemiprimeD1StackRecoveryNodeInputs.inverseWork,
    SemiprimeD1StackRecoveryNodeInputs.inverseOutput,SemiprimeD1StackRecoveryNodeInputs.powersOutput,
    SemiprimeD1StackRecoveryNodeInputs.powers,SemiprimeD1StackRecoveryNodeInputs.powersWork,
    SemiprimeD1StackRecoveryNodeInputs.qWord,SemiprimeD1StackRecoveryNodeInputs.affine,
    SemiprimeD1StackRecoveryAffine.rational,SemiprimeD1StackRecoveryAffine.grid,
    SemiprimeD1StackRecoveryAffine.aux,SemiprimeD1StackRecoveryGrid.rationalStack,
    SemiprimeD1StackNormalizedInverse.aux,SemiprimeD1StackRecoveryPowers.aux]
/-- Both scalar fields are distinct from every reused helper address. -/
theorem helper_not_scalar (role:I.Stack) (den:Bool):
    weightHelper role≠node (if den then N.scalarDen else N.scalarSigned):=by
  rcases role with role|role|role
  all_goals try cases role
  all_goals cases den
  all_goals simp [weightHelper,node,output,SemiprimeD1StackRecoveryNodeInputs.inverse,
    SemiprimeD1StackRecoveryNodeInputs.inverseReg,SemiprimeD1StackRecoveryNodeInputs.inverseWork,
    SemiprimeD1StackRecoveryNodeInputs.inverseOutput,SemiprimeD1StackRecoveryNodeInputs.powersOutput,
    SemiprimeD1StackRecoveryNodeInputs.powers,SemiprimeD1StackRecoveryNodeInputs.powersWork,
    SemiprimeD1StackRecoveryNodeInputs.qWord,SemiprimeD1StackRecoveryNodeInputs.affine,
    SemiprimeD1StackRecoveryNodeInputs.scalarSigned,SemiprimeD1StackRecoveryNodeInputs.scalarDen,
    SemiprimeD1StackRecoveryAffine.rational,SemiprimeD1StackRecoveryAffine.grid,
    SemiprimeD1StackRecoveryAffine.aux,SemiprimeD1StackRecoveryGrid.rationalStack,
    SemiprimeD1StackRecoveryGrid.reg,SemiprimeD1StackNormalizedInverse.aux,SemiprimeD1StackRecoveryPowers.aux]
/-- Every whole weight-source role is injectively wired, including all helper shadows. -/
theorem weight_injective:Function.Injective weight:=by
  intro x y h
  rcases x with x|x <;> rcases y with y|y
  · exact congrArg Sum.inl (weightHelper_injective h)
  · cases y
    · exact (helper_not_scalar x false h).elim
    · exact (helper_not_scalar x true h).elim
  · cases x
    · exact (helper_not_scalar y false h.symm).elim
    · exact (helper_not_scalar y true h.symm).elim
  · cases x <;> cases y <;> simp_all [weight,node,
      SemiprimeD1StackRecoveryNodeInputs.scalarSigned,SemiprimeD1StackRecoveryNodeInputs.scalarDen,
      SemiprimeD1StackRecoveryNodeInputs.affine,SemiprimeD1StackRecoveryAffine.grid,SemiprimeD1StackRecoveryGrid.reg]
/-- Exact six source operands are direct physical aliases. -/
theorem weight_inverse:weight (W.aux .denominator)=node N.inverseOutput:=rfl
/-- Acquired powers are immutable in the whole weight source, not inverse helper work. -/
theorem weight_powers:weight (W.aux .prefixReverse)=node N.powersOutput:=rfl
/-- All actual output bytes go into the only additional physical tape. -/
theorem weight_output:weight (W.aux .output)=output:=rfl
end RiemannGaussian.SemiprimeD1StackRecoveryNodeInventory
