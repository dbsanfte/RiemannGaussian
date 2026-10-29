/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackRecoveryWeightsOuterView
import RiemannGaussian.SemiprimeD1StackRecoveryWeightsCleanup
/-! # Complete final53 cleanup bank retains all six actual inputs and every ordered output row -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackRecoveryWeightsFinishView
open SemiprimeD1StackRecoveryWeights SemiprimeD1StackRecoveryWeightsView
open SemiprimeD1StackRecoveryWeightsOuterView SemiprimeD1StackRecoveryWeightsCleanup
open SemiprimeD1StackRecoveryWeightsInventory
open SemiprimeRationalBits (RationalWord)
/-- All actual private helpers and shadows are already empty at a clean outer EOF boundary. -/
theorem empty_private (inverse powers:List RationalWord) (scalar:RationalWord) (q:Nat) (width out:List Bool)
    (k:I.Stack) (hk:¬kept k):Old.store (outer inverse powers scalar q width 0 out).toWords k=[]:=by
  rcases k with r|r
  · have hn:r≠SemiprimeD1StackRationalOperation.aux .template:=by
      intro h
      apply hk
      left
      exact congrArg SemiprimeD1StackNormalizedInverse.rational h
    exact ite_eq_right hn
  · rcases r with r|r
    · rfl
    · cases r <;> first | rfl | (exfalso;apply hk;simp [kept,SemiprimeD1StackNormalizedInverse.aux,SemiprimeD1StackNormalizedInverse.template])
/-- The dedicated real cleanup keeps literal powers, inverse, q, W, scalar2 and ordered output, with no omitted word. -/
theorem clean_outer (inverse powers:List RationalWord) (scalar:RationalWord) (q:Nat) (width out:List Bool):
    cleanStore (outer inverse powers scalar q width 0 out)=bank (outer inverse powers scalar q width 0 out):=by
  classical
  funext role
  rcases role with role|role
  · change (if kept role then Old.store (outer inverse powers scalar q width 0 out).toWords role else [])=_
    by_cases h:kept role
    · rw [ite_eq_left h];rfl
    · rw [ite_eq_right h]
      exact (empty_private inverse powers scalar q width out role h).symm
  · rfl
end RiemannGaussian.SemiprimeD1StackRecoveryWeightsFinishView
