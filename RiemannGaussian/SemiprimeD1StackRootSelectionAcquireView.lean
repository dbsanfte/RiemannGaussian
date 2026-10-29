/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackRootSelectionAcquire
/-! # Exact complete2114-role boundaries and physical updates -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackRootSelectionAcquireView
open SemiprimeD1StackRootSelectionAcquire
/-- A real bank update preserves every other actual source/cache/shadow role. -/
theorem data_root (root:R.Stack→List Bool) (parameters:P.Stack→List Bool) (acquisition:Q.Stack→List Bool) (xs:List Bool) (k:R.Stack) :
    Function.update (data root parameters acquisition) (rootStack k) xs=data (Function.update root k xs) parameters acquisition :=by
  funext p
  rcases p with p|p
  · simp only [data,rootStack,Function.update_apply,Sum.elim_inl,Sum.inl.injEq]
  · rfl
/-- The full physical bank projection is exact. -/
theorem root_word (root:R.Stack→List Bool) (parameters:P.Stack→List Bool) (acquisition:Q.Stack→List Bool) (k:R.Stack) :
    data root parameters acquisition (rootStack k)=root k :=rfl
/-- A real bank update preserves every other actual source/cache/shadow role. -/
theorem data_parameters (root:R.Stack→List Bool) (parameters:P.Stack→List Bool) (acquisition:Q.Stack→List Bool) (xs:List Bool) (k:P.Stack) :
    Function.update (data root parameters acquisition) (parameterStack k) xs=data root (Function.update parameters k xs) acquisition :=by
  funext p
  rcases p with p|p
  · rfl
  · rcases p with p|p
    · simp only [data,parameterStack,Function.update_apply,Sum.elim_inr,Sum.inr.injEq,Sum.elim_inl,Sum.inl.injEq]
    · rfl
/-- The full physical bank projection is exact. -/
theorem parameters_word (root:R.Stack→List Bool) (parameters:P.Stack→List Bool) (acquisition:Q.Stack→List Bool) (k:P.Stack) :
    data root parameters acquisition (parameterStack k)=parameters k :=rfl
/-- A real bank update preserves every other actual source/cache/shadow role. -/
theorem data_acquisition (root:R.Stack→List Bool) (parameters:P.Stack→List Bool) (acquisition:Q.Stack→List Bool) (xs:List Bool) (k:Q.Stack) :
    Function.update (data root parameters acquisition) (acquisitionStack k) xs=data root parameters (Function.update acquisition k xs) :=by
  funext p
  rcases p with p|p
  · rfl
  · rcases p with p|p
    · rfl
    · simp only [data,acquisitionStack,Function.update_apply,Sum.elim_inr,Sum.inr.injEq]
/-- The full physical bank projection is exact. -/
theorem acquisition_word (root:R.Stack→List Bool) (parameters:P.Stack→List Bool) (acquisition:Q.Stack→List Bool) (k:Q.Stack) :
    data root parameters acquisition (acquisitionStack k)=acquisition k :=rfl
end RiemannGaussian.SemiprimeD1StackRootSelectionAcquireView
