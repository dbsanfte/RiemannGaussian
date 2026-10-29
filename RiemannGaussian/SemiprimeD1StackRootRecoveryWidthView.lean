/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackRootRecoveryWidth
/-! # Exact whole2211-role producer and width boundaries -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackRootRecoveryWidthView
open SemiprimeD1StackRootRecoveryWidth
/-- A real source-bank update retains every other actual allocated word. -/
theorem data_root (root:R.Stack→List Bool) (width:W.Stack→List Bool) (xs:List Bool) (k:R.Stack) :
    Function.update (data root width) (rootStack k) xs=data (Function.update root k xs) width :=by
  funext p
  rcases p with p|p
  · simp only [data,rootStack,Function.update_apply,Sum.elim_inl,Sum.inl.injEq]
  · rfl
/-- Generic physical projection is exact before original-N instantiation. -/
theorem root_word (root:R.Stack→List Bool) (width:W.Stack→List Bool) (k:R.Stack) :
    data root width (rootStack k)=root k :=rfl
/-- A real source-bank update retains every other actual allocated word. -/
theorem data_width (root:R.Stack→List Bool) (width:W.Stack→List Bool) (xs:List Bool) (k:W.Stack) :
    Function.update (data root width) (widthStack k) xs=data root (Function.update width k xs) :=by
  funext p
  rcases p with p|p
  · rfl
  · simp only [data,widthStack,Function.update_apply,Sum.elim_inr,Sum.inr.injEq]
/-- Generic physical projection is exact before original-N instantiation. -/
theorem width_word (root:R.Stack→List Bool) (width:W.Stack→List Bool) (k:W.Stack) :
    data root width (widthStack k)=width k :=rfl
end RiemannGaussian.SemiprimeD1StackRootRecoveryWidthView
