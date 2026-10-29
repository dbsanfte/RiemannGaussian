/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackRootPacketPadding
/-! # Exact whole2139-role producer and padding boundaries -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackRootPacketPaddingView
open SemiprimeD1StackRootPacketPadding
/-- A real source-bank update retains every other actual allocated word. -/
theorem data_root (root:R.Stack→List Bool) (padding:Q.Stack→List Bool) (xs:List Bool) (k:R.Stack) :
    Function.update (data root padding) (rootStack k) xs=data (Function.update root k xs) padding :=by
  funext p
  rcases p with p|p
  · simp only [data,rootStack,Function.update_apply,Sum.elim_inl,Sum.inl.injEq]
  · rfl
/-- Generic physical projection is exact before original-N instantiation. -/
theorem root_word (root:R.Stack→List Bool) (padding:Q.Stack→List Bool) (k:R.Stack) :
    data root padding (rootStack k)=root k :=rfl
/-- A real source-bank update retains every other actual allocated word. -/
theorem data_padding (root:R.Stack→List Bool) (padding:Q.Stack→List Bool) (xs:List Bool) (k:Q.Stack) :
    Function.update (data root padding) (paddingStack k) xs=data root (Function.update padding k xs) :=by
  funext p
  rcases p with p|p
  · rfl
  · simp only [data,paddingStack,Function.update_apply,Sum.elim_inr,Sum.inr.injEq]
/-- Generic physical projection is exact before original-N instantiation. -/
theorem padding_word (root:R.Stack→List Bool) (padding:Q.Stack→List Bool) (k:Q.Stack) :
    data root padding (paddingStack k)=padding k :=rfl
end RiemannGaussian.SemiprimeD1StackRootPacketPaddingView
