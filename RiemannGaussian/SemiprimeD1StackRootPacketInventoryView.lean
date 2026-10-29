/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackRootPacketInventory
/-! # Exact whole2270-role producer and inventory boundaries -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackRootPacketInventoryView
open SemiprimeD1StackRootPacketInventory
/-- A real source-bank update retains every other actual allocated word. -/
theorem data_root (root:R.Stack→List Bool) (inventory:I.Stack→List Bool) (xs:List Bool) (k:R.Stack) :
    Function.update (data root inventory) (rootStack k) xs=data (Function.update root k xs) inventory :=by
  funext p
  rcases p with p|p
  · simp only [data,rootStack,Function.update_apply,Sum.elim_inl,Sum.inl.injEq]
  · rfl
/-- Generic physical projection is exact before original-N instantiation. -/
theorem root_word (root:R.Stack→List Bool) (inventory:I.Stack→List Bool) (k:R.Stack) :
    data root inventory (rootStack k)=root k :=rfl
/-- A real source-bank update retains every other actual allocated word. -/
theorem data_inventory (root:R.Stack→List Bool) (inventory:I.Stack→List Bool) (xs:List Bool) (k:I.Stack) :
    Function.update (data root inventory) (inventoryStack k) xs=data root (Function.update inventory k xs) :=by
  funext p
  rcases p with p|p
  · rfl
  · simp only [data,inventoryStack,Function.update_apply,Sum.elim_inr,Sum.inr.injEq]
/-- Generic physical projection is exact before original-N instantiation. -/
theorem inventory_word (root:R.Stack→List Bool) (inventory:I.Stack→List Bool) (k:I.Stack) :
    data root inventory (inventoryStack k)=inventory k :=rfl
end RiemannGaussian.SemiprimeD1StackRootPacketInventoryView
