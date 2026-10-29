/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackRootPacketInventoryPrimitives
/-! # Actual selected-key/catalogue transfers with the retained source scratch -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackRootPacketInventoryInput
open SemiprimeD1StackRootPacketInventory SemiprimeD1StackRootPacketInventoryView
open SemiprimeD1StackRootPacketInventoryPrimitives SemiprimeD1StackProcedureTrace
local notation "ctl" => Label.local
/-- Only the literal next source's two input fields are populated. -/
def inventoryReady (root:R.Stack→List Bool) :I.Stack→List Bool :=
  Function.update (Function.update (fun _=>[])
    (I.source) (root Source.keysRole))
    (I.catalogue) (root Source.catalogueRole)
/-- The two actual writes yield exactly the next real source's honest physical input bank. -/
theorem inventoryReady_input (root:R.Stack→List Bool) :inventoryReady root=
    (I.initial (root Source.keysRole) (root Source.catalogueRole)).data :=by
  rfl
/-- Both restoring copies pay every actual metadata byte and both real returns. -/
def inventoryCopyTime (root:R.Stack→List Bool) :Nat :=
  5*((root Source.keysRole).length+(root Source.catalogueRole).length)+8
/-- The original producer bank is retained literally, including its reused scratch restored to empty. -/
theorem inventory_input_run (root:R.Stack→List Bool) (hs:root R.copyScratch=[]) :
    Runs program (inventoryCopyTime root) (ctl (.copy .keys)) (data root (fun _=>[]))
      (ctl .inventory) (data root (inventoryReady root)) :=by
  let s0:I.Stack→List Bool:=fun _=>[]
  let s1:=Function.update s0 (I.source) (root Source.keysRole)
  let s2:=Function.update s1 (I.catalogue) (root Source.catalogueRole)
  have h0:=copy_call .keys (data root s0) (root Source.keysRole) [] rfl rfl hs
  simp only [List.append_nil] at h0
  change Runs program _ _ _ _ (Function.update (data root s0)
    (inventoryStack (I.source)) (root Source.keysRole)) at h0
  rw [data_inventory] at h0
  have h1:=copy_call .catalogue (data root s1) (root Source.catalogueRole) [] rfl rfl hs
  simp only [List.append_nil] at h1
  change Runs program _ _ _ _ (Function.update (data root s1)
    (inventoryStack (I.catalogue)) (root Source.catalogueRole)) at h1
  rw [data_inventory] at h1
  have h:=join h0 h1
  change Runs program _ _ _ (ctl .inventory) _ at h
  change Runs program _ _ _ _ (data root s2)
  convert h using 1
  unfold inventoryCopyTime
  omega
end RiemannGaussian.SemiprimeD1StackRootPacketInventoryInput
