/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackPackedRootInputOriginal
/-! # Exact structural cache invariance under the actual marked-table replacement
The complete dependent row structure retains counts, order, duplicates and
every owner ID. Structural cache equalities below concern literal words,
never old tensor coefficients and never native-to-machine clock transport.
-/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
noncomputable section
namespace RiemannGaussian.SemiprimeD1PackedNetworkTopology
open SemiprimeD1TensorNetwork
open SemiprimeD1StackMarkedRootRecordsNetwork (old network rowsAt leftCount_eq rows_eq)
/-- Complete typed incidence structure, including its actual owner-count bound. -/
def stamp (net : Network) : (n : ℕ)×Rows n := ⟨net.leftCount,net.rows⟩
/-- Explicit dependent row transport preserves the whole structural object. -/
theorem stamp_eq (base next : Network) (h : next.leftCount=base.leftCount)
    (hr : rowsAt base next h=base.rows) : stamp next=stamp base := by
  cases base with
  | mk bn br bl bx =>
    cases next with
    | mk nn nr nl nx =>
      change nn=bn at h
      cases h
      change nr=br at hr
      cases hr
      rfl
/-- The actual acquired marked network has EXACTLY the old complete ordered incidence structure. -/
theorem actual_stamp (N : ℕ) (hN : 0<N) : stamp (network N hN)=stamp (old N hN) :=
  stamp_eq (old N hN) (network N hN) (leftCount_eq N hN) (rows_eq N hN)
/-- The entire occurrence/alphabet/selector/key-source bank depends only on rows and counts. -/
theorem selection_congr (base next : Network) (h : next.leftCount=base.leftCount)
    (hr : rowsAt base next h=base.rows) (a : ℕ) :
    SemiprimeD1StackSourceSelectionAcquireEncoding.result next a=
      SemiprimeD1StackSourceSelectionAcquireEncoding.result base a := by
  cases base with
  | mk bn br bl bx =>
    cases next with
    | mk nn nr nl nx =>
      change nn=bn at h
      cases h
      change nr=br at hr
      cases hr
      rfl
/-- ALL154 structural source/cache words have the same exact marked-network interpretation.
No table word or acquisition/runtime clock is transferred by this equality. -/
theorem actual_selection (N : ℕ) (hN : 0<N) (a : ℕ) :
    SemiprimeD1StackSourceSelectionAcquireEncoding.result (network N hN) a=
      SemiprimeD1StackSourceSelectionAcquireEncoding.result (old N hN) a :=
  selection_congr (old N hN) (network N hN) (leftCount_eq N hN) (rows_eq N hN) a
/-- Only chronological placements and raw packet bytes, with no native report clock. -/
def inventory (net : Network) (a : ℕ) :
    List SemiprimeD1PacketInventory.Placement × List (List Bool) :=
  let acquired := SemiprimeD1PacketReplayOriginal.acquire net.leftCount net.rows.length 64 a
    (SemiprimeD1TensorNetwork.arity net.rows) (SemiprimeD1TensorNetwork.owner net.rows)
  (acquired.placements,acquired.state.packets)
/-- The complete sparse inventory's useful payload depends only on the ordered incidence structure. -/
theorem inventory_congr (base next : Network) (h : next.leftCount=base.leftCount)
    (hr : rowsAt base next h=base.rows) (a : ℕ) : inventory next a=inventory base a := by
  cases base with
  | mk bn br bl bx =>
    cases next with
    | mk nn nr nl nx =>
      change nn=bn at h
      cases h
      change nr=br at hr
      cases hr
      rfl
/-- Exact marked-network replay order, duplicate occurrences and packet bytes reuse the old payload. -/
theorem actual_inventory (N : ℕ) (hN : 0<N) (a : ℕ) :
    inventory (network N hN) a=inventory (old N hN) a :=
  inventory_congr (old N hN) (network N hN) (leftCount_eq N hN) (rows_eq N hN) a
end RiemannGaussian.SemiprimeD1PackedNetworkTopology
