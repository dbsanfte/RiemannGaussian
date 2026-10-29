/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1PacketAssignmentRows

/-! # Original occurrence positions in the observed packet partition
Every position is read from the actual paired stream and observed packet list.
The bijection and packet membership are proved from acquisition, never advised.
-/
set_option autoImplicit false
set_option maxHeartbeats 3500000
namespace RiemannGaussian.SemiprimeD1OriginalPacketPositions
open SemiprimeD1OriginalIncidenceIndex SemiprimeD1CollisionOriginal
open SemiprimeD1PacketColumnPartition SemiprimeD1PacketInventory
noncomputable section

/-- Original pairing has exactly one entry per actual replay placement. -/
theorem pairs_length (n F r a : ℕ) (arity : Fin F→ℕ)
    (owner : ((e : Fin F)×Fin (arity e))→Fin n) :
    (originalPairs n F r a arity owner).length=
      (SemiprimeD1PacketReplayOriginal.acquire n F r a arity owner).placements.length := by
  unfold originalPairs
  rw [List.length_zip,SemiprimeD1OriginalModeAcquisition.original_size,Nat.min_self]

/-- Exact original typed-port/placement pair at every actual position, in order. -/
theorem pairs_ofFn (n F r a : ℕ) (arity : Fin F→ℕ)
    (owner : ((e : Fin F)×Fin (arity e))→Fin n) :
    originalPairs n F r a arity owner=List.ofFn (fun j : Fin
      (SemiprimeD1PacketReplayOriginal.acquire n F r a arity owner).placements.length =>
      ((position n F r a arity owner).symm j,
        (SemiprimeD1PacketReplayOriginal.acquire n F r a arity owner).placements[j.val])) := by
  apply List.ext_getElem
  · rw [pairs_length,List.length_ofFn]
  · intro k hk hk'
    have hM : k<(SemiprimeD1PacketReplayOriginal.acquire n F r a arity owner).placements.length := by
      simpa only [pairs_length] using hk
    have hP : k<(ports n F a arity).length := by
      rw [←SemiprimeD1OriginalModeAcquisition.original_size n F r a arity owner]
      exact hM
    have hp := port_at_position n F r a arity owner ((position n F r a arity owner).symm ⟨k,hM⟩)
    have hp' : (ports n F a arity)[k]=((position n F r a arity owner).symm ⟨k,hM⟩) := by
      simpa only [Equiv.apply_symm_apply] using hp
    simp only [originalPairs,List.getElem_zip,List.getElem_ofFn]
    exact Prod.ext hp' rfl

/-- Original placement's packet ordinal is the literal observed-list index. -/
def observed (n F r a : ℕ) (arity : Fin F→ℕ)
    (owner : ((e : Fin F)×Fin (arity e))→Fin n)
    (j : Fin (SemiprimeD1PacketReplayOriginal.acquire n F r a arity owner).placements.length) :
    Fin (SemiprimeD1PacketReplayOriginal.acquire n F r a arity owner).state.packets.length :=
  ⟨(SemiprimeD1PacketReplayOriginal.acquire n F r a arity owner).state.packets.idxOf
      ((SemiprimeD1PacketReplayOriginal.acquire n F r a arity owner).placements[j.val]).packet,
    List.idxOf_lt_length_of_mem (SemiprimeD1PacketInventoryCoverage.original_placement_packet
      n F r a arity owner _ (List.getElem_mem j.isLt))⟩

/-- The computed observed ordinal reads the placement's exact physical key. -/
theorem observed_key (n F r a : ℕ) (arity : Fin F→ℕ)
    (owner : ((e : Fin F)×Fin (arity e))→Fin n)
    (j : Fin (SemiprimeD1PacketReplayOriginal.acquire n F r a arity owner).placements.length) :
    (SemiprimeD1PacketReplayOriginal.acquire n F r a arity owner).state.packets[(observed n F r a arity owner j).val]=
      ((SemiprimeD1PacketReplayOriginal.acquire n F r a arity owner).placements[j.val]).packet :=
  List.getElem_idxOf (observed n F r a arity owner j).isLt

/-- Original byte-key packet filtering is exactly the computed finite partition. -/
theorem observed_eq_iff (n F r a : ℕ) (arity : Fin F→ℕ)
    (owner : ((e : Fin F)×Fin (arity e))→Fin n)
    (j : Fin (SemiprimeD1PacketReplayOriginal.acquire n F r a arity owner).placements.length)
    (f : Fin (SemiprimeD1PacketReplayOriginal.acquire n F r a arity owner).state.packets.length) :
    observed n F r a arity owner j=f ↔
      ((SemiprimeD1PacketReplayOriginal.acquire n F r a arity owner).placements[j.val]).packet=
        (SemiprimeD1PacketReplayOriginal.acquire n F r a arity owner).state.packets[f.val] := by
  constructor
  · intro h
    have hk := observed_key n F r a arity owner j
    have heq := congrArg (fun f : Fin (SemiprimeD1PacketReplayOriginal.acquire n F r a arity owner).state.packets.length =>
      (SemiprimeD1PacketReplayOriginal.acquire n F r a arity owner).state.packets[f.val]) h
    exact hk.symm.trans heq
  · intro h
    apply Fin.ext
    change (SemiprimeD1PacketReplayOriginal.acquire n F r a arity owner).state.packets.idxOf _=f.val
    rw [h]
    exact (SemiprimeD1PacketReplayOriginal.packets_nodup n F r a arity owner).idxOf_getElem f.val f.isLt

end
end RiemannGaussian.SemiprimeD1OriginalPacketPositions
