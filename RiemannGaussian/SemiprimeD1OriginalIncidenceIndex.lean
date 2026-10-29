/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1TensorNetworkLayout
import RiemannGaussian.SemiprimeD1OriginalModeAcquisition
import RiemannGaussian.SemiprimeD1ChildPortBijection

/-! # Computed original typed occurrences in actual placement order
The incidence/placement bijection is literal index search in the actual ordered
original metadata enumeration. Parallel incidences remain distinct, and the
zipped original port/placement pair is retained at every corresponding index.
-/
set_option autoImplicit false
set_option maxHeartbeats 2200000
namespace RiemannGaussian.SemiprimeD1OriginalIncidenceIndex
open SemiprimeD1CollisionOriginal SemiprimeD1ChildPortBijection
open SemiprimeD1TensorNetwork SemiprimeD1TensorNetworkLayout

/-- Actual original typed incidence positions, computed by native list search. -/
def portPosition (n F a : ℕ) (arity : Fin F → ℕ) :
    ((e : Fin F) × Fin (arity e)) ≃ Fin (ports n F a arity).length :=
  (List.Nodup.getEquivOfForallMemList (ports n F a arity) (original_ports_nodup n F a arity)
    (original_ports_complete n F a arity)).symm

/-- Position numbers are exactly the actual metadata's literal index search. -/
theorem portPosition_val (n F a : ℕ) (arity : Fin F → ℕ) (i : (e : Fin F) × Fin (arity e)) :
    (portPosition n F a arity i).val = (ports n F a arity).idxOf i := rfl

/-- Typed original occurrence to its ACTUAL replay placement position, in order. -/
def position (n F r a : ℕ) (arity : Fin F → ℕ)
    (owner : ((e : Fin F) × Fin (arity e)) → Fin n) :
    ((e : Fin F) × Fin (arity e)) ≃
      Fin (SemiprimeD1PacketReplayOriginal.acquire n F r a arity owner).placements.length :=
  (portPosition n F a arity).trans
    (finCongr (SemiprimeD1OriginalModeAcquisition.original_size n F r a arity owner).symm)

/-- Actual replay placement ordinals retain the original factor-major typed index. -/
theorem position_val (n F r a : ℕ) (arity : Fin F → ℕ)
    (owner : ((e : Fin F) × Fin (arity e)) → Fin n) (i : (e : Fin F) × Fin (arity e)) :
    (position n F r a arity owner i).val = (ports n F a arity).idxOf i := rfl

/-- Each computed replay position reads back the EXACT original typed occurrence. -/
theorem port_at_position (n F r a : ℕ) (arity : Fin F → ℕ)
    (owner : ((e : Fin F) × Fin (arity e)) → Fin n) (i : (e : Fin F) × Fin (arity e)) :
    (ports n F a arity)[(position n F r a arity owner i).val]'(by
      rw [position_val]; exact List.idxOf_lt_length_of_mem (original_ports_complete n F a arity i)) = i :=
  List.getElem_idxOf (List.idxOf_lt_length_of_mem (original_ports_complete n F a arity i))

/-- The actual original paired stream contains its exact typed occurrence and
placement at the computed position; no permutation or correspondence is advised. -/
theorem original_pair_at (n F r a : ℕ) (arity : Fin F → ℕ)
    (owner : ((e : Fin F) × Fin (arity e)) → Fin n) (i : (e : Fin F) × Fin (arity e)) :
    let j := position n F r a arity owner i
    ((ports n F a arity).zip (SemiprimeD1PacketReplayOriginal.acquire n F r a arity owner).placements)[j.val]? =
      some (i,(SemiprimeD1PacketReplayOriginal.acquire n F r a arity owner).placements[j.val]) := by
  dsimp only
  have hp : (position n F r a arity owner i).val < (ports n F a arity).length := by
    rw [position_val]
    exact List.idxOf_lt_length_of_mem (original_ports_complete n F a arity i)
  have hz : (position n F r a arity owner i).val <
      ((ports n F a arity).zip (SemiprimeD1PacketReplayOriginal.acquire n F r a arity owner).placements).length := by
    rw [List.length_zip]
    exact lt_min hp (position n F r a arity owner i).isLt
  rw [List.getElem?_eq_getElem hz,List.getElem_zip,port_at_position]

/-- The placement correspondence agrees with the concrete Network's canonical
global edge numbering, rather than merely with an abstract finite bijection. -/
theorem position_network_val {n : ℕ} (rows : Rows n) (r a : ℕ) (i : Incidence rows) :
    (position n rows.length r a (arity rows) (owner rows) i).val = edgeID rows i := by
  rw [position_val,SemiprimeD1TensorNetworkLayout.original_ports]
  rfl

end RiemannGaussian.SemiprimeD1OriginalIncidenceIndex
