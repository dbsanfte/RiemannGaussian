/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1PacketReplayOriginal

/-! # Every actual real placement belongs to the observed sparse packet inventory
The marker invariant proves a newly emitted packet is present. Literal packet
list preservation then carries it through every remaining replay step. This is
forward coverage of the executed inventory, not a supplied packet certificate.
-/
set_option autoImplicit false
set_option maxHeartbeats 2000000
namespace RiemannGaussian.SemiprimeD1PacketInventoryCoverage
open SemiprimeD1PacketInventory SemiprimeSourceHistogramTrie

/-- Literal packet discovery never drops a previously recorded packet. -/
theorem step_preserves_packet (dict : SemiprimeSourceHistogramRows.Dictionary) (a : ℕ)
    (state : State) (key packet : List Bool) (hp : packet ∈ state.packets) :
    packet ∈ (step dict a state key).2.packets := by
  change packet ∈ if _ then _::state.packets else state.packets
  split_ifs
  · exact List.mem_cons_of_mem _ hp
  · exact hp

/-- Every remaining original replay suffix preserves all already recorded packets. -/
theorem replay_preserves_packet (dict : SemiprimeSourceHistogramRows.Dictionary) (a : ℕ)
    (keys : List (List Bool)) (state : State) (packet : List Bool) (hp : packet ∈ state.packets) :
    packet ∈ (replay dict a keys state).2.packets := by
  induction keys generalizing state with
  | nil => exact hp
  | cons key keys ih => exact ih _ (step_preserves_packet dict a state key packet hp)

/-- The produced placement's own key is present after that SAME actual step. -/
theorem step_packet_mem (dict : SemiprimeSourceHistogramRows.Dictionary) (a : ℕ)
    (state : State) (key : List Bool) (hg : SeenGood state) :
    (step dict a state key).1.packet ∈ (step dict a state key).2.packets := by
  have hs := step_seen dict a state key hg
  have hw : stored (step dict a state key).2.seen (step dict a state key).1.packet = [true] := by
    simp only [step,SemiprimeSourceHistogramTrieStore.put_stored,ite_true]
  rw [hs.2] at hw
  by_contra hn
  simp only [hn,ite_false] at hw
  cases hw

/-- EVERY real placement emitted by replay belongs to its actual final sparse inventory. -/
theorem replay_placement_packet (dict : SemiprimeSourceHistogramRows.Dictionary) (a : ℕ)
    (keys : List (List Bool)) (state : State) (hg : SeenGood state) (out : Placement)
    (ho : out ∈ (replay dict a keys state).1) : out.packet ∈ (replay dict a keys state).2.packets := by
  induction keys generalizing state with
  | nil => simp only [replay,List.not_mem_nil] at ho
  | cons key keys ih =>
    change out ∈ (step dict a state key).1 :: (replay dict a keys (step dict a state key).2).1 at ho
    rcases List.mem_cons.mp ho with he | ht
    · subst out
      exact replay_preserves_packet dict a keys (step dict a state key).2 _ (step_packet_mem dict a state key hg)
    · exact ih _ (step_seen dict a state key hg) ht

/-- Closed original-input coverage: every actual placement has an actually observed packet. -/
theorem original_placement_packet (n F r a : ℕ) (arity : Fin F → ℕ)
    (owner : ((e : Fin F) × Fin (arity e)) → Fin n) (out : Placement)
    (ho : out ∈ (SemiprimeD1PacketReplayOriginal.acquire n F r a arity owner).placements) :
    out.packet ∈ (SemiprimeD1PacketReplayOriginal.acquire n F r a arity owner).state.packets :=
  replay_placement_packet _ _ _ _ (initial_seen _) out ho

end RiemannGaussian.SemiprimeD1PacketInventoryCoverage
