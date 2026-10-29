/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1PacketReplayBudget

/-! # Actual replay metadata widths from its retained physical reports
The same step/replay recursion proves all observed packet and positive edge-ID
payloads are bounded by the retained replay report. No encoded width or packet
catalogue is supplied. Original report envelopes may then replace that report.
-/
set_option autoImplicit false
set_option maxHeartbeats 1200000
namespace RiemannGaussian.SemiprimeD1ReplayMetadataBounds
open SemiprimeD1PacketInventory SemiprimeSourceHistogramTrie
open SemiprimeSourceCompactBits SemiprimeBitArithmetic

/-- Actual physical compact-add output allocation is paid in its report. -/
theorem add_output_length (a b : List Bool) : (add a b).bits.length ≤ (add a b).clock := by
  have h:=trim_length (addBits a b false).bits
  have hc:=trim_clock (addBits a b false).bits
  unfold add
  dsimp only
  omega

/-- Every stored observed-packet payload and header is covered by the actual report. -/
def PacketBound (state : State) : Prop := state.packets.length ≤ state.clock ∧
  ∀p∈state.packets,p.length ≤ state.clock

/-- Empty observed storage satisfies the literal bound at every original seed. -/
theorem initial_bound (clock : ℕ) : PacketBound (initial clock) := by simp [PacketBound,initial]

/-- One physical replay step introduces at most one discovered packet. -/
theorem step_packet_count (dict : SemiprimeSourceHistogramRows.Dictionary) (a : ℕ)
    (state : State) (key : List Bool) :
    (step dict a state key).2.packets.length ≤ state.packets.length+1 := by
  simp only [step]
  split_ifs
  · simp only [List.length_cons];omega
  · omega

/-- Both actual output payload widths are paid in that SAME step's report. -/
theorem step_payload (dict : SemiprimeSourceHistogramRows.Dictionary) (a : ℕ)
    (state : State) (key : List Bool) :
    (step dict a state key).1.packet.length ≤ (step dict a state key).2.clock ∧
    (step dict a state key).1.edge.length ≤ (step dict a state key).2.clock := by
  have h:=add_output_length state.next [true]
  constructor
  · simp only [step,copy_clock]
    omega
  · change (increment state.next).bits.length ≤ _
    have hi : (increment state.next).bits.length ≤ (increment state.next).clock:=h
    change _ ≤ state.clock+_+_+_+(increment state.next).clock+_+_+_+_+_+25
    omega

/-- A physical orientation step cannot create more than the parsed row's axes. -/
theorem step_slots (dict : SemiprimeSourceHistogramRows.Dictionary) (a : ℕ)
    (state : State) (key : List Bool) : (step dict a state key).1.slot.length ≤ a := by
  exact (SemiprimeD1PacketReplayBudget.slots_length _ _ _).trans (SemiprimeD1PacketRows.parse_length _ _)

/-- Packet data bound preserved by the actual discovery/copy branch. -/
theorem step_bound (dict : SemiprimeSourceHistogramRows.Dictionary) (a : ℕ)
    (state : State) (key : List Bool) (hb : PacketBound state) :
    PacketBound (step dict a state key).2 := by
  have hr:=step_retains dict a state key
  have hp:=(step_payload dict a state key).1
  have hbold:=hb.1
  constructor
  · have hc:=step_packet_count dict a state key
    have hstrict : state.clock+1 ≤ (step dict a state key).2.clock := by unfold step;dsimp only;omega
    omega
  · intro p hm
    simp only [step,copy_bits] at hm
    split_ifs at hm
    · rcases List.mem_cons.mp hm with rfl|hm
      · exact hp
      · exact (hb.2 p hm).trans hr
    · exact (hb.2 p hm).trans hr

/-- Every actual observed packet/header remains covered through the full replay. -/
theorem replay_bound (dict : SemiprimeSourceHistogramRows.Dictionary) (a : ℕ)
    (keys : List (List Bool)) (state : State) (hb : PacketBound state) :
    PacketBound (replay dict a keys state).2 := by
  induction keys generalizing state with
  | nil => exact hb
  | cons key keys ih => exact ih _ (step_bound dict a state key hb)

/-- Every generated real placement's payload and slot are bounded, including
all earlier placements still retained while later replay steps execute. -/
theorem replay_placements (dict : SemiprimeSourceHistogramRows.Dictionary) (a : ℕ)
    (keys : List (List Bool)) (state : State) :
    ∀p∈(replay dict a keys state).1,
      p.packet.length ≤ (replay dict a keys state).2.clock ∧
      p.edge.length ≤ (replay dict a keys state).2.clock ∧ p.slot.length ≤ a := by
  induction keys generalizing state with
  | nil => simp [replay]
  | cons key keys ih =>
    intro p hm
    change p∈(step dict a state key).1::(replay dict a keys (step dict a state key).2).1 at hm
    rcases List.mem_cons.mp hm with rfl|hm
    · have hp:=step_payload dict a state key
      have hr:=replay_retains dict a keys (step dict a state key).2
      exact ⟨hp.1.trans hr,hp.2.trans hr,step_slots dict a state key⟩
    · exact ih _ p hm

/-- The observed factor count is bounded by the REAL input stream, retaining duplicates. -/
theorem replay_count (dict : SemiprimeSourceHistogramRows.Dictionary) (a : ℕ)
    (keys : List (List Bool)) (state : State) :
    (replay dict a keys state).2.packets.length ≤ state.packets.length+keys.length := by
  induction keys generalizing state with
  | nil => simp [replay]
  | cons key keys ih =>
    have ht:=ih (step dict a state key).2
    have hs:=step_packet_count dict a state key
    change (replay dict a keys (step dict a state key).2).2.packets.length ≤ _
    simp only [List.length_cons]
    omega

/-- Actual original acquisition satisfies the report-derived packet bound. -/
theorem original_packets (n F r a : ℕ) (arity : Fin F→ℕ)
    (owner : ((e : Fin F)×Fin (arity e))→Fin n) :
    PacketBound (SemiprimeD1PacketReplayOriginal.acquire n F r a arity owner).state :=
  replay_bound _ _ _ _ (initial_bound _)

/-- Actual original real placement bytes have derived widths, with no advice. -/
theorem original_placements (n F r a : ℕ) (arity : Fin F→ℕ)
    (owner : ((e : Fin F)×Fin (arity e))→Fin n) :
    ∀p∈(SemiprimeD1PacketReplayOriginal.acquire n F r a arity owner).placements,
      p.packet.length ≤ (SemiprimeD1PacketReplayOriginal.acquire n F r a arity owner).state.clock ∧
      p.edge.length ≤ (SemiprimeD1PacketReplayOriginal.acquire n F r a arity owner).state.clock ∧
      p.slot.length ≤ a := replay_placements _ _ _ _

/-- No original observed factor count exceeds the actual number of input occurrences. -/
theorem original_count (n F r a : ℕ) (arity : Fin F→ℕ)
    (owner : ((e : Fin F)×Fin (arity e))→Fin n) :
    (SemiprimeD1PacketReplayOriginal.acquire n F r a arity owner).state.packets.length ≤ ∑e,arity e := by
  have h:=replay_count (SemiprimeD1PacketPadding.acquire n F r a arity owner).source.selection.cache.rows.source.dictionary
    a (SemiprimeD1PacketPadding.acquire n F r a arity owner).source.keys
    (initial (SemiprimeD1PacketPadding.acquire n F r a arity owner).clock)
  simp only [initial,List.length_nil,Nat.zero_add] at h
  change _ ≤ (SemiprimeD1IncidenceAcquisition.acquire n F r a arity owner).keys.length at h
  exact h.trans (SemiprimeD1IncidenceAcquisitionBounds.keys_length n F r a arity owner).le

end RiemannGaussian.SemiprimeD1ReplayMetadataBounds
