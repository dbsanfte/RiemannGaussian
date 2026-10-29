/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1PacketRows
import RiemannGaussian.SemiprimeSourceHistogramTrieStore

/-! # Sparse replay inventory of actual real ports
Each original occurrence is replayed once. Its old class counter is the padding
index; the physical orientation produces packet and slot bytes. Only observed
packet keys are recorded. Slot payloads are positive physical occurrence IDs.
Global slot injectivity/capacity is a separate obligation, not a runtime oracle.
-/
set_option autoImplicit false
namespace RiemannGaussian.SemiprimeD1PacketInventory
open SemiprimeSourceHistogramTrie

/-- One acquired real-port placement, in original occurrence order. -/
structure Placement where
  /-- Original selected pair bytes. -/
  source : List Bool
  /-- Old class-frequency bytes copied by the same bump traversal. -/
  padding : List Bool
  /-- Actual generated packet key. -/
  packet : List Bool
  /-- Actual orientation slot. -/
  slot : List Bool
  /-- Positive original occurrence ID, physically incremented. -/
  edge : List Bool
  /-- Parser and equal-row-shape flags. -/
  valid : Bool

/-- Sparse persistent inventory, with no full orbit or palette catalogue. -/
structure State where
  /-- Original pair-class frequencies during replay. -/
  classes : Trie
  /-- Marker map for observed packet keys only. -/
  seen : Trie
  /-- Actual distinct-key insertion candidates, in reverse discovery order. -/
  packets : List (List Bool)
  /-- Framed packet/slot map to positive original occurrence IDs. -/
  slots : Trie
  /-- Last assigned occurrence ID. -/
  next : List Bool
  /-- Retained producer, reader, replay and control reports. -/
  clock : ℕ

/-- Start replay with the already paid original acquisition retained exactly once. -/
def initial (clock : ℕ) : State := ⟨.empty,.empty,[],.empty,[],clock+2⟩

/-- One literal replay step. No native labels or semantic row getters execute. -/
def step (dict : SemiprimeSourceHistogramRows.Dictionary) (a : ℕ)
    (state : State) (key : List Bool) : Placement × State :=
  let changed := bump state.classes key
  let rows := SemiprimeD1PacketRows.read dict a key
  let oriented := SemiprimeD1OrientationBits.acquire rows.left rows.right changed.old
  let id := SemiprimeSourceCompactBits.increment state.next
  let address := SemiprimeSourceHistogramKeyBits.pair oriented.key oriented.slots
  let written := SemiprimeSourceHistogramTrieStore.put state.slots address.bits id.bits
  let present := lookup state.seen oriented.key
  let marked := SemiprimeSourceHistogramTrieStore.put state.seen oriented.key [true]
  let copied := SemiprimeSourceCompactBits.copy oriented.key
  let fresh := present.bits.isEmpty
  let packets := if fresh then copied.bits::state.packets else state.packets
  let out := ⟨changed.trie,marked.trie,packets,written.trie,id.bits,
    state.clock+changed.clock+rows.clock+oriented.clock+id.clock+address.clock+
      written.clock+present.clock+marked.clock+copied.clock+25⟩
  (⟨key,changed.old,oriented.key,oriented.slots,id.bits,rows.valid && oriented.valid⟩,out)

/-- Actual same-order traversal of the original selected-pair stream. -/
def replay (dict : SemiprimeSourceHistogramRows.Dictionary) (a : ℕ)
    : List (List Bool) → State → List Placement × State
  | [],state => ([],state)
  | key::keys,state =>
    let here := step dict a state key
    let tail := replay dict a keys here.2
    (here.1::tail.1,tail.2)

/-- Retained original selection and sparse placements; no supplied answer fields. -/
structure Acquired (n F a : ℕ) (arity : Fin F→ℕ) where
  /-- Once-acquired original cache, selected IDs, real keys and frequency state. -/
  source : SemiprimeD1IncidenceAcquisition.Acquired n F a arity
  /-- One placement per actual original occurrence. -/
  placements : List Placement
  /-- Final sparse replay inventory and complete retained report. -/
  state : State

/-- Original-input endpoint: acquire once, then replay only its actual real keys. -/
def acquire (n F r a : ℕ) (arity : Fin F→ℕ)
    (owner : ((e : Fin F)×Fin (arity e))→Fin n) : Acquired n F a arity :=
  let source := SemiprimeD1IncidenceAcquisition.acquire n F r a arity owner
  let out := replay source.selection.cache.rows.source.dictionary a source.keys
    (initial source.state.clock)
  ⟨source,out.1,out.2⟩

/-- Replay preserves every original occurrence and its exact order/multiplicity. -/
theorem replay_sources (dict : SemiprimeSourceHistogramRows.Dictionary) (a : ℕ)
    (keys : List (List Bool)) (state : State) :
    ((replay dict a keys state).1.map Placement.source)=keys := by
  induction keys generalizing state with
  | nil => rfl
  | cons key keys ih => simp only [replay,List.map_cons,step,ih]

/-- Every original real port appears once, even parallel equal-key occurrences. -/
theorem acquire_sources (n F r a : ℕ) (arity : Fin F→ℕ)
    (owner : ((e : Fin F)×Fin (arity e))→Fin n) :
    ((acquire n F r a arity owner).placements.map Placement.source)=
      (SemiprimeD1IncidenceAcquisition.acquire n F r a arity owner).keys :=
  replay_sources _ _ _ _

/-- Exact old counter from the very same executed update, not an advised index. -/
theorem step_padding (dict : SemiprimeSourceHistogramRows.Dictionary) (a : ℕ)
    (state : State) (key : List Bool) :
    (step dict a state key).1.padding=stored state.classes key := bump_old _ _

/-- The positive occurrence counter really advances by one. -/
theorem step_edge (dict : SemiprimeSourceHistogramRows.Dictionary) (a : ℕ)
    (state : State) (key : List Bool) :
    SemiprimeBitArithmetic.bitValue (step dict a state key).1.edge=
      SemiprimeBitArithmetic.bitValue state.next+1 :=
  SemiprimeSourceCompactBits.increment_value _

/-- Exact per-key replay frequency transition, including missing and prefix keys. -/
theorem step_frequency (dict : SemiprimeSourceHistogramRows.Dictionary) (a : ℕ)
    (state : State) (key query : List Bool) :
    value (step dict a state key).2.classes query=
      if query=key then value state.classes query+1 else value state.classes query :=
  bump_value _ _ _

/-- The just-produced packet/slot address really stores this positive edge ID.
Global preservation for other steps additionally needs slot-address injectivity. -/
theorem step_slot (dict : SemiprimeSourceHistogramRows.Dictionary) (a : ℕ)
    (state : State) (key : List Bool) :
    stored (step dict a state key).2.slots
      (SemiprimeSourceHistogramKeyBits.frame (step dict a state key).1.packet
        (step dict a state key).1.slot)=(step dict a state key).1.edge := by
  simp only [step,SemiprimeSourceHistogramKeyBits.pair_bits,
    SemiprimeSourceHistogramTrieStore.put_stored,ite_true]

/-- No earlier producer/read/replay report is dropped by one step. -/
theorem step_retains (dict : SemiprimeSourceHistogramRows.Dictionary) (a : ℕ)
    (state : State) (key : List Bool) : state.clock≤(step dict a state key).2.clock := by
  unfold step
  dsimp only
  omega

/-- The final report retains the entire actual traversal prefix. -/
theorem replay_retains (dict : SemiprimeSourceHistogramRows.Dictionary) (a : ℕ)
    (keys : List (List Bool)) (state : State) :
    state.clock≤(replay dict a keys state).2.clock := by
  induction keys generalizing state with
  | nil => exact le_rfl
  | cons key keys ih => exact le_trans (step_retains dict a state key) (ih _)

/-- Later occurrences cannot reuse a class index already present at entry. -/
theorem replay_padding_lower (dict : SemiprimeSourceHistogramRows.Dictionary) (a : ℕ)
    (keys : List (List Bool)) (state : State) (out : Placement)
    (hout : out∈(replay dict a keys state).1) :
    value state.classes out.source≤SemiprimeBitArithmetic.bitValue out.padding := by
  induction keys generalizing state with
  | nil => simp [replay] at hout
  | cons key keys ih =>
    change out∈(step dict a state key).1::(replay dict a keys (step dict a state key).2).1 at hout
    rcases List.mem_cons.mp hout with h|h
    · subst out
      rw [step_padding]
      exact le_rfl
    · have hh := ih (step dict a state key).2 h
      have hm : value state.classes out.source≤value (step dict a state key).2.classes out.source := by
        rw [step_frequency]
        split_ifs <;> omega
      exact le_trans hm hh

/-- Distinct real occurrences have distinct (original class, padding) pairs. -/
theorem replay_indices_nodup (dict : SemiprimeSourceHistogramRows.Dictionary) (a : ℕ)
    (keys : List (List Bool)) (state : State) :
    ((replay dict a keys state).1.map (fun p => (p.source,SemiprimeBitArithmetic.bitValue p.padding))).Nodup := by
  induction keys generalizing state with
  | nil => exact List.nodup_nil
  | cons key keys ih =>
    rw [replay,List.map_cons,List.nodup_cons]
    refine ⟨?_,ih _⟩
    intro hm
    obtain ⟨out,hout,heq⟩ := List.mem_map.mp hm
    have hs : out.source=key := congrArg Prod.fst heq
    have hv := congrArg Prod.snd heq
    have hl := replay_padding_lower dict a keys (step dict a state key).2 out hout
    rw [hs,step_frequency] at hl
    simp only [ite_true] at hl
    have old : SemiprimeBitArithmetic.bitValue (step dict a state key).1.padding=value state.classes key := by
      rw [step_padding]
      rfl
    rw [old] at hv
    omega

/-- Exact sparse discovery-marker invariant; no bucket coverage is supplied. -/
def SeenGood (state : State) : Prop := state.packets.Nodup ∧
  ∀ key,stored state.seen key=if key∈state.packets then [true] else []

/-- The empty discovery state satisfies its concrete marker invariant. -/
theorem initial_seen (clock : ℕ) : SeenGood (initial clock) := by
  refine ⟨List.nodup_nil,?_⟩
  intro key
  simp only [initial,stored_empty,List.not_mem_nil,ite_false]

/-- Exactly first observations enter the sparse packet list. -/
theorem step_seen (dict : SemiprimeSourceHistogramRows.Dictionary) (a : ℕ)
    (state : State) (key : List Bool) (hg : SeenGood state) :
    SeenGood (step dict a state key).2 := by
  let packet := (SemiprimeD1OrientationBits.acquire
    (SemiprimeD1PacketRows.read dict a key).left
    (SemiprimeD1PacketRows.read dict a key).right (bump state.classes key).old).key
  have hp : (lookup state.seen packet).bits=if packet∈state.packets then [true] else [] := by
    rw [lookup_bits,hg.2]
  have hpacks : (step dict a state key).2.packets=
      if packet∈state.packets then state.packets else packet::state.packets := by
    change (if (lookup state.seen packet).bits.isEmpty then
      (SemiprimeSourceCompactBits.copy packet).bits::state.packets else state.packets)=_
    rw [hp,SemiprimeSourceCompactBits.copy_bits]
    by_cases hm : packet∈state.packets <;> simp only [hm,ite_true,ite_false,List.isEmpty_cons,
      List.isEmpty_nil,Bool.false_eq_true]
  constructor
  · rw [hpacks]
    split_ifs with hm
    · exact hg.1
    · exact List.nodup_cons.mpr ⟨hm,hg.1⟩
  · intro query
    change stored (SemiprimeSourceHistogramTrieStore.put state.seen packet [true]).trie query=_
    rw [SemiprimeSourceHistogramTrieStore.put_stored,hg.2,hpacks]
    by_cases hm : packet∈state.packets <;> by_cases he : query=packet <;> simp [hm,he]

/-- Discovery list remains duplicate-free after the actual entire replay. -/
theorem replay_seen (dict : SemiprimeSourceHistogramRows.Dictionary) (a : ℕ)
    (keys : List (List Bool)) (state : State) (hg : SeenGood state) :
    SeenGood (replay dict a keys state).2 := by
  induction keys generalizing state with
  | nil => exact hg
  | cons key keys ih => exact ih _ (step_seen dict a state key hg)

/-- Exact actual per-class frequency after replay, including every multiplicity. -/
theorem replay_frequency (dict : SemiprimeSourceHistogramRows.Dictionary) (a : ℕ)
    (keys : List (List Bool)) (state : State) (query : List Bool) :
    value (replay dict a keys state).2.classes query=value state.classes query+keys.count query := by
  induction keys generalizing state with
  | nil => simp only [replay,List.count_nil,Nat.add_zero]
  | cons key keys ih =>
    rw [replay,ih,step_frequency,List.count_cons]
    by_cases he : query=key
    · subst query
      simp
      omega
    · have hb : (key==query)=false := by simp [Ne.symm he]
      simp only [he,ite_false,hb,Bool.false_eq_true,ite_false]
      omega

/-- No class count decreases during the literal suffix traversal. -/
theorem replay_frequency_mono (dict : SemiprimeSourceHistogramRows.Dictionary) (a : ℕ)
    (keys : List (List Bool)) (state : State) (query : List Bool) :
    value state.classes query≤value (replay dict a keys state).2.classes query := by
  rw [replay_frequency]
  omega

/-- Every copied old class counter is strictly below its final actual load. -/
theorem replay_padding_upper (dict : SemiprimeSourceHistogramRows.Dictionary) (a : ℕ)
    (keys : List (List Bool)) (state : State) (out : Placement)
    (hout : out∈(replay dict a keys state).1) :
    SemiprimeBitArithmetic.bitValue out.padding<value (replay dict a keys state).2.classes out.source := by
  induction keys generalizing state with
  | nil => simp [replay] at hout
  | cons key keys ih =>
    change out∈(step dict a state key).1::(replay dict a keys (step dict a state key).2).1 at hout
    rcases List.mem_cons.mp hout with h|h
    · subst out
      have hm := replay_frequency_mono dict a keys (step dict a state key).2 key
      change SemiprimeBitArithmetic.bitValue (step dict a state key).1.padding<_
      rw [step_padding]
      have hs := step_frequency dict a state key key
      simp only [ite_true] at hs
      change SemiprimeBitArithmetic.bitValue (stored state.classes key)<_
      change value state.classes key<_
      change value state.classes key<value (replay dict a keys (step dict a state key).2).2.classes key
      omega
    · exact ih (step dict a state key).2 h

/-- Original compact frequency counters give compact copied old indices. -/
theorem replay_padding_compact (dict : SemiprimeSourceHistogramRows.Dictionary) (a : ℕ)
    (keys : List (List Bool)) (state : State) (hc : CompactCounters state.classes)
    (out : Placement) (hout : out∈(replay dict a keys state).1) :
    SemiprimeSourceCompactBits.Compact out.padding := by
  induction keys generalizing state with
  | nil => simp [replay] at hout
  | cons key keys ih =>
    change out∈(step dict a state key).1::(replay dict a keys (step dict a state key).2).1 at hout
    rcases List.mem_cons.mp hout with h|h
    · subst out
      rw [step_padding]
      exact hc key
    · exact ih _ (bump_compact state.classes key hc) h

/-- Each retained placement is literally the physical reader/orientation output. -/
theorem replay_oriented (dict : SemiprimeSourceHistogramRows.Dictionary) (a : ℕ)
    (keys : List (List Bool)) (state : State) (out : Placement)
    (hout : out∈(replay dict a keys state).1) :
    let rows := SemiprimeD1PacketRows.read dict a out.source
    let oriented := SemiprimeD1OrientationBits.acquire rows.left rows.right out.padding
    out.packet=oriented.key ∧ out.slot=oriented.slots ∧ out.valid=(rows.valid && oriented.valid) := by
  induction keys generalizing state with
  | nil => simp [replay] at hout
  | cons key keys ih =>
    change out∈(step dict a state key).1::(replay dict a keys (step dict a state key).2).1 at hout
    rcases List.mem_cons.mp hout with h|h
    · subst out
      exact ⟨rfl,rfl,rfl⟩
    · exact ih _ h

/-- Sparse discovery records only keys of genuinely generated real placements. -/
theorem replay_packets_generated (dict : SemiprimeSourceHistogramRows.Dictionary) (a : ℕ)
    (keys : List (List Bool)) (state : State) (packet : List Bool)
    (hp : packet∈(replay dict a keys state).2.packets) :
    packet∈state.packets ∨ ∃ out∈(replay dict a keys state).1,out.packet=packet := by
  induction keys generalizing state with
  | nil => exact Or.inl hp
  | cons key keys ih =>
    rcases ih (step dict a state key).2 hp with h|h
    · change packet∈(if _ then _ else state.packets) at h
      split_ifs at h with hf
      · rcases List.mem_cons.mp h with he|he
        · right
          refine ⟨(step dict a state key).1,List.mem_cons_self,?_⟩
          simpa only [step,SemiprimeSourceCompactBits.copy_bits] using he.symm
        · exact Or.inl he
      · exact Or.inl h
    · right
      obtain ⟨out,ho,he⟩ := h
      exact ⟨out,List.mem_cons_of_mem _ ho,he⟩

/-- Exact physical slot-address layout used by the insertion call. -/
def slotAddress (out : Placement) : List Bool :=
  SemiprimeSourceHistogramKeyBits.frame out.packet out.slot

/-- A suffix that writes no selected address preserves its exact stored bytes. -/
theorem replay_preserves (dict : SemiprimeSourceHistogramRows.Dictionary) (a : ℕ)
    (keys : List (List Bool)) (state : State) (address : List Bool)
    (ha : address∉(replay dict a keys state).1.map slotAddress) :
    stored (replay dict a keys state).2.slots address=stored state.slots address := by
  induction keys generalizing state with
  | nil => rfl
  | cons key keys ih =>
    change address∉slotAddress (step dict a state key).1::
      ((replay dict a keys (step dict a state key).2).1.map slotAddress) at ha
    have hh := ih (step dict a state key).2 (fun hm => ha (List.mem_cons_of_mem _ hm))
    change stored (replay dict a keys (step dict a state key).2).2.slots address=_
    rw [hh]
    have hn : address≠slotAddress (step dict a state key).1 := by
      intro he
      exact ha (List.mem_cons.mpr (Or.inl he))
    have hput := SemiprimeSourceHistogramTrieStore.put_stored state.slots
      (slotAddress (step dict a state key).1) (step dict a state key).1.edge address
    simp only [hn,ite_false] at hput
    simpa only [step,slotAddress,SemiprimeSourceHistogramKeyBits.pair_bits] using hput

/-- Without duplicate generated addresses, the final sparse dictionary returns
exactly the actual occurrence ID of every real port, not merely its last writer. -/
theorem replay_lookup (dict : SemiprimeSourceHistogramRows.Dictionary) (a : ℕ)
    (keys : List (List Bool)) (state : State)
    (hn : ((replay dict a keys state).1.map slotAddress).Nodup)
    (out : Placement) (ho : out∈(replay dict a keys state).1) :
    stored (replay dict a keys state).2.slots (slotAddress out)=out.edge := by
  induction keys generalizing state with
  | nil => simp [replay] at ho
  | cons key keys ih =>
    change (slotAddress (step dict a state key).1::
      ((replay dict a keys (step dict a state key).2).1.map slotAddress)).Nodup at hn
    have hnd := List.nodup_cons.mp hn
    change out∈(step dict a state key).1::(replay dict a keys (step dict a state key).2).1 at ho
    rcases List.mem_cons.mp ho with he|he
    · subst out
      change stored (replay dict a keys (step dict a state key).2).2.slots _=_
      rw [replay_preserves dict a keys (step dict a state key).2 _ hnd.1]
      exact step_slot _ _ _ _
    · exact ih (step dict a state key).2 hnd.2 he

/-- Physical occurrence IDs are positive and grow beyond the entry counter. -/
theorem replay_edge_lower (dict : SemiprimeSourceHistogramRows.Dictionary) (a : ℕ)
    (keys : List (List Bool)) (state : State) (out : Placement)
    (ho : out∈(replay dict a keys state).1) :
    SemiprimeBitArithmetic.bitValue state.next<SemiprimeBitArithmetic.bitValue out.edge := by
  induction keys generalizing state with
  | nil => simp [replay] at ho
  | cons key keys ih =>
    change out∈(step dict a state key).1::(replay dict a keys (step dict a state key).2).1 at ho
    rcases List.mem_cons.mp ho with h|h
    · subst out
      rw [step_edge]
      omega
    · have hh := ih (step dict a state key).2 h
      have hn : SemiprimeBitArithmetic.bitValue (step dict a state key).2.next=
          SemiprimeBitArithmetic.bitValue state.next+1 := SemiprimeSourceCompactBits.increment_value _
      omega

/-- Literal positive edge IDs are exactly consecutive original occurrence numbers. -/
theorem replay_edges (dict : SemiprimeSourceHistogramRows.Dictionary) (a : ℕ)
    (keys : List (List Bool)) (state : State) :
    ((replay dict a keys state).1.map (fun out => SemiprimeBitArithmetic.bitValue out.edge))=
      List.range' (SemiprimeBitArithmetic.bitValue state.next+1) keys.length := by
  induction keys generalizing state with
  | nil => rfl
  | cons key keys ih =>
    change SemiprimeBitArithmetic.bitValue (step dict a state key).1.edge::
      ((replay dict a keys (step dict a state key).2).1.map _)=_
    rw [ih,step_edge]
    have hn : SemiprimeBitArithmetic.bitValue (step dict a state key).2.next=
        SemiprimeBitArithmetic.bitValue state.next+1 := SemiprimeSourceCompactBits.increment_value _
    rw [hn]
    simp only [List.length_cons,List.range'_succ,Nat.add_assoc]

/-- Physical lookup of a completed packet slot, including address framing/read. -/
def lookupSlot (state : State) (packet slot : List Bool) : SemiprimeSourceCompactBits.Report :=
  let address := SemiprimeSourceHistogramKeyBits.pair packet slot
  let out := lookup state.slots address.bits
  ⟨out.bits,address.clock+out.clock+4⟩

/-- Literal byte semantics of the executed slot lookup. -/
theorem lookupSlot_bits (state : State) (packet slot : List Bool) :
    (lookupSlot state packet slot).bits=stored state.slots
      (SemiprimeSourceHistogramKeyBits.frame packet slot) := by
  simp only [lookupSlot,SemiprimeSourceHistogramKeyBits.pair_bits,lookup_bits]

end RiemannGaussian.SemiprimeD1PacketInventory
