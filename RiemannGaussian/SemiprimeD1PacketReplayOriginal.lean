/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1PacketRowsOriginal
import RiemannGaussian.SemiprimeD1PacketPadding

/-! # Original-input sparse packet replay
Padding acquisition is executed once and its retained source feeds the physical
reader/orientation replay. Every original occurrence retains its own class index.
-/
set_option autoImplicit false
set_option maxHeartbeats 2400000
namespace RiemannGaussian.SemiprimeD1PacketReplayOriginal
open SemiprimeD1PacketInventory SemiprimeD1PacketRowsOriginal
open SemiprimeBitArithmetic SemiprimeSourceHistogramTrie

/-- Padding acquisition and its actual sparse replay inventory. -/
structure Acquired (n F a : ℕ) (arity : Fin F→ℕ) where
  /-- Once-acquired source and physical maximum/rounding result. -/
  padding : SemiprimeD1PacketPadding.Result n F a arity
  /-- Exact original-order real port placements. -/
  placements : List Placement
  /-- Sparse observed packets/slots and retained report. -/
  state : State

/-- The final endpoint pays original selection, padding and replay once each. -/
def acquire (n F r a : ℕ) (arity : Fin F→ℕ)
    (owner : ((e : Fin F)×Fin (arity e))→Fin n) : Acquired n F a arity :=
  let padding := SemiprimeD1PacketPadding.acquire n F r a arity owner
  let out := replay padding.source.selection.cache.rows.source.dictionary a padding.source.keys
    (initial padding.clock)
  ⟨padding,out.1,out.2⟩

/-- No original real occurrence is duplicated or omitted by replay. -/
theorem sources (n F r a : ℕ) (arity : Fin F→ℕ)
    (owner : ((e : Fin F)×Fin (arity e))→Fin n) :
    ((acquire n F r a arity owner).placements.map Placement.source)=
      (SemiprimeD1IncidenceAcquisition.acquire n F r a arity owner).keys :=
  replay_sources _ _ _ _

/-- Discovery stores only distinct observed packet keys, never a full orbit bank. -/
theorem packets_nodup (n F r a : ℕ) (arity : Fin F→ℕ)
    (owner : ((e : Fin F)×Fin (arity e))→Fin n) :
    (acquire n F r a arity owner).state.packets.Nodup :=
  (replay_seen _ _ _ _ (initial_seen _)).1

/-- Complete original producer and physical-padding reports remain in the result. -/
theorem retains_padding (n F r a : ℕ) (arity : Fin F→ℕ)
    (owner : ((e : Fin F)×Fin (arity e))→Fin n) :
    (SemiprimeD1PacketPadding.acquire n F r a arity owner).clock≤
      (acquire n F r a arity owner).state.clock := by
  change _≤(replay _ _ _ (initial (SemiprimeD1PacketPadding.acquire n F r a arity owner).clock)).2.clock
  have hh := replay_retains
    (SemiprimeD1PacketPadding.acquire n F r a arity owner).source.selection.cache.rows.source.dictionary a
    (SemiprimeD1PacketPadding.acquire n F r a arity owner).source.keys
    (initial (SemiprimeD1PacketPadding.acquire n F r a arity owner).clock)
  exact le_trans (Nat.le_add_right _ 2) hh

/-- A real port's replay index is below its physically acquired padding bound. -/
theorem padding_lt (n F r a : ℕ) (arity : Fin F→ℕ)
    (owner : ((e : Fin F)×Fin (arity e))→Fin n) (out : Placement)
    (ho : out∈(acquire n F r a arity owner).placements) :
    bitValue out.padding<bitValue (acquire n F r a arity owner).padding.padding := by
  have hu := replay_padding_upper _ _ _ _ out ho
  rw [replay_frequency] at hu
  change bitValue out.padding<value .empty out.source+_ at hu
  simp only [value,stored_empty,bitValue] at hu
  have hg := (SemiprimeD1IncidenceAcquisition.acquire_good n F r a arity owner).1 out.source
  have hb := SemiprimeD1PacketPadding.stored_le_padding n F r a arity owner out.source
  change value (SemiprimeD1IncidenceAcquisition.acquire n F r a arity owner).state.trie out.source≤_ at hb
  rw [hg] at hb
  simp only [Nat.zero_add] at hu
  exact lt_of_lt_of_le hu hb

/-- Canonical palette fields have no aliases. This is erased proof data only. -/
theorem fields_injective {r a : ℕ} : Function.Injective
    (SemiprimeD1OrientationPalette.fields (r:=r) (a:=a)) := by
  intro left right he
  apply List.ofFn_injective at he
  funext q
  apply Fin.ext
  have h := congrArg (fun f => bitValue (f q)) he
  simpa only [SemiprimeSourceHistogramHeadRefinement.numberKey_value] using h

/-- All original source keys read equal-shape rows and distinct keys cannot alias. -/
theorem reader_injective (n F r a : ℕ) [NeZero r] (arity : Fin F→ℕ)
    (owner : ((e : Fin F)×Fin (arity e))→Fin n)
    (key key' : List Bool)
    (hk : key∈(SemiprimeD1IncidenceAcquisition.acquire n F r a arity owner).keys)
    (hk' : key'∈(SemiprimeD1IncidenceAcquisition.acquire n F r a arity owner).keys)
    (hl : (SemiprimeD1PacketRows.read
      (SemiprimeD1IncidenceAcquisition.acquire n F r a arity owner).selection.cache.rows.source.dictionary a key).left=
      (SemiprimeD1PacketRows.read
      (SemiprimeD1IncidenceAcquisition.acquire n F r a arity owner).selection.cache.rows.source.dictionary a key').left)
    (hr : (SemiprimeD1PacketRows.read
      (SemiprimeD1IncidenceAcquisition.acquire n F r a arity owner).selection.cache.rows.source.dictionary a key).right=
      (SemiprimeD1PacketRows.read
      (SemiprimeD1IncidenceAcquisition.acquire n F r a arity owner).selection.cache.rows.source.dictionary a key').right) : key=key' := by
  rw [SemiprimeD1IncidenceAcquisition.keys_original] at hk hk'
  obtain ⟨i,_,rfl⟩ := List.mem_map.mp hk
  obtain ⟨j,_,rfl⟩ := List.mem_map.mp hk'
  have hi := original_read n F r a arity owner i
  have hj := original_read n F r a arity owner j
  change (originalRead n F r a arity owner i).left=(originalRead n F r a arity owner j).left at hl
  change (originalRead n F r a arity owner i).right=(originalRead n F r a arity owner j).right at hr
  rw [hi.1,hj.1] at hl
  rw [hi.2.1,hj.2.1] at hr
  apply (SemiprimeD1IncidenceAcquisition.originalKey_eq_iff n F r a arity owner i j).mpr
  exact Prod.ext (fields_injective hl) (fields_injective hr)

/-- Canonical palette fields derive their bounds from the original finite colours. -/
theorem fields_allowed {r a : ℕ} (word : OAI.Algorithms.SubexponentialSAT.MulticolorTypes.Word r a) :
    SemiprimeD1OrientationPalette.Allowed r (SemiprimeD1OrientationPalette.fields word) := by
  intro colour hc
  rw [SemiprimeD1OrientationPalette.fields,List.mem_ofFn] at hc
  obtain ⟨q,rfl⟩ := hc
  refine ⟨SemiprimeSourceHistogramHeadRefinement.numberKey_compact _,?_⟩
  rw [SemiprimeSourceHistogramHeadRefinement.numberKey_value]
  exact (word q).isLt

/-- Every actual input key has original palette rows of the original coordinate length. -/
theorem row_properties (n F r a : ℕ) [NeZero r] (arity : Fin F→ℕ)
    (owner : ((e : Fin F)×Fin (arity e))→Fin n) (key : List Bool)
    (hk : key∈(SemiprimeD1IncidenceAcquisition.acquire n F r a arity owner).keys) :
    let rows := SemiprimeD1PacketRows.read
      (SemiprimeD1IncidenceAcquisition.acquire n F r a arity owner).selection.cache.rows.source.dictionary a key
    rows.left.length=a ∧ rows.right.length=a ∧
      SemiprimeD1OrientationPalette.Allowed r rows.left ∧
      SemiprimeD1OrientationPalette.Allowed r rows.right ∧ rows.valid=true := by
  rw [SemiprimeD1IncidenceAcquisition.keys_original] at hk
  obtain ⟨i,_,rfl⟩ := List.mem_map.mp hk
  have hi := original_read n F r a arity owner i
  dsimp only [originalRead] at hi
  dsimp only
  rw [hi.1,hi.2.1,hi.2.2]
  exact ⟨List.length_ofFn, List.length_ofFn,fields_allowed _,fields_allowed _,rfl⟩

/-- Each observed packet is generated from genuine original palette rows and an
actual compact padding index strictly below the physically acquired bound. -/
theorem observed_generated (n F r a : ℕ) [NeZero r] (arity : Fin F→ℕ)
    (owner : ((e : Fin F)×Fin (arity e))→Fin n) (packet : List Bool)
    (hp : packet∈(acquire n F r a arity owner).state.packets) :
    ∃ left right : List (List Bool),∃ j : List Bool,
      left.length=a ∧ right.length=a ∧
      SemiprimeD1OrientationPalette.Allowed r left ∧
      SemiprimeD1OrientationPalette.Allowed r right ∧
      SemiprimeSourceCompactBits.Compact j ∧
      bitValue j<bitValue (acquire n F r a arity owner).padding.padding ∧
      (SemiprimeD1OrientationBits.acquire left right j).key=packet := by
  have he := replay_packets_generated _ _ _ _ packet hp
  rcases he with h|⟨out,ho,he⟩
  · exact False.elim (List.not_mem_nil h)
  · have hm : out.source∈(SemiprimeD1IncidenceAcquisition.acquire n F r a arity owner).keys := by
      rw [←sources n F r a arity owner]
      exact List.mem_map.mpr ⟨out,ho,rfl⟩
    have hr := row_properties n F r a arity owner out.source hm
    have hor := replay_oriented _ _ _ _ out ho
    have hc := replay_padding_compact _ _ _ _ empty_compact out ho
    have hj := padding_lt n F r a arity owner out ho
    refine ⟨_,_,out.padding,hr.1,hr.2.1,hr.2.2.1,hr.2.2.2.1,hc,hj,?_⟩
    exact hor.1.symm.trans he

/-- No two actual real occurrences address the same generated packet slot. -/
theorem slots_nodup (n F r a : ℕ) [NeZero r] (arity : Fin F→ℕ)
    (owner : ((e : Fin F)×Fin (arity e))→Fin n) :
    ((acquire n F r a arity owner).placements.map
      (fun out => SemiprimeSourceHistogramKeyBits.frame out.packet out.slot)).Nodup := by
  let source := SemiprimeD1IncidenceAcquisition.acquire n F r a arity owner
  let dict := source.selection.cache.rows.source.dictionary
  let state := initial (SemiprimeD1PacketPadding.acquire n F r a arity owner).clock
  change ((replay dict a source.keys state).1.map _).Nodup
  have hn := replay_indices_nodup dict a source.keys state
  have hn' := List.Nodup.of_map _ hn
  apply hn'.map_on
  intro left hl right hr he
  have hk := (SemiprimeSourceHistogramKeyBits.frame_injective _ _ _ _ he).1
  have hs := (SemiprimeSourceHistogramKeyBits.frame_injective _ _ _ _ he).2
  have hls : left.source∈source.keys := by
    rw [←replay_sources dict a source.keys state]
    exact List.mem_map.mpr ⟨left,hl,rfl⟩
  have hrs : right.source∈source.keys := by
    rw [←replay_sources dict a source.keys state]
    exact List.mem_map.mpr ⟨right,hr,rfl⟩
  have hlrow := row_properties n F r a arity owner left.source hls
  have hrrow := row_properties n F r a arity owner right.source hrs
  have hlp := replay_oriented dict a source.keys state left hl
  have hrp := replay_oriented dict a source.keys state right hr
  have hcl := replay_padding_compact dict a source.keys state empty_compact left hl
  have hcr := replay_padding_compact dict a source.keys state empty_compact right hr
  rw [hlp.1,hrp.1] at hk
  rw [hlp.2.1,hrp.2.1] at hs
  have hinv := SemiprimeD1OrientationInverse.injective _ _ _ _ left.padding right.padding
    (hlrow.1.trans hlrow.2.1.symm) (hrrow.1.trans hrrow.2.1.symm) hcl hcr hk hs
  have hsource := reader_injective n F r a arity owner left.source right.source hls hrs hinv.1 hinv.2.1
  apply List.inj_on_of_nodup_map hn hl hr
  exact Prod.ext hsource (congrArg bitValue hinv.2.2)

/-- Actual final dictionary lookup returns the correct positive original edge ID. -/
theorem slot_lookup (n F r a : ℕ) [NeZero r] (arity : Fin F→ℕ)
    (owner : ((e : Fin F)×Fin (arity e))→Fin n) (out : Placement)
    (ho : out∈(acquire n F r a arity owner).placements) :
    stored (acquire n F r a arity owner).state.slots (slotAddress out)=out.edge := by
  exact replay_lookup _ _ _ _ (slots_nodup n F r a arity owner) out ho

/-- Zero remains reserved for unused slots; every real port has a positive ID. -/
theorem edge_positive (n F r a : ℕ) (arity : Fin F→ℕ)
    (owner : ((e : Fin F)×Fin (arity e))→Fin n) (out : Placement)
    (ho : out∈(acquire n F r a arity owner).placements) : 0<bitValue out.edge := by
  exact replay_edge_lower _ _ _ _ out ho

/-- Every actual real placement has a valid length-a physical orientation slot. -/
theorem placement_valid (n F r a : ℕ) [NeZero r] (arity : Fin F→ℕ)
    (owner : ((e : Fin F)×Fin (arity e))→Fin n) (out : Placement)
    (ho : out∈(acquire n F r a arity owner).placements) :
    out.valid=true ∧ out.slot.length=a := by
  have hm : out.source∈(SemiprimeD1IncidenceAcquisition.acquire n F r a arity owner).keys := by
    rw [←sources n F r a arity owner]
    exact List.mem_map.mpr ⟨out,ho,rfl⟩
  have hr := row_properties n F r a arity owner out.source hm
  have hh := replay_oriented _ _ _ _ out ho
  simp only [SemiprimeD1PacketPadding.acquire_source] at hh
  have hshape := hr.1.trans hr.2.1.symm
  have hv := (SemiprimeD1OrientationBits.acquire_valid _ _ out.padding).mpr hshape
  have hs := SemiprimeD1OrientationBits.acquire_slots_length _ _ out.padding hshape
  constructor
  · rw [hh.2.2,hr.2.2.2.2,hv]
    rfl
  · rw [hh.2.1,hs,hr.1]

/-- The real-port dictionary uses original occurrence number plus one. -/
theorem occurrence_ids (n F r a : ℕ) (arity : Fin F→ℕ)
    (owner : ((e : Fin F)×Fin (arity e))→Fin n) :
    ((acquire n F r a arity owner).placements.map (fun out => bitValue out.edge))=
      List.range' 1 (SemiprimeD1CollisionOriginal.ports n F a arity).length := by
  have h := replay_edges
    (SemiprimeD1PacketPadding.acquire n F r a arity owner).source.selection.cache.rows.source.dictionary a
    (SemiprimeD1PacketPadding.acquire n F r a arity owner).source.keys
    (initial (SemiprimeD1PacketPadding.acquire n F r a arity owner).clock)
  change _=List.range' (bitValue []+1) _ at h
  rw [SemiprimeD1PacketPadding.acquire_source] at h
  have hlen := congrArg List.length (SemiprimeD1IncidenceAcquisition.keys_original n F r a arity owner)
  simp only [List.length_map] at hlen
  rw [hlen] at h
  exact h

/-- Executed slot lookup returns each real original occurrence ID. -/
theorem lookup_real (n F r a : ℕ) [NeZero r] (arity : Fin F→ℕ)
    (owner : ((e : Fin F)×Fin (arity e))→Fin n) (out : Placement)
    (ho : out∈(acquire n F r a arity owner).placements) :
    (lookupSlot (acquire n F r a arity owner).state out.packet out.slot).bits=out.edge := by
  rw [lookupSlot_bits]
  exact slot_lookup n F r a arity owner out ho

/-- Unoccupied slots return literal zero, without adding artificial real ports. -/
theorem lookup_unused (n F r a : ℕ) (arity : Fin F→ℕ)
    (owner : ((e : Fin F)×Fin (arity e))→Fin n) (packet slot : List Bool)
    (hu : SemiprimeSourceHistogramKeyBits.frame packet slot∉
      ((acquire n F r a arity owner).placements.map slotAddress)) :
    (lookupSlot (acquire n F r a arity owner).state packet slot).bits=[] := by
  rw [lookupSlot_bits]
  exact (replay_preserves _ _ _ _ _ hu).trans (stored_empty _)

end RiemannGaussian.SemiprimeD1PacketReplayOriginal
