/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1ChildMetadataPrimitives
import RiemannGaussian.SemiprimeD1OriginalModeAcquisition

/-! # Original-source child graph metadata supplier
All widths and stream sizes are derived from the actual original selector,
dictionary and replay. The bound retains its acquisition report. Native typed
owner/index evaluation is a separate finite metadata stage, not a free bit oracle.
-/
set_option autoImplicit false
set_option maxHeartbeats 1600000
namespace RiemannGaussian.SemiprimeD1OriginalChildGraphBudget
open scoped BigOperators
open SemiprimeD1ChildGraph SemiprimeD1ChildMetadataPrimitives
open SemiprimeD1PacketInventory SemiprimeSourceHistogramTrie

/-- Literal original retained replay source. -/
abbrev source (n F r a : ℕ) (arity : Fin F→ℕ)
    (owner : ((e : Fin F)×Fin (arity e))→Fin n) :=
  SemiprimeD1PacketReplayOriginal.acquire n F r a arity owner

/-- Original selected-pair byte width from the already executed compact producer. -/
def keyCap (n F r a : ℕ) : ℕ :=
  3*SemiprimeSourceHistogramFeatureBitsBounds.width (n+F) (r^a)+1

/-- Original dictionary payload width, independent of the queried ID. -/
def rowCap (r a : ℕ) : ℕ := a*(2*(r+1)+1)

/-- Closed original replay report envelope used as a conservative byte cap. -/
def replayCap (n F r a M : ℕ) : ℕ := SemiprimeD1PacketReplayBudget.budget n F r a M

/-- Every original pair/placement occurs once in this literal metadata stream. -/
theorem pairs_length (n F r a : ℕ) (arity : Fin F→ℕ)
    (owner : ((e : Fin F)×Fin (arity e))→Fin n) :
    ((source n F r a arity owner).padding.source.selection.cache.data.metadata.incidences.zip
      (source n F r a arity owner).placements).length=∑e,arity e := by
  have hm : (SemiprimeD1CollisionOriginal.ports n F a arity).length=∑e,arity e :=
    (SemiprimeSourceHistogramMetadata.sizes n F a arity).2.2.1
  have hp:=(SemiprimeD1OriginalModeAcquisition.original_size n F r a arity owner).trans hm
  rw [SemiprimeD1ChildGraphSemantics.original_ports,List.length_zip,hp,hm,Nat.min_self]

/-- Each original placed pair key has its actually acquired finite width. -/
theorem placement_source (n F r a : ℕ) [NeZero r] (arity : Fin F→ℕ)
    (owner : ((e : Fin F)×Fin (arity e))→Fin n) :
    ∀p∈(source n F r a arity owner).placements,p.source.length ≤ keyCap n F r a := by
  intro p hp
  have hmem : p.source∈((source n F r a arity owner).placements.map Placement.source):=List.mem_map.mpr ⟨p,hp,rfl⟩
  rw [SemiprimeD1PacketReplayOriginal.sources] at hmem
  exact SemiprimeD1IncidenceAcquisitionBounds.key_length n F r a arity owner p.source hmem

/-- Literal original dictionary, not a row-answer callback. -/
theorem dictionary (n F r a : ℕ) (arity : Fin F→ℕ)
    (owner : ((e : Fin F)×Fin (arity e))→Fin n) :
    (source n F r a arity owner).padding.source.selection.cache.rows.source.dictionary=
      SemiprimeSourceHistogramRows.acquire r a := rfl

/-- Actual original dictionary payload widths apply to every total byte lookup. -/
theorem dictionary_width (n F r a : ℕ) (arity : Fin F→ℕ)
    (owner : ((e : Fin F)×Fin (arity e))→Fin n) (id : List Bool) :
    (stored (source n F r a arity owner).padding.source.selection.cache.rows.source.dictionary.trie id).length ≤ rowCap r a := by
  rw [dictionary]
  exact SemiprimeSourceHistogramRowsBounds.acquire_width r a id

/-- Entire original emitted endpoint payloads have report-derived byte caps. -/
theorem endpoint_payload (n F r a : ℕ) [NeZero r] (arity : Fin F→ℕ)
    (owner : ((e : Fin F)×Fin (arity e))→Fin n) (q : Fin a) (g : Fin r) :
    ∀e∈(fromReplay owner (source n F r a arity owner) q g).endpoints,
      e.packet.length ≤ replayCap n F r a (∑e,arity e) ∧
      e.edge.length ≤ replayCap n F r a (∑e,arity e) ∧ e.slot.length ≤ a := by
  let src:=source n F r a arity owner
  have hc:=SemiprimeD1PacketReplayBudget.acquire_work n F r a arity owner
  apply scan_payload
  intro x hx
  have hp:=SemiprimeD1ReplayMetadataBounds.original_placements n F r a arity owner x.2
    (List.of_mem_zip hx).2
  exact ⟨hp.1.trans hc,hp.2.1.trans hc,hp.2.2⟩

/-- Actual emitted endpoint count, without an advised group load. -/
theorem endpoints_length (n F r a : ℕ) (arity : Fin F→ℕ)
    (owner : ((e : Fin F)×Fin (arity e))→Fin n) (q : Fin a) (g : Fin r) :
    (fromReplay owner (source n F r a arity owner) q g).endpoints.length ≤ 2*∑e,arity e := by
  have h:=scan_length owner (source n F r a arity owner).padding.source.selection.cache.rows.source.dictionary
    a q.val (SemiprimeSourceHistogramPortKeys.encodeKey g.val).bits
    ((source n F r a arity owner).padding.source.selection.cache.data.metadata.incidences.zip
      (source n F r a arity owner).placements)
  rwa [pairs_length] at h

/-- All observed factors, including empty buckets, are retained and counted. -/
theorem factors_length (n F r a : ℕ) (arity : Fin F→ℕ)
    (owner : ((e : Fin F)×Fin (arity e))→Fin n) (q : Fin a) (g : Fin r) :
    (fromReplay owner (source n F r a arity owner) q g).factors.length ≤ ∑e,arity e := by
  rw [SemiprimeD1ChildGraphSemantics.factors_length]
  exact SemiprimeD1ReplayMetadataBounds.original_count n F r a arity owner

/-- Conservative cached-factor incidence count from actual bucket loops. -/
theorem factors_flatten_length (n F r a : ℕ) (arity : Fin F→ℕ)
    (owner : ((e : Fin F)×Fin (arity e))→Fin n) (q : Fin a) (g : Fin r) :
    (fromReplay owner (source n F r a arity owner) q g).factors.flatten.length ≤ 2*(∑e,arity e)^2 := by
  have h:=buckets_length (fromReplay owner (source n F r a arity owner) q g).endpoints
    (source n F r a arity owner).state.packets
  have hP:=SemiprimeD1ReplayMetadataBounds.original_count n F r a arity owner
  have hE:=endpoints_length n F r a arity owner q g
  change _ ≤ 2*(∑e,arity e)^2
  exact h.trans (by nlinarith)

/-- Explicit supplier overhead, a fixed polynomial in original dimensions and
retained replay envelope. No2^M or full palette orbit enumeration occurs. -/
def overhead (n F r a M : ℕ) : ℕ :=
  SemiprimeSourceHistogramPortKeys.encodeBudget r+
    M*(oneBudget a a (keyCap n F r a) (rowCap r a) (SemiprimeSourceHistogramPortKeys.keyWidth r)+8)+2+
    M*((2*M)*(6*replayCap n F r a M+9)+6)+2+2*M+12

/-- CLOSED actual fromReplay supplier report: source is retained once, and all
physical row, comparison, endpoint, bucket and constructor reports are paid. -/
theorem fromReplay_work (n F r a : ℕ) [NeZero r] (arity : Fin F→ℕ)
    (owner : ((e : Fin F)×Fin (arity e))→Fin n) (q : Fin a) (g : Fin r) :
    (fromReplay owner (source n F r a arity owner) q g).work ≤
      (source n F r a arity owner).state.clock+overhead n F r a (∑e,arity e) := by
  let src:=source n F r a arity owner
  let target:=SemiprimeSourceHistogramPortKeys.encodeKey g.val
  let xs:=src.padding.source.selection.cache.data.metadata.incidences.zip src.placements
  let emitted:=scan owner src.padding.source.selection.cache.rows.source.dictionary a q.val target.bits xs
  have ht:=SemiprimeSourceHistogramPortKeys.encodeKey_clock g.val r (by omega)
  change target.clock ≤ SemiprimeSourceHistogramPortKeys.encodeBudget r at ht
  have hG:=SemiprimeSourceHistogramPortKeys.encodeKey_length g.val r (by omega)
  have hx : xs.length=∑e,arity e:=pairs_length n F r a arity owner
  have hs:=scan_work owner src.padding.source.selection.cache.rows.source.dictionary a q.val target.bits xs
    (keyCap n F r a) (rowCap r a) (SemiprimeSourceHistogramPortKeys.keyWidth r)
    (fun x hx=>placement_source n F r a arity owner x.2 (List.of_mem_zip hx).2) hG
    (dictionary_width n F r a arity owner)
  rw [hx] at hs
  have he:=endpoints_length n F r a arity owner q g
  change emitted.value.length ≤ 2*∑e,arity e at he
  have hp:=SemiprimeD1ReplayMetadataBounds.original_count n F r a arity owner
  change src.state.packets.length ≤ ∑e,arity e at hp
  have hb:=buckets_work emitted.value src.state.packets (replayCap n F r a (∑e,arity e))
    (fun e he=>(endpoint_payload n F r a arity owner q g e he).1)
  have hread : emitted.work ≤ (∑e,arity e)*(oneBudget a a (keyCap n F r a) (rowCap r a)
      (SemiprimeSourceHistogramPortKeys.keyWidth r)+8)+2 := hs.trans (by unfold oneBudget colourBudget;gcongr;exact Nat.le_of_lt q.isLt)
  have hbucket : (buckets emitted.value src.state.packets).work ≤
      (∑e,arity e)*((2*∑e,arity e)*(6*replayCap n F r a (∑e,arity e)+9)+6)+2 := hb.trans (by gcongr)
  have hmeta : src.padding.source.selection.cache.data.metadata.incidences.length+src.placements.length=2*∑e,arity e := by
    rw [SemiprimeD1ChildGraphSemantics.original_ports,SemiprimeD1OriginalModeAcquisition.original_size]
    have hm : (SemiprimeD1CollisionOriginal.ports n F a arity).length=∑e,arity e:=
      (SemiprimeSourceHistogramMetadata.sizes n F a arity).2.2.1
    rw [hm]
    omega
  change src.state.clock+target.clock+emitted.work+(buckets emitted.value src.state.packets).work+
    src.padding.source.selection.cache.data.metadata.incidences.length+src.placements.length+12 ≤
      src.state.clock+overhead n F r a (∑e,arity e)
  unfold overhead
  omega

end RiemannGaussian.SemiprimeD1OriginalChildGraphBudget
