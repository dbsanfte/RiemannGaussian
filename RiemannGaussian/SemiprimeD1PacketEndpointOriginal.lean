/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1PacketTensorTables

/-! # Real replay witnesses for every actual packet-table endpoint
The witnesses are extracted from the concrete bucket/scan/one construction.
No endpoint provenance, local degree, or slot-shape certificate is supplied.
-/
set_option autoImplicit false
set_option maxHeartbeats 2800000
namespace RiemannGaussian.SemiprimeD1PacketEndpointOriginal
open SemiprimeD1ChildGraph SemiprimeD1ChildGraphSemantics SemiprimeD1PacketInventory

/-- Every member of one physical endpoint test has its actual successful-side witness. -/
theorem one_origin {n F : ℕ} {arity : Fin F→ℕ}
    (owner : ((e : Fin F)×Fin (arity e))→Fin n)
    (dict : SemiprimeSourceHistogramRows.Dictionary) (a q : ℕ) (target : List Bool)
    (port : (e : Fin F)×Fin (arity e)) (out : Placement) (endpoint : Endpoint (n+F))
    (he : endpoint∈(one owner dict a q target port out).value) :
    (endpoint=(endpoints owner port out).1 ∧
      (testColour target q (SemiprimeD1PacketRows.read dict a out.source).left).value=true) ∨
    (endpoint=(endpoints owner port out).2 ∧
      (testColour target q (SemiprimeD1PacketRows.read dict a out.source).right).value=true) := by
  change endpoint∈(if (testColour target q (SemiprimeD1PacketRows.read dict a out.source).left).value then
      [(endpoints owner port out).1] else [])++
    (if (testColour target q (SemiprimeD1PacketRows.read dict a out.source).right).value then
      [(endpoints owner port out).2] else []) at he
  rcases List.mem_append.mp he with he|he
  · by_cases h : (testColour target q (SemiprimeD1PacketRows.read dict a out.source).left).value=true
    · exact Or.inl ⟨by simpa only [h,ite_true,List.mem_singleton] using he,h⟩
    · simp [h] at he
  · by_cases h : (testColour target q (SemiprimeD1PacketRows.read dict a out.source).right).value=true
    · exact Or.inr ⟨by simpa only [h,ite_true,List.mem_singleton] using he,h⟩
    · simp [h] at he

/-- Literal bucket membership supplies both the real scan member and actual packet key. -/
theorem bucket_member {n F r a : ℕ} {arity : Fin F→ℕ}
    (owner : ((e : Fin F)×Fin (arity e))→Fin n)
    (source : SemiprimeD1PacketReplayOriginal.Acquired n F a arity)
    (packet : Fin source.state.packets.length) (i : Fin a) (g : Fin r) (endpoint : Endpoint (n+F))
    (he : endpoint∈((fromReplay owner source i g).factors[packet.val]?).getD []) :
    endpoint∈(fromReplay owner source i g).endpoints ∧ endpoint.packet=source.state.packets[packet.val] := by
  change endpoint∈((buckets _ source.state.packets).value[packet.val]?).getD [] at he
  rw [buckets_value,List.getElem?_map,List.getElem?_eq_getElem packet.isLt] at he
  simp only [Option.map_some,Option.getD_some] at he
  exact ⟨(List.mem_filter.mp he).1,of_decide_eq_true (List.mem_filter.mp he).2⟩

/-- Every actual packet endpoint comes from an actual original placement, preserving
its exact side and the actual successful physical group test. -/
theorem endpoint_origin {n F r a : ℕ} {arity : Fin F→ℕ}
    (owner : ((e : Fin F)×Fin (arity e))→Fin n)
    (source : SemiprimeD1PacketReplayOriginal.Acquired n F a arity)
    (packet : Fin source.state.packets.length) (i : Fin a) (g : Fin r) (endpoint : Endpoint (n+F))
    (he : endpoint∈((fromReplay owner source i g).factors[packet.val]?).getD []) :
    ∃ port : (e : Fin F)×Fin (arity e),∃ out∈source.placements,
      out.packet=source.state.packets[packet.val] ∧
      ((endpoint=(endpoints owner port out).1 ∧
        (testColour (SemiprimeSourceHistogramPortKeys.encodeKey g.val).bits i.val
          (SemiprimeD1PacketRows.read source.padding.source.selection.cache.rows.source.dictionary a out.source).left).value=true) ∨
       (endpoint=(endpoints owner port out).2 ∧
        (testColour (SemiprimeSourceHistogramPortKeys.encodeKey g.val).bits i.val
          (SemiprimeD1PacketRows.read source.padding.source.selection.cache.rows.source.dictionary a out.source).right).value=true)) := by
  obtain ⟨hm,hpacket⟩ := bucket_member owner source packet i g endpoint he
  change endpoint∈(scan owner source.padding.source.selection.cache.rows.source.dictionary a i.val
    (SemiprimeSourceHistogramPortKeys.encodeKey g.val).bits
    (source.padding.source.selection.cache.data.metadata.incidences.zip source.placements)).value at hm
  rw [scan_value] at hm
  obtain ⟨pair,hpair,hmem⟩ := List.mem_flatMap.mp hm
  have horigin := one_origin owner _ a i.val _ pair.1 pair.2 endpoint hmem
  refine ⟨pair.1,pair.2,(List.of_mem_zip hpair).2,?_,horigin⟩
  rcases horigin with ⟨heq,_⟩|⟨heq,_⟩ <;> simpa only [heq,endpoints] using hpacket

/-- Every original endpoint slot has its derived exact length, hence no runtime clipping. -/
theorem original_slot_length (n F r a : ℕ) [NeZero r] (arity : Fin F→ℕ)
    (owner : ((e : Fin F)×Fin (arity e))→Fin n)
    (packet : Fin (SemiprimeD1PacketReplayOriginal.acquire n F r a arity owner).state.packets.length)
    (i : Fin a) (g : Fin r) (endpoint : Endpoint (n+F))
    (he : endpoint∈((acquire n F r a arity owner i g).factors[packet.val]?).getD []) : endpoint.slot.length=a := by
  obtain ⟨port,out,ho,_,horigin⟩ := endpoint_origin owner _ packet i g endpoint he
  have hs := (SemiprimeD1PacketReplayOriginal.placement_valid n F r a arity owner out ho).2
  rcases horigin with ⟨heq,_⟩|⟨heq,_⟩ <;> simpa only [heq,endpoints] using hs

end RiemannGaussian.SemiprimeD1PacketEndpointOriginal
