/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1ModeRoutingBudget
import RiemannGaussian.SemiprimeD1OriginalChildGraphBudget
import RiemannGaussian.SemiprimeD1PacketTensorTables

/-! # Original packet classifiers and complete header acquisition report
The actual global catalogue is constructed and charged. All byte caps and
original wrappers are producer-derived; no routes, mode lists or Fits are advice.
-/
set_option autoImplicit false
set_option maxHeartbeats 1800000
namespace RiemannGaussian.SemiprimeD1PacketModeMaskBudget
open scoped BigOperators
open SemiprimeD1PacketModeMask SemiprimeD1ModeCatalog
open SemiprimeD1OriginalChildGraphBudget

/-- Actual per-mode physical routing/classification and native field ledger. -/
def itemBudget (a W M T : ℕ) : ℕ :=
  SemiprimeD1ModeRoutingBudget.budget a W T+20*(W+1)+M+M*T+T+20

/-- Exact actual tile value is bounded even for an unrelated-packet descriptor. -/
theorem one_tile {n F a : ℕ} {arity : Fin F→ℕ}
    (src : SemiprimeD1PacketReplayOriginal.Acquired n F a arity)
    (packet : Fin src.state.packets.length) (i : Fin a) (group : List Bool) (mode : Mode) :
    (acquireOne src packet i group mode).tile ≤ 2^a := by
  have ht : mode.slot%2^(i.val+1)<2^(i.val+1):=Nat.mod_lt _ (by positivity)
  have hp:=Nat.pow_le_pow_right (by decide : 0<(2:ℕ)) (show i.val+1 ≤ a by omega)
  unfold acquireOne
  dsimp only
  split_ifs <;> dsimp only <;> omega

/-- Actual byte routing/classification report, including unrelated-packet skip. -/
theorem one_clock {n F a : ℕ} {arity : Fin F→ℕ}
    (src : SemiprimeD1PacketReplayOriginal.Acquired n F a arity)
    (packet : Fin src.state.packets.length) (i : Fin a) (group : List Bool) (mode : Mode)
    (M W : ℕ) (hp : src.state.packets.length ≤ M)
    (hk : ∀key∈src.state.packets,key.length ≤ W) (hm : mode.slot ≤ M*2^a) :
    (acquireOne src packet i group mode).clock ≤ itemBudget a W M (2^a) := by
  have hkey:=hk _ (List.getElem_mem packet.isLt)
  have htiles : 2^(i.val+1) ≤ (2:ℕ)^a:=
    Nat.pow_le_pow_right (by decide) (by omega)
  have hpacket : packet.val ≤ M:=by have h:=packet.isLt;omega
  let tile : Fin (2^(i.val+1)):=⟨mode.slot%2^(i.val+1),Nat.mod_lt _ (by positivity)⟩
  let key:=SemiprimeSourceCompactBits.copy src.state.packets[packet.val]
  let route:=SemiprimeD1ModeRoutingBits.acquire key.bits a i tile
  have hkb : key.bits.length ≤ W:=by simpa only [key,SemiprimeSourceCompactBits.copy_bits] using hkey
  have hroute:=SemiprimeD1ModeRoutingBudget.acquire_clock key.bits a i tile W hkb
  have hlen:=SemiprimeD1ModeRoutingBudget.route_lengths key.bits a i tile
  have ht:=SemiprimeD1ChildGraph.equalBytes_work route.target group
  have hs:=SemiprimeD1ChildGraph.equalBytes_work route.source group
  have hleft : route.source.length ≤ W:=hlen.1.trans hkb
  have hright : route.target.length ≤ W:=hlen.2.trans hkb
  change route.clock ≤ _ at hroute
  unfold acquireOne
  dsimp only
  split_ifs
  · change key.clock+route.clock+(SemiprimeD1ChildGraph.equalBytes route.target group).work+
      (SemiprimeD1ChildGraph.equalBytes route.source group).work+packet.val+mode.slot+2^(i.val+1)+9 ≤ _
    have hc : key.clock ≤ 3*W+1:=by rw [SemiprimeSourceCompactBits.copy_clock];omega
    unfold itemBudget
    omega
  · change mode.slot+2^(i.val+1)+5 ≤ _
    unfold itemBudget
    omega

/-- Literal same-order classifier loop pays every acquired descriptor. -/
theorem scan_clock {n F a : ℕ} {arity : Fin F→ℕ}
    (src : SemiprimeD1PacketReplayOriginal.Acquired n F a arity)
    (packet : Fin src.state.packets.length) (i : Fin a) (group : List Bool)
    (modes : List Mode) (M W : ℕ) (hp : src.state.packets.length ≤ M)
    (hk : ∀key∈src.state.packets,key.length ≤ W) (hm : ∀mode∈modes,mode.slot ≤ M*2^a) :
    (scan src packet i group modes).clock ≤ modes.length*(itemBudget a W M (2^a)+4)+1 := by
  induction modes with
  | nil => simp [scan]
  | cons mode modes ih =>
    have hh:=one_clock src packet i group mode M W hp hk (hm mode List.mem_cons_self)
    have ht:=ih (fun x hx=>hm x (List.mem_cons_of_mem mode hx))
    simp only [scan,List.length_cons]
    nlinarith

/-- Original classifier/header overhead remains polynomial in replay bytes,
working precision, real port count and actual dyadic tile range. -/
def overhead (r a M P W : ℕ) : ℕ :=
  SemiprimeSourceHistogramPortKeys.encodeBudget r+
    (10*P+10+P*(10*(M*2^a)+10))+
    (P*M*2^a)*(itemBudget a W M (2^a)+4)+9

/-- Actual complete acquired mode cache, keeping source.work LINEAR and explicit. -/
theorem fromModes_clock {n F r a : ℕ} {arity : Fin F→ℕ}
    (src : SemiprimeD1OriginalModeAcquisition.Acquired n F a arity)
    (packet : Fin src.packets.state.packets.length) (i : Fin a) (g : Fin r) (M W : ℕ)
    (hp : src.packets.state.packets.length ≤ M)
    (hk : ∀key∈src.packets.state.packets,key.length ≤ W) :
    (fromModes src packet i g).clock ≤ src.work+overhead r a M src.precision W := by
  let group:=SemiprimeSourceHistogramPortKeys.encodeKey g.val
  let slots:=src.packets.state.packets.length*2^(i.val+1)
  let catalogue:=acquireCatalog slots (src.precision-1)
  have htile : 2^(i.val+1) ≤ (2:ℕ)^a:=Nat.pow_le_pow_right (by decide) (by omega)
  have hslots : slots ≤ M*2^a:=Nat.mul_le_mul hp htile
  have hc : catalogue.value.length ≤ src.precision*M*2^a := by
    rw [show catalogue.value=catalog slots (src.precision-1) from acquireCatalog_value _ _,catalog_length]
    have h:=Nat.mul_le_mul (Nat.sub_le src.precision 1) hslots
    nlinarith
  have hwork : catalogue.work ≤ 10*src.precision+10+src.precision*(10*(M*2^a)+10) := by
    rw [show catalogue.work=10*(src.precision-1)+10+(src.precision-1)*(10*slots+10) from acquireCatalog_work _ _]
    gcongr <;> exact Nat.sub_le _ _
  have hm : ∀mode∈catalogue.value,mode.slot ≤ M*2^a := by
    intro mode hm
    rw [show catalogue.value=catalog slots (src.precision-1) from acquireCatalog_value _ _] at hm
    exact (Nat.le_of_lt ((mem_catalog _ _ _).mp hm).1).trans hslots
  have hs:=scan_clock src.packets packet i group.bits catalogue.value M W hp hk hm
  have hg:=SemiprimeSourceHistogramPortKeys.encodeKey_clock g.val r (by omega)
  have hs' : (scan src.packets packet i group.bits catalogue.value).clock ≤
      (src.precision*M*2^a)*(itemBudget a W M (2^a)+4)+1:=hs.trans (by gcongr)
  change src.work+group.clock+catalogue.work+(scan src.packets packet i group.bits catalogue.value).clock+8 ≤ _
  change group.clock ≤ _ at hg
  change _ ≤ src.work+(SemiprimeSourceHistogramPortKeys.encodeBudget r+
    (10*src.precision+10+src.precision*(10*(M*2^a)+10))+
    (src.precision*M*2^a)*(itemBudget a W M (2^a)+4)+9)
  omega

/-- Every ACTUAL acquired mask item has constructor-derived order and tile caps. -/
theorem item_caps {n F r a : ℕ} {arity : Fin F→ℕ}
    (src : SemiprimeD1OriginalModeAcquisition.Acquired n F a arity)
    (packet : Fin src.packets.state.packets.length) (i : Fin a) (g : Fin r)
    (item : Item) (hi : item∈(fromModes src packet i g).items) :
    item.mode.order ≤ src.precision ∧ item.tile ≤ 2^a := by
  have hmode : item.mode∈((fromModes src packet i g).items.map Item.mode):=List.mem_map.mpr ⟨item,hi,rfl⟩
  rw [fromModes_catalogue] at hmode
  have hc:=((mem_catalog _ _ _).mp hmode).2
  have horder : item.mode.order ≤ src.precision:=by omega
  have hitems : (fromModes src packet i g).items=
      ((acquireCatalog (src.packets.state.packets.length*2^(i.val+1)) (src.precision-1)).value.map
        (acquireOne src.packets packet i (SemiprimeSourceHistogramPortKeys.encodeKey g.val).bits)) := by
    exact scan_items _ _ _ _ _
  rw [hitems] at hi
  obtain ⟨mode,_,rfl⟩:=List.mem_map.mp hi
  exact ⟨horder,one_tile _ _ _ _ _⟩

/-- Literal original mode source retained by the controller. -/
abbrev originalSource (n F r a u phase p : ℕ) (arity : Fin F→ℕ)
    (owner : ((e : Fin F)×Fin (arity e))→Fin n) :=
  SemiprimeD1OriginalModeAcquisition.acquire n F r a u phase p arity owner

/-- CLOSED actual original-source mode classifier budget. -/
theorem original_clock (n F r a u phase p : ℕ) [NeZero r] (arity : Fin F→ℕ)
    (owner : ((e : Fin F)×Fin (arity e))→Fin n)
    (packet : Fin (originalSource n F r a u phase p arity owner).packets.state.packets.length)
    (i : Fin a) (g : Fin r) :
    (fromModes (originalSource n F r a u phase p arity owner) packet i g).clock ≤
      (originalSource n F r a u phase p arity owner).work+
        overhead r a (∑e,arity e) (originalSource n F r a u phase p arity owner).precision
          (replayCap n F r a (∑e,arity e)) := by
  apply fromModes_clock _ _ _ _ _ _ (SemiprimeD1ReplayMetadataBounds.original_count n F r a arity owner)
  intro key hk
  exact ((SemiprimeD1ReplayMetadataBounds.original_packets n F r a arity owner).2 key hk).trans
    (SemiprimeD1PacketReplayBudget.acquire_work n F r a arity owner)

/-- A cached bucket read contains only endpoints of the actually emitted list. -/
theorem buckets_get_subset {V : ℕ} (es : List (SemiprimeD1ChildGraph.Endpoint V))
    (packets : List (List Bool)) (j : ℕ) (e : SemiprimeD1ChildGraph.Endpoint V)
    (he : e∈(((SemiprimeD1ChildGraph.buckets es packets).value[j]?).getD [])) : e∈es := by
  induction packets generalizing j with
  | nil => simp [SemiprimeD1ChildGraph.buckets] at he
  | cons packet packets ih =>
    cases j with
    | zero =>
      change e∈(SemiprimeD1ChildGraph.bucket packet es).value at he
      rw [SemiprimeD1ChildGraphSemantics.bucket_value] at he
      exact (List.mem_filter.mp he).1
    | succ j => exact ih j he

/-- A total cached bucket read never exceeds the actual emitted endpoint count. -/
theorem buckets_get_length {V : ℕ} (es : List (SemiprimeD1ChildGraph.Endpoint V))
    (packets : List (List Bool)) (j : ℕ) :
    (((SemiprimeD1ChildGraph.buckets es packets).value[j]?).getD []).length ≤ es.length := by
  induction packets generalizing j with
  | nil => simp [SemiprimeD1ChildGraph.buckets]
  | cons packet packets ih =>
    cases j with
    | zero => exact SemiprimeD1ChildMetadataPrimitives.bucket_length packet es
    | succ j => exact ih j

/-- Full original packet header supplier overhead. -/
def prepareOverhead (n F r a M P : ℕ) : ℕ :=
  overhead r a M P (replayCap n F r a M)+
    SemiprimeD1OriginalChildGraphBudget.overhead n F r a M+3*M+10

/-- Actual header endpoints inherit physical original packet/slot/edge bytes. -/
theorem prepare_payload (n F r a u phase p : ℕ) [NeZero r] (arity : Fin F→ℕ)
    (owner : ((e : Fin F)×Fin (arity e))→Fin n)
    (packet : Fin (originalSource n F r a u phase p arity owner).packets.state.packets.length)
    (i : Fin a) (g : Fin r) :
    ∀e∈(SemiprimeD1PacketTensorTables.prepare owner (originalSource n F r a u phase p arity owner) packet i g).endpoints,
      e.packet.length ≤ replayCap n F r a (∑e,arity e) ∧
      e.edge.length ≤ replayCap n F r a (∑e,arity e) ∧ e.slot.length ≤ a := by
  intro e he
  let src:=originalSource n F r a u phase p arity owner
  let graph:=SemiprimeD1ChildGraph.fromReplay owner src.packets i g
  have hm : e∈graph.endpoints := buckets_get_subset graph.endpoints src.packets.state.packets packet.val e he
  exact endpoint_payload n F r a arity owner i g e hm

/-- Actual cached packet table degree uses the proved orientation-slot injection,
not the coarse polynomial metadata endpoint-count estimate. -/
theorem prepare_degree (n F r a u phase p : ℕ) [NeZero r] (arity : Fin F→ℕ)
    (owner : ((e : Fin F)×Fin (arity e))→Fin n)
    (packet : Fin (originalSource n F r a u phase p arity owner).packets.state.packets.length)
    (i : Fin a) (g : Fin r) :
    (SemiprimeD1PacketTensorTables.prepare owner (originalSource n F r a u phase p arity owner) packet i g).endpoints.length ≤ 2*2^a := by
  let G:=SemiprimeD1ChildGraph.acquire n F r a arity owner i g
  have hp : packet.val < G.factors.length := by
    change packet.val < (SemiprimeD1ChildGraph.fromReplay owner
      (SemiprimeD1PacketReplayOriginal.acquire n F r a arity owner) i g).factors.length
    rw [SemiprimeD1ChildGraphSemantics.factors_length]
    exact packet.isLt
  change ((G.factors[packet.val]?).getD []).length ≤ _
  rw [List.getElem?_eq_getElem hp,Option.getD_some]
  exact SemiprimeD1ChildGraphBounds.packet_arity n F r a arity owner i g ⟨packet.val,hp⟩

/-- All original cached header mode descriptors have computed order/tile caps. -/
theorem prepare_item_caps (n F r a u phase p : ℕ) (arity : Fin F→ℕ)
    (owner : ((e : Fin F)×Fin (arity e))→Fin n)
    (packet : Fin (originalSource n F r a u phase p arity owner).packets.state.packets.length)
    (i : Fin a) (g : Fin r) (item : Item)
    (hi : item∈(SemiprimeD1PacketTensorTables.prepare owner
      (originalSource n F r a u phase p arity owner) packet i g).masks.items) :
    item.mode.order ≤ (originalSource n F r a u phase p arity owner).precision ∧ item.tile ≤ 2^a :=
  item_caps _ _ _ _ item hi

/-- CLOSED original complete-header report. The source acquisition/menu report
is retained LINEARLY and all repeated classifiers/graph scans remain paid. -/
theorem prepare_clock (n F r a u phase p : ℕ) [NeZero r] (arity : Fin F→ℕ)
    (owner : ((e : Fin F)×Fin (arity e))→Fin n)
    (packet : Fin (originalSource n F r a u phase p arity owner).packets.state.packets.length)
    (i : Fin a) (g : Fin r) :
    (SemiprimeD1PacketTensorTables.prepare owner (originalSource n F r a u phase p arity owner) packet i g).clock ≤
      (originalSource n F r a u phase p arity owner).work+
        prepareOverhead n F r a (∑e,arity e) (originalSource n F r a u phase p arity owner).precision := by
  let src:=originalSource n F r a u phase p arity owner
  let graph:=SemiprimeD1ChildGraph.fromReplay owner src.packets i g
  let masks:=fromModes src packet i g
  let W:=replayCap n F r a (∑e,arity e)
  have hm:=original_clock n F r a u phase p arity owner packet i g
  change masks.clock ≤ src.work+overhead r a (∑e,arity e) src.precision W at hm
  have hg:=SemiprimeD1OriginalChildGraphBudget.fromReplay_work n F r a arity owner i g
  change graph.work ≤ src.packets.state.clock+_ at hg
  have hd : graph.work-src.packets.state.clock ≤ SemiprimeD1OriginalChildGraphBudget.overhead n F r a (∑e,arity e) := by omega
  have hp:=SemiprimeD1ReplayMetadataBounds.original_count n F r a arity owner
  change src.packets.state.packets.length ≤ ∑e,arity e at hp
  have hpacket : packet.val ≤ ∑e,arity e := by
    have h:=packet.isLt
    change packet.val < src.packets.state.packets.length at h
    omega
  have he:=buckets_get_length graph.endpoints src.packets.state.packets packet.val
  have hE:=endpoints_length n F r a arity owner i g
  change graph.endpoints.length ≤ _ at hE
  have hlen : ((graph.factors[packet.val]?).getD []).length ≤ 2*∑e,arity e := he.trans hE
  change masks.clock+(graph.work-src.packets.state.clock)+packet.val+
    ((graph.factors[packet.val]?).getD []).length+10 ≤ src.work+
    (overhead r a (∑e,arity e) src.precision W+
      SemiprimeD1OriginalChildGraphBudget.overhead n F r a (∑e,arity e)+3*(∑e,arity e)+10)
  omega

end RiemannGaussian.SemiprimeD1PacketModeMaskBudget
