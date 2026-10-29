/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1PacketEndpointOriginal
import RiemannGaussian.SemiprimeD1PacketModeProjection

/-! # Original real-row crossing discharges the executed mode bit test
The successful physical child-group test and actual route source inequality
supply the hypothesis of the original replay routing theorem. No selected-word
getter, endpoint origin witness, or same-bit answer is a caller premise.
-/
set_option autoImplicit false
set_option maxHeartbeats 3200000
namespace RiemannGaussian.SemiprimeD1PacketModeOriginal
open SemiprimeD1ChildGraph SemiprimeD1PacketEndpointOriginal SemiprimeBitArithmetic

/-- A real row in the acquired child packet has the tile bit whenever it crosses
away from that actual acquired source colour. -/
theorem row_samebit (n F r a : ℕ) [NeZero r] (arity : Fin F→ℕ)
    (owner : ((e : Fin F)×Fin (arity e))→Fin n)
    (packet : Fin (SemiprimeD1PacketReplayOriginal.acquire n F r a arity owner).state.packets.length)
    (i : Fin a) (g : Fin r) (tile : Fin (2^(i.val+1))) (endpoint : Endpoint (n+F))
    (he : endpoint∈((acquire n F r a arity owner i g).factors[packet.val]?).getD [])
    (hside : endpoint.side=true)
    (hsource : (SemiprimeD1ModeRoutingBits.acquire
      (SemiprimeD1PacketReplayOriginal.acquire n F r a arity owner).state.packets[packet.val] a i tile).source≠
        (SemiprimeSourceHistogramPortKeys.encodeKey g.val).bits) :
    (bitValue endpoint.slot).testBit i.val=tile.val.testBit i.val := by
  let source := SemiprimeD1PacketReplayOriginal.acquire n F r a arity owner
  obtain ⟨port,out,ho,hpacket,horigin⟩ := endpoint_origin owner source packet i g endpoint he
  rcases horigin with ⟨heq,hrow⟩|⟨heq,hcolumn⟩
  · have hnum := (testColour_correct (SemiprimeSourceHistogramPortKeys.encodeKey g.val).bits i.val
      (SemiprimeD1PacketRows.read source.padding.source.selection.cache.rows.source.dictionary a out.source).left).mp hrow
    have hs : (SemiprimeD1ModeRoutingBits.fromReplay source packet i tile).source≠
        (SemiprimeSourceHistogramPortKeys.encodeKey g.val).bits := by
      rw [(SemiprimeD1ModeRoutingBits.fromReplay_data source packet i tile).1]
      exact hsource
    have hcompact := (SemiprimeD1ModeRoutingOriginal.route_palette n F r a arity owner packet i tile).1
    have hx : (((SemiprimeD1ModeRoutingOriginal.actualRows source out).left[i.val]?).getD [])≠
        (SemiprimeD1ModeRoutingBits.fromReplay source packet i tile).source := by
      intro hcolour
      apply hs
      apply SemiprimeSourceCompactWordIds.compact_value_injective _ _ hcompact
        (SemiprimeSourceHistogramPortKeys.encodeKey_compact g.val)
      rw [←hcolour]
      exact hnum
    have hbit := SemiprimeD1ModeRoutingOriginal.crossing_testBit n F r a arity owner packet i tile out ho hpacket hx
    simpa only [heq,endpoints] using hbit
  · rw [heq] at hside
    simp only [endpoints,Bool.false_eq_true] at hside

/-- The physical coefficient bit test is true on each original crossing row. -/
theorem row_test_true (n F r a : ℕ) [NeZero r] (arity : Fin F→ℕ)
    (owner : ((e : Fin F)×Fin (arity e))→Fin n)
    (packet : Fin (SemiprimeD1PacketReplayOriginal.acquire n F r a arity owner).state.packets.length)
    (i : Fin a) (g : Fin r) (tile : Fin (2^(i.val+1))) (endpoint : Endpoint (n+F))
    (he : endpoint∈((acquire n F r a arity owner i g).factors[packet.val]?).getD [])
    (hside : endpoint.side=true)
    (hsource : (SemiprimeD1ModeRoutingBits.acquire
      (SemiprimeD1PacketReplayOriginal.acquire n F r a arity owner).state.packets[packet.val] a i tile).source≠
        (SemiprimeSourceHistogramPortKeys.encodeKey g.val).bits) (bit : Bool) :
    (SemiprimeD1PacketEntryBits.sameBit
      (SemiprimeD1PacketEntryInputs.wire a endpoint bit).1.slot.val tile.val i.val).value=true := by
  have hs := original_slot_length n F r a arity owner packet i g endpoint he
  rw [SemiprimeD1PacketEntryBits.sameBit_value,SemiprimeD1PacketEntryInputs.wire_slot a endpoint bit hs,
    row_samebit n F r a arity owner packet i g tile endpoint he hside hsource]
  exact beq_self_eq_true _

/-- Literal nonlocal branch flag of an actually acquired mode descriptor. -/
def nonlocalMask (item : SemiprimeD1PacketModeMask.Item) : Bool :=
  item.inPacket && item.targetHere && !item.sourceHere

/-- The actual acquired nonlocal mode mask discharges the coefficient's physical
bit test on every original row. Source inequality is derived, not supplied. -/
theorem acquired_row_test_true (n F r a : ℕ) [NeZero r] (arity : Fin F→ℕ)
    (owner : ((e : Fin F)×Fin (arity e))→Fin n)
    (packet : Fin (SemiprimeD1PacketReplayOriginal.acquire n F r a arity owner).state.packets.length)
    (i : Fin a) (g : Fin r) (mode : SemiprimeD1ModeCatalog.Mode) (endpoint : Endpoint (n+F))
    (he : endpoint∈((acquire n F r a arity owner i g).factors[packet.val]?).getD [])
    (hside : endpoint.side=true)
    (hmask : nonlocalMask (SemiprimeD1PacketModeMask.acquireOne
      (SemiprimeD1PacketReplayOriginal.acquire n F r a arity owner) packet i
      (SemiprimeSourceHistogramPortKeys.encodeKey g.val).bits mode)=true) (bit : Bool) :
    let item := SemiprimeD1PacketModeMask.acquireOne
      (SemiprimeD1PacketReplayOriginal.acquire n F r a arity owner) packet i
      (SemiprimeSourceHistogramPortKeys.encodeKey g.val).bits mode
    (SemiprimeD1PacketEntryBits.sameBit
      (SemiprimeD1PacketEntryInputs.wire a endpoint bit).1.slot.val (item.tile%2^a) i.val).value=true := by
  let source := SemiprimeD1PacketReplayOriginal.acquire n F r a arity owner
  let item := SemiprimeD1PacketModeMask.acquireOne source packet i
    (SemiprimeSourceHistogramPortKeys.encodeKey g.val).bits mode
  change (item.inPacket && item.targetHere && !item.sourceHere)=true at hmask
  change (SemiprimeD1PacketEntryBits.sameBit
    (SemiprimeD1PacketEntryInputs.wire a endpoint bit).1.slot.val (item.tile%2^a) i.val).value=true
  have hpacket : mode.slot/2^(i.val+1)=packet.val := by
    by_contra hn
    have hz := SemiprimeD1PacketModeMask.acquireOne_other source packet i
      (SemiprimeSourceHistogramPortKeys.encodeKey g.val).bits mode hn
    have hm := (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp hmask).1).1
    change (SemiprimeD1PacketModeMask.acquireOne source packet i _ mode).inPacket=true at hm
    rw [hz.1] at hm
    cases hm
  let tile : Fin (2^(i.val+1)) := ⟨mode.slot%2^(i.val+1),Nat.mod_lt _ (by positivity)⟩
  have hh := SemiprimeD1PacketModeMask.acquireOne_here source packet i
    (SemiprimeSourceHistogramPortKeys.encodeKey g.val).bits mode hpacket
  have hs : (SemiprimeD1ModeRoutingBits.acquire source.state.packets[packet.val] a i tile).source≠
      (SemiprimeSourceHistogramPortKeys.encodeKey g.val).bits := by
    intro heq
    have hflag := hh.2.2.mpr heq
    have hn := (Bool.and_eq_true_iff.mp hmask).2
    have hflag' : item.sourceHere=true := hflag
    rw [hflag'] at hn
    cases hn
  have ht := row_test_true n F r a arity owner packet i g tile endpoint he hside hs bit
  have htile : item.tile=tile.val := by
    dsimp only [item,SemiprimeD1PacketModeMask.acquireOne]
    simp only [hpacket,ite_true,tile]
  have hlt : tile.val<2^a := tile.isLt.trans_le
    (Nat.pow_le_pow_right (by omega : 0<2) (by omega : i.val+1≤a))
  simpa only [htile,Nat.mod_eq_of_lt hlt] using ht

end RiemannGaussian.SemiprimeD1PacketModeOriginal
