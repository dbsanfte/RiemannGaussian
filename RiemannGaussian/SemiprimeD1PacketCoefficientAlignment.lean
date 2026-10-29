/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1PacketAffineRowEvaluation

/-! # Actual real-row coefficients and original routing masks
For a mode in the actual packet, the executed coefficient is zero at its local
source group and is exactly the signed original D.12 mode otherwise. Original
routing proves the target and same-bit tests; neither is supplied as advice.
-/
set_option autoImplicit false
set_option maxHeartbeats 4000000
namespace RiemannGaussian.SemiprimeD1PacketCoefficientAlignment
open SemiprimeD1PacketEntryInputs SemiprimeD1PacketEntryBits
open SemiprimeD1PacketEntryComponents SemiprimeD1PacketRowExpansion SemiprimeD1PacketGlobalRowForm
open SemiprimeD1ChildGraph SemiprimeD1JetAxes SemiprimeD1JetInterpretation
noncomputable section
attribute [local instance] Classical.propDecidable

/-- The actual tile ordinal is its literal flattened-slot residue in both
classifier branches. -/
theorem acquireOne_tile {n F a : ℕ} {arity : Fin F→ℕ}
    (source : SemiprimeD1PacketReplayOriginal.Acquired n F a arity)
    (packet : Fin source.state.packets.length) (i : Fin a) (group : List Bool)
    (mode : SemiprimeD1ModeCatalog.Mode) :
    (SemiprimeD1PacketModeMask.acquireOne source packet i group mode).tile=mode.slot%2^(i.val+1) := by
  unfold SemiprimeD1PacketModeMask.acquireOne
  dsimp only
  split_ifs <;> rfl

/-- Actual original in-packet row coefficient, with both physical routing tests
closed from the real endpoint and original group relation. -/
theorem coefficient_in_packet (ctx : Context) (z : SemiprimeD1JetAffineCoefficient.JetRun)
    (n F r a : ℕ) [NeZero r] (arity : Fin F→ℕ)
    (owner : ((e : Fin F)×Fin (arity e))→Fin n)
    (packet : Fin (SemiprimeD1PacketReplayOriginal.acquire n F r a arity owner).state.packets.length)
    (i : Fin a) (g : Fin r) (endpoint : Endpoint (n+F))
    (he : endpoint∈((acquire n F r a arity owner i g).factors[packet.val]?).getD [])
    (hside : endpoint.side=true) (bit : Bool) (mode : SemiprimeD1ModeCatalog.Mode)
    (hpacket : mode.slot/2^(i.val+1)=packet.val)
    (t : Fin (SemiprimeD1WireKernelOriginal.size a)) (hpos : ctx.Positive) (hp : 0<ctx.precision)
    (ht : SemiprimeD1WireKernelOriginal.point a t.val≠0)
    (hi : padicValInt 2 (SemiprimeD1WireKernelOriginal.point a t.val)=i.val) :
    let source := SemiprimeD1PacketReplayOriginal.acquire n F r a arity owner
    let tile : Fin (2^(i.val+1)) := ⟨mode.slot%2^(i.val+1),Nat.mod_lt _ (by positivity)⟩
    let item := SemiprimeD1PacketModeMask.acquireOne source packet i
      (SemiprimeSourceHistogramPortKeys.encodeKey g.val).bits mode
    let row := (wire a endpoint bit).1
    interpret ctx (coefficient ctx z a i t row item).words=
      if (SemiprimeD1ModeRoutingBits.acquire source.state.packets[packet.val] a i tile).source=
          (SemiprimeSourceHistogramPortKeys.encodeKey g.val).bits then 0
      else if bit then modeValue ctx z a i t row tile mode.order else -modeValue ctx z a i t row tile mode.order := by
  let source := SemiprimeD1PacketReplayOriginal.acquire n F r a arity owner
  let tile : Fin (2^(i.val+1)) := ⟨mode.slot%2^(i.val+1),Nat.mod_lt _ (by positivity)⟩
  let item := SemiprimeD1PacketModeMask.acquireOne source packet i
    (SemiprimeSourceHistogramPortKeys.encodeKey g.val).bits mode
  let row := (wire a endpoint bit).1
  have hh := SemiprimeD1PacketModeMask.acquireOne_here source packet i
    (SemiprimeSourceHistogramPortKeys.encodeKey g.val).bits mode hpacket
  have hc := coefficient_value ctx z a i t row item hpos hp ht hi
  dsimp only at hc
  change interpret ctx (coefficient ctx z a i t row item).words=
    if (SemiprimeD1ModeRoutingBits.acquire source.state.packets[packet.val] a i tile).source=
      (SemiprimeSourceHistogramPortKeys.encodeKey g.val).bits then 0
    else if bit then modeValue ctx z a i t row tile mode.order else -modeValue ctx z a i t row tile mode.order
  have hip : item.inPacket=true := hh.1
  by_cases hs : (SemiprimeD1ModeRoutingBits.acquire source.state.packets[packet.val] a i tile).source=
      (SemiprimeSourceHistogramPortKeys.encodeKey g.val).bits
  · have hf : item.sourceHere=true := hh.2.2.mpr hs
    rw [hc]
    simp only [hf,Bool.not_true,Bool.and_false,Bool.false_and,Bool.false_eq_true,ite_false,hs,ite_true]
  · have htarget := original_row_target n F r a arity owner packet i g tile endpoint he hside hs
    have htf : item.targetHere=true := hh.2.1.mpr htarget
    have hsf : item.sourceHere=false := by
      cases hx : item.sourceHere
      · rfl
      · exact False.elim (hs (hh.2.2.mp hx))
    have hb := SemiprimeD1PacketModeOriginal.row_test_true n F r a arity owner packet i g tile
      endpoint he hside hs bit
    rw [sameBit_value] at hb
    have hb' : (row.slot.val.testBit i.val == tile.val.testBit i.val)=true := hb
    have hrowbit : row.bit=bit := (wire_data a endpoint bit).1
    have hti : item.tile=tile.val := acquireOne_tile source packet i _ mode
    have htl : tile.val<2^a := tile.isLt.trans_le (Nat.pow_le_pow_right (by omega) (by omega))
    have hm : item.mode=mode := SemiprimeD1PacketModeMask.acquireOne_mode source packet i _ mode
    rw [hc]
    simp only [hip,htf,hsf,Bool.not_false,Bool.and_true,hti,Nat.mod_eq_of_lt htl,hb',hrowbit,ite_true,
      hs,ite_false,hm]
    rfl

end
end RiemannGaussian.SemiprimeD1PacketCoefficientAlignment
