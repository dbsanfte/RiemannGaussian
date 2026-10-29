/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1PacketReplayOriginal
import RiemannGaussian.SemiprimeD1PacketSlotCapacity

/-! # Full-slot coverage and capacity of the actual sparse packet inventory
Finite palette functions occur only in this erased image-counting proof. The
executed inventory enumerates actual real ports and observed packet keys only.
-/
set_option autoImplicit false
set_option maxHeartbeats 2600000
namespace RiemannGaussian.SemiprimeD1PacketReplayCapacity
open SemiprimeD1PacketReplayOriginal SemiprimeD1OrientationPalette
open SemiprimeD1OrientationComplete SemiprimeBitArithmetic
open OAI.Algorithms.SubexponentialSAT.MulticolorTypes

/-- Erased finite padded-input domain used solely for cardinality. -/
abbrev Input (r a H : ℕ) := (Word r a×Word r a)×Fin H

/-- Deterministic orientation map, used only for a finite image proof. -/
noncomputable def encode (r a H : ℕ) (input : Input r a H) : List Bool×(Fin a→Bool) :=
  let out := SemiprimeD1OrientationBits.acquire (fields input.1.1) (fields input.1.2)
    (SemiprimeSourceHistogramHeadRefinement.numberKey input.2.val)
  (out.key,fun q => (out.slots[q.val]?).getD false)

/-- Every slot of each actually observed packet has a genuine finite original
palette/padding preimage. No desired inverse or bucket catalogue is supplied. -/
theorem covers (n F r a : ℕ) [NeZero r] (arity : Fin F→ℕ)
    (owner : ((e : Fin F)×Fin (arity e))→Fin n) (packet : List Bool)
    (hp : packet∈(acquire n F r a arity owner).state.packets) (slot : Fin a→Bool) :
    ∃ input : Input r a (bitValue (acquire n F r a arity owner).padding.padding),
      encode r a _ input=(packet,slot) := by
  obtain ⟨left,right,j,hl,hr,hla,hra,hj,hjlt,hkey⟩ :=
    observed_generated n F r a arity owner packet hp
  let H := bitValue (acquire n F r a arity owner).padding.padding
  have hd : 2^a∣H := SemiprimeD1PacketPadding.packet_dvd_padding n F r a arity owner
  have hfull := SemiprimeD1OrientationForward.generated_full_slots r a left right j
    (List.ofFn slot) H (hl.trans hr.symm) hl hla hra hj hjlt hd List.length_ofFn
  let back := SemiprimeD1OrientationInverse.recover
    (SemiprimeD1OrientationBits.acquire left right j).key (List.ofFn slot)
  change SemiprimeSourceCompactBits.Compact back.index ∧ bitValue back.index<H ∧ _ at hfull
  obtain ⟨leftId,_,hleft⟩ := hfull.2.2.2.1
  obtain ⟨rightId,_,hright⟩ := hfull.2.2.2.2
  have hi : SemiprimeSourceHistogramHeadRefinement.numberKey (bitValue back.index)=back.index := by
    apply SemiprimeSourceCompactWordIds.compact_value_injective _ _
      (SemiprimeSourceHistogramHeadRefinement.numberKey_compact _) hfull.1
    exact SemiprimeSourceHistogramHeadRefinement.numberKey_value _
  refine ⟨((SemiprimeSourceWordBankSemantics.decode r a leftId,
    SemiprimeSourceWordBankSemantics.decode r a rightId),⟨bitValue back.index,hfull.2.1⟩),?_⟩
  have hk := congrArg Prod.fst hfull.2.2.1
  have hs := congrArg (fun out => out.2.1) hfull.2.2.1
  change (SemiprimeD1OrientationBits.acquire back.left back.right back.index).key=
    (SemiprimeD1OrientationBits.acquire left right j).key at hk
  change (SemiprimeD1OrientationBits.acquire back.left back.right back.index).slots=List.ofFn slot at hs
  apply Prod.ext
  · change (SemiprimeD1OrientationBits.acquire _ _ _).key=packet
    rw [hleft,hright,hi,hk,hkey]
  · funext q
    change ((SemiprimeD1OrientationBits.acquire _ _ _).slots[q.val]?).getD false=slot q
    rw [hleft,hright,hi,hs]
    simp only [List.getElem?_ofFn,q.isLt,↓reduceDIte,Option.getD_some]

/-- The actual sparse observed-packet capacity is at most the full padded input size. -/
theorem capacity (n F r a : ℕ) [NeZero r] (arity : Fin F→ℕ)
    (owner : ((e : Fin F)×Fin (arity e))→Fin n) :
    (acquire n F r a arity owner).state.packets.length*2^a≤
      r^(2*a)*bitValue (acquire n F r a arity owner).padding.padding := by
  have hh := SemiprimeD1PacketSlotCapacity.boolean_capacity
    (acquire n F r a arity owner).state.packets (packets_nodup n F r a arity owner) a
    (encode r a _) (covers n F r a arity owner)
  simpa only [Input,Word,Fintype.card_prod,Fintype.card_fun,Fintype.card_fin,Fintype.card_bool,
    ←pow_add,←two_mul] using hh

/-- Original degree and D.3 size bounds yield at most3M sparse acquired slots.
Every producer is the literal original-input endpoint; no packet answer is supplied. -/
theorem threeM_capacity (n F r a : ℕ) [NeZero r] (arity : Fin F→ℕ)
    (owner : ((e : Fin F)×Fin (arity e))→Fin n) (Δ : ℕ)
    (ho : ∀ i∈SemiprimeD1CollisionOriginal.ports n F a arity,
      SemiprimeSourceHistogramGrouping.multiplicity (fun i => (owner i).val)
        (SemiprimeD1CollisionOriginal.ports n F a arity) (owner i).val≤Δ)
    (hf : ∀ i∈SemiprimeD1CollisionOriginal.ports n F a arity,
      SemiprimeSourceHistogramGrouping.multiplicity (fun i => n+i.1.val)
        (SemiprimeD1CollisionOriginal.ports n F a arity) (n+i.1.val)≤Δ)
    (hsmall : 2*(r^(2*a))^2*Δ≤(SemiprimeD1CollisionOriginal.ports n F a arity).length)
    (hsize : r^(2*a)*2^a≤(SemiprimeD1CollisionOriginal.ports n F a arity).length) :
    (acquire n F r a arity owner).state.packets.length*2^a≤
      3*(SemiprimeD1CollisionOriginal.ports n F a arity).length :=
  (capacity n F r a arity owner).trans
    (SemiprimeD1PacketPadding.padding_scaled_le n F r a arity owner Δ ho hf hsmall hsize)

end RiemannGaussian.SemiprimeD1PacketReplayCapacity
