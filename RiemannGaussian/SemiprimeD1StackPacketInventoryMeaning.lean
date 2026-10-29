/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackPacketInventoryEncoding
/-! # Exact sparse inventory meaning without native clock transfer
Only stored literal bytes, packet order, positive edge words and placements are
compared. The original report clock supplies no machine time theorem.
-/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackPacketInventoryMeaning
open SemiprimeD1StackPacketInventoryEncoding
namespace Old
export SemiprimeD1PacketInventory (State initial step replay)
end Old
namespace T
export SemiprimeSourceHistogramTrie (stored bump bump_old bump_stored lookup lookup_bits stored_empty)
end T
/-- The paid compact machine successor is the exact old compact successor, including padded input words. -/
theorem successor_original (word:List Bool):
    Counter.successor word=(SemiprimeSourceCompactBits.increment word).bits:=by
  apply SemiprimeSourceCompactWordIds.compact_value_injective _ _ (Counter.successor_compact _)
    (SemiprimeSourceCompactBits.increment_compact _)
  rw [Counter.successor_value,SemiprimeSourceCompactBits.increment_value]
/-- Exact source-cache meaning; report clocks and trie allocation shapes are deliberately absent. -/
structure Rel (s:Summary) (old:Old.State):Prop where
  /-- Every raw class key returns its actual old counter bytes. -/
  classes:∀q,Dict.read s.classes q=T.stored old.classes q
  /-- Every observed packet marker has exact byte lookup meaning. -/
  seen:∀q,Dict.read s.seen q=T.stored old.seen q
  /-- Every framed raw packet-slot address has its actual positive edge bytes. -/
  slots:∀q,Dict.read s.slots q=T.stored old.slots q
  /-- Exact newest-first first-discovery order. -/
  packets:s.packets=old.packets
  /-- Exact compact positive occurrence word. -/
  edge:s.edge=old.next
/-- No prepared dictionary, edge or packet is supplied to either empty source. -/
theorem empty_rel (clock:Nat):Rel empty (Old.initial clock):=by
  refine ⟨?_,?_,?_,rfl,rfl⟩ <;> intro q <;> exact (T.stored_empty q).symm
/-- Exact one-occurrence old placement, including raw bytes and validity. -/
theorem step_placement (a:Nat) (s:Summary) (old:Old.State) (raw:List Bool) (h:Rel s old):
    (step a s raw).placements=s.placements++[(Old.step (SemiprimeSourceHistogramRows.acquire 64 a) a old raw).1]:=by
  have hc:(T.bump old.classes raw).old=Dict.read s.classes raw:=by rw [T.bump_old,h.classes]
  change s.placements++[_]=s.placements++[_]
  rw [Old.step]
  dsimp only
  rw [hc,←h.edge,←successor_original]
/-- Actual head overrides implement every original sparse map and discovery transition exactly. -/
theorem step_rel (a:Nat) (s:Summary) (old:Old.State) (raw:List Bool) (h:Rel s old):
    Rel (step a s raw) (Old.step (SemiprimeSourceHistogramRows.acquire 64 a) a old raw).2:=by
  have hc:(T.bump old.classes raw).old=Dict.read s.classes raw:=by rw [T.bump_old,h.classes]
  let rows:=SemiprimeD1PacketRows.read (SemiprimeSourceHistogramRows.acquire 64 a) a raw
  let out:=SemiprimeD1OrientationBits.acquire rows.left rows.right (Dict.read s.classes raw)
  constructor
  · intro q
    change Dict.read ((raw,Counter.successor (Dict.read s.classes raw))::s.classes) q=T.stored (T.bump old.classes raw).trie q
    rw [override_read,T.bump_stored,←h.classes raw,←successor_original,←h.classes q]
    by_cases he:raw=q <;> simp only [he,eq_comm,ite_true,ite_false]
  · intro q
    change Dict.read ((out.key,[true])::s.seen) q=_
    change _=T.stored (SemiprimeSourceHistogramTrieStore.put old.seen
      (SemiprimeD1OrientationBits.acquire rows.left rows.right (T.bump old.classes raw).old).key [true]).trie q
    rw [hc,override_read,SemiprimeSourceHistogramTrieStore.put_stored,←h.seen q]
    change (if out.key=q then [true] else Dict.read s.seen q)=(if q=out.key then [true] else Dict.read s.seen q)
    by_cases he:out.key=q
    · rw [he]
    · simp only [he,Ne.symm he,ite_false]
  · intro q
    change Dict.read ((SemiprimeSourceHistogramKeyBits.frame out.key out.slots,Counter.successor s.edge)::s.slots) q=_
    change _=T.stored (SemiprimeSourceHistogramTrieStore.put old.slots
      (SemiprimeSourceHistogramKeyBits.pair
        (SemiprimeD1OrientationBits.acquire rows.left rows.right (T.bump old.classes raw).old).key
        (SemiprimeD1OrientationBits.acquire rows.left rows.right (T.bump old.classes raw).old).slots).bits
      (SemiprimeSourceCompactBits.increment old.next).bits).trie q
    rw [hc,SemiprimeSourceHistogramKeyBits.pair_bits,override_read,
      SemiprimeSourceHistogramTrieStore.put_stored,←h.edge,←successor_original,←h.slots q]
    change (if SemiprimeSourceHistogramKeyBits.frame out.key out.slots=q then Counter.successor s.edge else Dict.read s.slots q)=
      (if q=SemiprimeSourceHistogramKeyBits.frame out.key out.slots then Counter.successor s.edge else Dict.read s.slots q)
    by_cases he:SemiprimeSourceHistogramKeyBits.frame out.key out.slots=q
    · rw [he]
    · simp only [he,Ne.symm he,ite_false]
  · change (if (Dict.read s.seen out.key).isEmpty then out.key::s.packets else s.packets)=_
    change _=(if (T.lookup old.seen (SemiprimeD1OrientationBits.acquire rows.left rows.right (T.bump old.classes raw).old).key).bits.isEmpty then
      (SemiprimeSourceCompactBits.copy (SemiprimeD1OrientationBits.acquire rows.left rows.right (T.bump old.classes raw).old).key).bits::old.packets else old.packets)
    rw [hc,T.lookup_bits,←h.seen out.key,SemiprimeSourceCompactBits.copy_bits,h.packets]
  · change Counter.successor s.edge=(SemiprimeSourceCompactBits.increment old.next).bits
    rw [h.edge,successor_original]
/-- Same chronological fold gives all original placements and exact final sparse state, independent of native report values. -/
theorem replay_rel (a:Nat) (keys:List (List Bool)) (s:Summary) (old:Old.State) (h:Rel s old):
    (keys.foldl (step a) s).placements=s.placements++(Old.replay (SemiprimeSourceHistogramRows.acquire 64 a) a keys old).1 ∧
      Rel (keys.foldl (step a) s) (Old.replay (SemiprimeSourceHistogramRows.acquire 64 a) a keys old).2:=by
  induction keys generalizing s old with
  | nil=>exact ⟨(List.append_nil _).symm,h⟩
  | cons raw keys ih=>
    obtain ⟨hp,hr⟩:=ih (step a s raw) (Old.step (SemiprimeSourceHistogramRows.acquire 64 a) a old raw).2 (step_rel a s old raw h)
    refine ⟨?_,hr⟩
    rw [List.foldl_cons,hp,step_placement a s old raw h,List.append_assoc]
    rfl
/-- Complete original sparse replay from physically empty maps and zero edge. -/
theorem acquire_original (a:Nat) (keys:List (List Bool)) (clock:Nat):
    (acquire a keys).placements=(Old.replay (SemiprimeSourceHistogramRows.acquire 64 a) a keys (Old.initial clock)).1 ∧
      Rel (acquire a keys) (Old.replay (SemiprimeSourceHistogramRows.acquire 64 a) a keys (Old.initial clock)).2:=by
  exact replay_rel a keys empty (Old.initial clock) (empty_rel clock)
end RiemannGaussian.SemiprimeD1StackPacketInventoryMeaning
