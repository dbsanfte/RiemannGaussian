/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackPacketInventoryStep
import RiemannGaussian.SemiprimeD1StackSourceKeyFrequencyBytes
import RiemannGaussian.SemiprimeD1StackPacketOrientationLayout
/-! # Actual source-generated sparse cache widths -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackPacketInventoryWidths
open SemiprimeD1StackPacketInventoryEncoding SemiprimeD1StackPacketInventoryStepEncoding
open SemiprimeD1TensorTapeCodec (vectorBits)
namespace B
export SemiprimeD1StackSourceKeyFrequencyBytes (Sized empty_sized read_length_le dictionary_length unread_length_le)
end B
/-- The actual row vector is bounded by twice the actual acquired catalogue bytes and its terminator. -/
theorem fields_length (a:Nat) (id:List Bool) (hi:id∈(SemiprimeSourceCompactWordBank.acquire 64 a).ids):
    (vectorBits (Reader.fields 64 a id)).length ≤ 2*(alphabet a).length+1:=by
  have h:=SemiprimeD1StackPacketRowsClock.lookup_lengths id (SemiprimeD1StackPacketRowsMeaning.originalEntries 64 a)
  rw [(SemiprimeD1StackPacketRowsMeaning.original_lookup 64 a id hi).1] at h
  have hh:=SemiprimeD1StackPacketRowsClock.history_length (Reader.fields 64 a id)
  rw [←SemiprimeD1StackPacketRowsEncoding.prefix_vector]
  rw [List.length_append,List.length_singleton]
  have hc: (SemiprimeD1StackOwnerLookup.records (SemiprimeD1StackPacketRowsMeaning.originalEntries 64 a) []).length=(alphabet a).length:=
    congrArg List.length (SemiprimeD1StackPacketRowsMeaning.catalogue_original a)
  omega
/-- Counter width and both real vector widths bound the complete raw packet, actual slots and remaining high word. -/
theorem oriented_lengths (a:Nat) (s:Summary) (owner factor:List Bool)
    (ho:owner∈(SemiprimeSourceCompactWordBank.acquire 64 a).ids)
    (hf:factor∈(SemiprimeSourceCompactWordBank.acquire 64 a).ids):
    (oriented a s owner factor).key.length ≤ 8*(alphabet a).length+4+(index s owner factor).length ∧
      (oriented a s owner factor).slots.length ≤ 2*(alphabet a).length+1 ∧
      (oriented a s owner factor).high.length ≤ (index s owner factor).length:=by
  have hl:=fields_length a owner ho
  have hr:=fields_length a factor hf
  have he: (Reader.fields 64 a owner).length=(Reader.fields 64 a factor).length:=(read_info a owner factor ho hf).2.2.2
  have hk:=SemiprimeD1StackPacketOrientationLayout.chunks_key (Reader.fields 64 a owner) (Reader.fields 64 a factor) (index s owner factor) he
  have hc:=SemiprimeD1StackPacketOrientationLayout.chunks_length (Reader.fields 64 a owner) (Reader.fields 64 a factor)
  have hs:=SemiprimeD1StackPacketOrientationLayout.slots_length (Reader.fields 64 a owner) (Reader.fields 64 a factor) (index s owner factor) he
  have hh:=SemiprimeD1StackPacketOrientationLayout.high_length (Reader.fields 64 a owner) (Reader.fields 64 a factor) (index s owner factor)
  have hk':(oriented a s owner factor).key.length=
      (SemiprimeD1StackPacketOrientationLoop.chunks (Reader.fields 64 a owner) (Reader.fields 64 a factor)).length+
      (oriented a s owner factor).high.length:=by
    dsimp only [oriented]
    rw [←hk,List.length_append]
  dsimp only [oriented] at hk' ⊢
  exact ⟨by omega,hs.trans hl,hh⟩
/-- Every retained class override is charged by one actual processed occurrence. -/
def classSummary (s:Summary):SemiprimeD1StackSourceKeyFrequencyEncoding.Summary:=⟨s.classes,s.edge⟩
/-- Seen markers retain every historical override, with packet bytes bounded from actual rows. -/
def seenSummary (s:Summary):SemiprimeD1StackSourceKeyFrequencyEncoding.Summary:=⟨s.seen,[]⟩
/-- The two dictionaries actually scanned by the next occurrence have paid bounded widths. -/
structure Sized (m S:Nat) (s:Summary):Prop where
  /-- Actual class records, count payloads and edge width. -/
  classes:B.Sized m S (classSummary s)
  /-- Actual packet records, marker payloads and empty auxiliary maximum. -/
  seen:B.Sized m (20*S) (seenSummary s)
/-- No input dictionary or counter is supplied initially. -/
theorem empty_sized (S:Nat):Sized 0 S empty:=⟨B.empty_sized S,B.empty_sized (20*S)⟩
/-- The real OLD index is a stored physical count or literal empty zero. -/
theorem index_length (m S:Nat) (s:Summary) (owner factor:List Bool) (hs:Sized m S s):
    (index s owner factor).length ≤ m:=B.read_length_le s.classes _ m (fun r hr=>(hs.classes.words r hr).2)
/-- Both actual historical dictionaries remain bounded after the same real source step. -/
theorem step_sized (a m S:Nat) (s:Summary) (owner factor:List Bool)
    (ho:owner∈(SemiprimeSourceCompactWordBank.acquire 64 a).ids)
    (hf:factor∈(SemiprimeSourceCompactWordBank.acquire 64 a).ids)
    (_hS:1 ≤ S) (hm:m+1 ≤ S) (ha:(alphabet a).length ≤ S)
    (hs:Sized m S s) (hk:(key owner factor).length ≤ S):Sized (m+1) S (step a s (key owner factor)):=by
  have hi:=index_length m S s owner factor hs
  have hc:(Counter.successor (index s owner factor)).length ≤ m+1:=
    (SemiprimeD1StackSourceEnvironmentEncoding.successor_length _).trans (by omega)
  have he:(nextEdge s).length ≤ m+1:=
    (SemiprimeD1StackSourceEnvironmentEncoding.successor_length _).trans (by exact Nat.add_le_add_right hs.classes.maximum 1)
  have hp:(oriented a s owner factor).key.length ≤ 20*S:=by
    have hh:=(oriented_lengths a s owner factor ho hf).1
    omega
  rw [step_eq a s owner factor ho hf]
  constructor
  · refine ⟨?_,?_,he⟩
    · exact congrArg (fun n=>n+1) hs.classes.count
    · intro row hr
      rcases List.mem_cons.mp hr with hh|hh
      · cases hh;exact ⟨hk,hc⟩
      · exact ⟨(hs.classes.words row hh).1,(hs.classes.words row hh).2.trans (by omega)⟩
  · refine ⟨?_,?_,Nat.zero_le _⟩
    · exact congrArg (fun n=>n+1) hs.seen.count
    · intro row hr
      rcases List.mem_cons.mp hr with hh|hh
      · cases hh;exact ⟨hp,by simp only [List.length_singleton];omega⟩
      · exact ⟨(hs.seen.words row hh).1,(hs.seen.words row hh).2.trans (by omega)⟩
end RiemannGaussian.SemiprimeD1StackPacketInventoryWidths
