/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackPacketInventoryWidths
/-! # Fixed polynomial caps for the actual inventory replay fragments -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackPacketInventoryRowCost
open SemiprimeD1StackPacketInventoryEncoding SemiprimeD1StackPacketInventoryStepEncoding
open SemiprimeD1StackPacketInventoryWidths SemiprimeD1StackPacketInventoryStep
open SemiprimeD1TensorTapeCodec (vectorBits)
namespace D
export SemiprimeD1StackSourceKeyFrequencyEncoding (coded encoded dictionary read)
end D
/-- Every copied/scanned/unread catalogue byte is charged to the same actual lookup source. -/
theorem readBound_le (q:List Bool) (rows:List (List Bool×List Bool)):
    SemiprimeD1StackPacketInventoryRead.readBound q rows  ≤
      200*(q.length+1)*((SemiprimeD1StackOwnerLookup.records rows []).length+1):=by
  have hu:=(SemiprimeD1StackPacketRowsClock.lookup_lengths q rows).2
  unfold SemiprimeD1StackPacketInventoryRead.readBound SemiprimeD1StackOwnerLookupBounds.runBound
  nlinarith
/-- Uniform cubic read cap in actual source width; historical overrides are all included. -/
theorem readBound_cubic (S:Nat) (hS:1 ≤ S) (q:List Bool) (rows:List (List Bool×List Bool))
    (hq:q.length ≤ 21*S) (hd:(SemiprimeD1StackOwnerLookup.records rows []).length ≤ 50*S^2):
    SemiprimeD1StackPacketInventoryRead.readBound q rows ≤ 300000*S^3:=by
  have hh:=readBound_le q rows
  have hp:=Nat.mul_le_mul (show 200*(q.length+1) ≤ 200*(22*S) by omega)
    (show (SemiprimeD1StackOwnerLookup.records rows []).length+1 ≤ 51*S^2 by
      have h2:1 ≤ S^2:=by nlinarith
      omega)
  have he:200*(22*S)*(51*S^2) ≤ 300000*S^3:=by nlinarith
  exact hh.trans (hp.trans he)
/-- Both dictionaries actually scanned by the source have quadratic retained byte size. -/
theorem dictionary_caps (S m:Nat) (hS:1 ≤ S) (hm:m ≤ S) (s:Summary) (hs:Sized m S s):
    (D.dictionary s.classes).length ≤ 50*S^2 ∧ (D.dictionary s.seen).length ≤ 50*S^2:=by
  have hc:=B.dictionary_length m S (classSummary s) hs.classes
  have hv:=B.dictionary_length m (20*S) (seenSummary s) hs.seen
  have hpc:=Nat.mul_le_mul hm (show 2*(S+1+m)+3 ≤ 4*S+5 by omega)
  have hpv:=Nat.mul_le_mul hm (show 2*(20*S+1+m)+3 ≤ 42*S+5 by omega)
  change (D.dictionary s.classes).length ≤ _ at hc
  change (D.dictionary s.seen).length ≤ _ at hv
  constructor <;> nlinarith
/-- One literal whole replay step has a fixed cubic bound in paid source bytes. -/
theorem rowBound_le (a S m:Nat) (hS:1 ≤ S) (hm:m+1 ≤ S) (ha:(alphabet a).length ≤ S)
    (s:Summary) (hs:Sized m S s) (owner factor:List Bool)
    (ho:owner∈(SemiprimeSourceCompactWordBank.acquire 64 a).ids)
    (hf:factor∈(SemiprimeSourceCompactWordBank.acquire 64 a).ids)
    (hk:(key owner factor).length ≤ S):rowBound a s owner factor ≤ 1000000000*S^3:=by
  have hi:=index_length m S s owner factor hs
  have hi':(D.read s.classes (key owner factor)).length ≤ S:=hi.trans (by omega)
  have hn:(Counter.successor (D.read s.classes (key owner factor))).length ≤ S:=
    (SemiprimeD1StackSourceEnvironmentEncoding.successor_length _).trans (by change (index s owner factor).length+1 ≤ S;omega)
  have he:s.edge.length ≤ S:=hs.classes.maximum.trans (by omega)
  have hen:(nextEdge s).length ≤ S:=
    (SemiprimeD1StackSourceEnvironmentEncoding.successor_length s.edge).trans (by
      have hh:s.edge.length ≤ m:=hs.classes.maximum
      omega)
  have hl:=fields_length a owner ho
  have hr:=fields_length a factor hf
  have hp:=oriented_lengths a s owner factor ho hf
  have hp':(oriented a s owner factor).key.length ≤ 20*S:=by omega
  have hv':(oriented a s owner factor).slots.length ≤ 3*S:=by omega
  have hh':(oriented a s owner factor).high.length ≤ S:=by omega
  have hd:=dictionary_caps S m hS (by omega) s hs
  have hq:(D.encoded (key owner factor)).length ≤ 21*S:=by
    simp only [D.encoded,List.length_append,List.length_singleton];omega
  have hqp:(D.encoded (oriented a s owner factor).key).length ≤ 21*S:=by
    simp only [D.encoded,List.length_append,List.length_singleton];omega
  have hc:=readBound_cubic S hS (D.encoded (key owner factor)) (D.coded s.classes) hq hd.1
  have hv:=readBound_cubic S hS (D.encoded (oriented a s owner factor).key) (D.coded s.seen) hqp hd.2
  have h2:S ≤ S^2:=Nat.le_pow (by decide:0<(2:Nat))
  have h3:S^2 ≤ S^3:=by nlinarith
  have hRows:SemiprimeD1StackPacketInventoryRows.rowsBound a owner factor (index s owner factor) ≤ 1000000*S^2:=by
    have hh:(key owner factor).length+(alphabet a).length+1 ≤ 3*S:=by omega
    have hp2:=Nat.pow_le_pow_left hh 2
    unfold SemiprimeD1StackPacketInventoryRows.rowsBound
      SemiprimeD1StackPacketRowsClock.polynomial SemiprimeD1StackPacketRowsClock.inputSize
      SemiprimeD1StackPacketOrientationClock.polynomial SemiprimeD1StackPacketOrientationClock.inputSize
    change 100000*((key owner factor).length+(alphabet a).length+1)^2+1+1+
      (10000*((vectorBits (Reader.fields 64 a owner)).length+(vectorBits (Reader.fields 64 a factor)).length+
      (index s owner factor).length+1)+1)+1 ≤ 1000000*S^2
    nlinarith only [hp2,hl,hr,ha,hi,hm,hS,h2]
  have hqsmall:(D.encoded (key owner factor)).length ≤ S+1:=by
    simp only [D.encoded,List.length_append,List.length_singleton];omega
  have hclass:SemiprimeD1StackPacketInventoryClass.classBound s.classes (key owner factor) ≤ 1000000*S^3:=by
    unfold SemiprimeD1StackPacketInventoryClass.classBound
    omega
  have hseen:SemiprimeD1StackPacketInventoryDiscovery.seenBound s.seen (oriented a s owner factor).key ≤ 1000000*S^3:=by
    unfold SemiprimeD1StackPacketInventoryDiscovery.seenBound
    omega
  unfold rowBound
  omega
end RiemannGaussian.SemiprimeD1StackPacketInventoryRowCost
