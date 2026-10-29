/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackChildGroupFactoryBucketOneBounds
import RiemannGaussian.SemiprimeD1StackChildGroupFactoryBucketsSource
/-! # Whole actual chronological bucket catalogue clock and bytes
The same global-counter budgets span every packet and are preserved by real
binary successors. Empty and repeated packets are retained. No earlier output
log is charged as a recursively growing runtime bound.
-/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackChildGroupFactoryBucketsBounds
open SemiprimeD1StackChildGroupFactoryRoles
namespace E
export SemiprimeD1StackChildGroupFactoryBucketParse (Endpoint)
end E
namespace Op
export SemiprimeD1StackChildGroupFactoryOperationBounds (endpointBytes)
end Op
namespace Scan
export SemiprimeD1StackChildGroupFactoryBucketLoopView (finalPosition portWords records selected)
end Scan
namespace Count
export SemiprimeD1StackChildGroupFactoryCounterBounds (scan_bounds selected_word_bounds selected_length)
end Count
namespace One
export SemiprimeD1StackChildGroupFactoryBucketOne (result timeBound)
export SemiprimeD1StackChildGroupFactoryBucketOneView (bucketRow)
end One
namespace Loop
export SemiprimeD1StackChildGroupFactoryBucketsLoop (result timeBound)
export SemiprimeD1StackChildGroupFactoryBucketsLoopView (records)
end Loop
/-- Exact per-bucket unary port bytes are bounded by derived generated-ID VALUE, not source addresses. -/
theorem unary_bytes (es:List E.Endpoint) (packet position:List Bool) (G:Nat)
    (hv:SemiprimeBitArithmetic.bitValue position+es.length≤G):
    (SemiprimeD1StackPortOrdinalStream.result (Scan.portWords es packet position)).length≤es.length*(2*G+2)+1:=by
  have h:=SemiprimeD1StackChildGroupFactoryUnaryScopeBounds.unary_length (Scan.portWords es packet position) G (by
    intro w hw;obtain ⟨p,hp,rfl⟩:=List.mem_map.mp hw
    have ht:=(Count.selected_word_bounds es packet position p hp).2
    omega)
  have hn:=Count.selected_length es packet position
  simp only [Scan.portWords,List.length_map] at h
  dsimp only [Scan.portWords]
  nlinarith
/-- One real bucket row includes the actual raw packet, child vector and converted unary scope. -/
theorem bucket_bytes (es:List E.Endpoint) (packet position:List Bool) (B L G:Nat)
    (hc:∀e∈es,Op.endpointBytes e≤B) (hp:position.length+2*es.length≤L)
    (hv:SemiprimeBitArithmetic.bitValue position+es.length≤G):
    (One.bucketRow es packet position).length≤1000*(B+packet.length+L+G+1)*(es.length+1):=by
  have hh:=SemiprimeD1StackChildGroupFactoryBucketScanBounds.child_bytes es packet position B L hc hp
  have hu:=unary_bytes es packet position G hv
  simp only [One.bucketRow,SemiprimeD1StackChildGroupFactoryBucketRecord.row,
    SemiprimeD1StackChildGroupFactoryBucketRecord.payload,SemiprimeSourceHistogramKeyBits.frame_length,
    List.length_cons,List.length_append,List.length_nil]
  nlinarith
/-- All packets use one fixed metadata allowance; the real counter budgets survive each actual scan. -/
theorem loop_time (packets:List (List Bool)) (before:Stack→List Bool) (es:List E.Endpoint)
    (position:List Bool) (B P L G:Nat)
    (hc:∀e∈es,Op.endpointBytes e≤B) (hpack:∀packet∈packets,packet.length≤P)
    (hp:position.length+2*(packets.length*es.length)≤L)
    (hv:SemiprimeBitArithmetic.bitValue position+packets.length*es.length≤G):
    Loop.timeBound packets before es position≤100000000*(B+P+L+G+1)*(es.length+1)*(packets.length+1):=by
  induction packets generalizing before position with
  | nil=>simp only [Loop.timeBound,List.length_nil,Nat.zero_add,Nat.mul_one];nlinarith
  | cons packet packets ih=>
    have hh:=hpack packet List.mem_cons_self
    simp only [List.length_cons,Nat.add_mul,Nat.one_mul] at hp hv
    have hrow:=SemiprimeD1StackChildGroupFactoryBucketOneBounds.timeBound_le before es packet
      (SemiprimeD1TensorTapeCodec.vectorBits packets) position B L G hc (by omega) (by omega)
    have hs:=Count.scan_bounds es packet position
    have ht:=ih (One.result before es packet (SemiprimeD1TensorTapeCodec.vectorBits packets) position)
      (Scan.finalPosition es packet position) (fun p h=>hpack p (List.mem_cons_of_mem packet h))
      (by omega) (by omega)
    simp only [Loop.timeBound,List.length_cons]
    nlinarith
/-- Actual complete chronological row bytes have the same additive per-packet count envelope. -/
theorem records_bytes (packets:List (List Bool)) (es:List E.Endpoint) (position:List Bool) (B P L G:Nat)
    (hc:∀e∈es,Op.endpointBytes e≤B) (hpack:∀packet∈packets,packet.length≤P)
    (hp:position.length+2*(packets.length*es.length)≤L)
    (hv:SemiprimeBitArithmetic.bitValue position+packets.length*es.length≤G):
    (Loop.records packets es position).length≤1000*(B+P+L+G+1)*(es.length+1)*packets.length:=by
  induction packets generalizing position with
  | nil=>simp only [Loop.records,List.length_nil,Nat.mul_zero,le_refl]
  | cons packet packets ih=>
    have hh:=hpack packet List.mem_cons_self
    simp only [List.length_cons,Nat.add_mul,Nat.one_mul] at hp hv
    have hrow:=bucket_bytes es packet position B L G hc (by omega) (by omega)
    have hs:=Count.scan_bounds es packet position
    have ht:=ih (Scan.finalPosition es packet position) (fun p h=>hpack p (List.mem_cons_of_mem packet h))
      (by omega) (by omega)
    simp only [Loop.records,List.length_append,List.length_cons]
    nlinarith
/-- Entire actual source has a fixed physical-byte product envelope, including final copy/seed/reversal. -/
theorem source_time (before:Stack→List Bool) (packets:List (List Bool)) (es:List E.Endpoint)
    (position:List Bool) (B P L G:Nat)
    (hc:∀e∈es,Op.endpointBytes e≤B) (hpack:∀packet∈packets,packet.length≤P)
    (hp:position.length+2*(packets.length*es.length)≤L)
    (hv:SemiprimeBitArithmetic.bitValue position+packets.length*es.length≤G):
    SemiprimeD1StackChildGroupFactoryBucketsSource.timeBound before packets es position≤
      1000000000*(B+P+L+G+(SemiprimeD1TensorTapeCodec.vectorBits packets).length+1)*(es.length+1)*(packets.length+1):=by
  have ht:=loop_time packets (SemiprimeD1StackChildGroupFactoryBucketsSource.copied before packets) es position B P L G hc hpack hp hv
  have hb:=records_bytes packets es position B P L G hc hpack hp hv
  let Q:=(B+P+L+G+1)*(es.length+1)*(packets.length+1)
  let V:=(es.length+1)*(packets.length+1)
  have hqpos:0<Q:=by dsimp only [Q];positivity
  have hq:1≤Q:=hqpos
  have hv':0<V:=by dsimp only [V];positivity
  have ht':Loop.timeBound packets (SemiprimeD1StackChildGroupFactoryBucketsSource.copied before packets) es position≤100000000*Q:=by
    have heq:100000000*(B+P+L+G+1)*(es.length+1)*(packets.length+1)=100000000*Q:=by dsimp only [Q];ring
    rw [←heq]
    exact ht
  have hb':(Loop.records packets es position).length≤1000*Q:=by
    apply hb.trans
    dsimp only [Q]
    calc
      _≤1000*(B+P+L+G+1)*(es.length+1)*(packets.length+1):=by gcongr;omega
      _=_:=by ring
  have hvlen:(SemiprimeD1TensorTapeCodec.vectorBits packets).length≤
      (SemiprimeD1TensorTapeCodec.vectorBits packets).length*V:=Nat.le_mul_of_pos_right _ hv'
  have heq:1000000000*(B+P+L+G+(SemiprimeD1TensorTapeCodec.vectorBits packets).length+1)*(es.length+1)*(packets.length+1)=
      1000000000*Q+1000000000*((SemiprimeD1TensorTapeCodec.vectorBits packets).length*V):=by
    dsimp only [Q,V];ring
  rw [heq]
  dsimp only [SemiprimeD1StackChildGroupFactoryBucketsSource.timeBound]
  omega

end RiemannGaussian.SemiprimeD1StackChildGroupFactoryBucketsBounds
