/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackChildGroupFactoryInputCapacities
import RiemannGaussian.SemiprimeD1StackChildGroupFactoryBucketsBounds
/-! # Whole actual activation/endpoint/bucket prefix has one fixed quartic rate
This entire prefix is acquired once by its literal source. Its stopped physical
bank is bounded from that SAME trace, rather than from any recursive child's
runtime or a native acquisition report clock.
-/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackChildGroupFactoryForwardBucketsBounds
open SemiprimeD1StackChildGroupFactoryRoles SemiprimeD1StackChildGroupFactoryWiring
open SemiprimeD1StackChildGroupFactory SemiprimeD1StackProcedureTrace
namespace F
export SemiprimeD1StackChildGroupFactoryForwardBucketsSource (endpoints result timeBound source_trace)
end F
namespace Cap
export SemiprimeD1StackChildGroupFactoryInputCapacities
  (endpoint_bytes endpoints_count packets_count packet_bytes packet_tape)
export SemiprimeD1StackChildGroupFactoryForwardBounds (capacity)
export SemiprimeD1StackChildGroupFactoryTraceBounds (Valid inputBytes input_word_le)
end Cap
namespace P
export SemiprimeD1StackChildGroupFactoryEndpointParse (Fields)
end P
/-- Actual global-zero bucket source has a fixed quartic bound even for repeated prepared packets. -/
theorem bucket_time (before:Stack→List Bool) (i:Inputs) (a coordinate:Nat) (ids packets:List (List Bool))
    (fields:List P.Fields) (hv:Cap.Valid i a coordinate ids packets fields):
    SemiprimeD1StackChildGroupFactoryBucketsSource.timeBound before packets (F.endpoints i a coordinate ids fields) []≤
      1000000000000*(Cap.capacity i+1)^4:=by
  let S:=Cap.capacity i
  let es:=F.endpoints i a coordinate ids fields
  have he:es.length≤S:=Cap.endpoints_count i a coordinate ids packets fields hv
  have hk:packets.length≤S:=Cap.packets_count i a coordinate ids packets fields hv
  have htape:(SemiprimeD1TensorTapeCodec.vectorBits packets).length≤S:=Cap.packet_tape i a coordinate ids packets fields hv
  have hm:packets.length*es.length≤S*S:=Nat.mul_le_mul hk he
  have h:=SemiprimeD1StackChildGroupFactoryBucketsBounds.source_time before packets es [] S S
    (2*(packets.length*es.length)) (packets.length*es.length)
    (Cap.endpoint_bytes i a coordinate ids packets fields hv) (Cap.packet_bytes i a coordinate ids packets fields hv)
    (by simp only [List.length_nil,Nat.zero_add,le_refl])
    (by simp only [SemiprimeBitArithmetic.bitValue,Nat.zero_add,le_refl])
  have hsize:S+S+2*(packets.length*es.length)+packets.length*es.length+
      (SemiprimeD1TensorTapeCodec.vectorBits packets).length+1≤10*(S+1)^2:=by nlinarith
  have hmajor:1000000000*(S+S+2*(packets.length*es.length)+packets.length*es.length+
      (SemiprimeD1TensorTapeCodec.vectorBits packets).length+1)*(es.length+1)*(packets.length+1)≤
      1000000000*(10*(S+1)^2)*(S+1)*(S+1):=by gcongr
  have heq:1000000000*(10*(S+1)^2)*(S+1)*(S+1)=10000000000*(S+1)^4:=by ring
  change SemiprimeD1StackChildGroupFactoryBucketsSource.timeBound before packets es []≤_
  rw [heq] at hmajor
  nlinarith
/-- Whole actual frontdoor through chronological buckets has fixed coefficient/degree before every input. -/
theorem timeBound_le (i:Inputs) (a coordinate:Nat) (ids packets:List (List Bool)) (fields:List P.Fields)
    (hv:Cap.Valid i a coordinate ids packets fields):
    F.timeBound i a coordinate ids packets fields≤10000000000000*(Cap.capacity i+1)^4:=by
  have hforward:=SemiprimeD1StackChildGroupFactoryForwardBounds.timeBound_le i a coordinate ids fields
    hv.id_members hv.environment hv.catalogue hv.colour hv.count hv.pairs hv.placements hv.domain
  have hb:=bucket_time (SemiprimeD1StackChildGroupFactoryForwardSource.result i a coordinate ids fields)
    i a coordinate ids packets fields hv
  dsimp only [F.timeBound]
  nlinarith
/-- ALL115 actually stopped words are bounded from this SAME successful prefix, paid once. -/
theorem result_word_le (i:Inputs) (a coordinate:Nat) (ids packets:List (List Bool)) (fields:List P.Fields)
    (hv:Cap.Valid i a coordinate ids packets fields):
    ∀k,(F.result i a coordinate ids packets fields k).length≤100000000000000*(Cap.capacity i+1)^4:=by
  obtain ⟨t,ht,hr⟩:=F.source_trace i a coordinate ids packets fields hv.id_members hv.environment
    hv.catalogue hv.colour hv.count hv.pairs hv.placements hv.domain hv.packet_tape
  obtain ⟨finish,hfinish,hat⟩:=hr [] (initial i) ⟨rfl,rfl,rfl⟩
  have hd:=SemiprimeD1StackReturnLink.run_data_bound program t (Cap.inputBytes i) (initial i) finish
    (Cap.input_word_le i) hfinish
  rw [hat.2.1] at hd
  have hc:=timeBound_le i a coordinate ids packets fields hv
  have hi:Cap.inputBytes i≤Cap.capacity i:=by dsimp only [Cap.capacity];omega
  intro k
  have h:=hd k
  have hp:Cap.capacity i≤(Cap.capacity i+1)^4:=
    (Nat.le_succ _).trans (Nat.le_pow (by decide:0<(4:Nat)))
  nlinarith
end RiemannGaussian.SemiprimeD1StackChildGroupFactoryForwardBucketsBounds
