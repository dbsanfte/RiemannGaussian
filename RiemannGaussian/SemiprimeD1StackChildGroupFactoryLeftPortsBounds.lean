/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackChildGroupFactoryStructuralByteBounds
import RiemannGaussian.SemiprimeD1StackChildGroupFactoryPortConvertBounds
import RiemannGaussian.SemiprimeD1StackChildGroupFactoryRowByteBounds
/-! # Whole actual left-scope acquisition clock
Each actual nested field visit and every generated unary ordinal VALUE is paid.
The bound depends on the physical retained cache and real child count, not on
recursive-child runtimes or a supplied scope/order answer.
-/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackChildGroupFactoryLeftPortsBounds
open SemiprimeD1StackChildGroupFactoryRoles
namespace Op
export SemiprimeD1StackChildGroupFactoryOperationBounds
  (endpointBytes child_payload_length vertex_time word_log_time bucket_header_time)
end Op
namespace V
export SemiprimeD1StackChildGroupFactoryLeftPortVisit (timeBound cleanupTime)
end V
namespace I
export SemiprimeD1StackChildGroupFactoryLeftPortsInner (Child records timeBound)
end I
namespace B
export SemiprimeD1StackChildGroupFactoryLeftPortsLoop (Bucket records portWords timeBound stepTime)
end B
namespace Source
export SemiprimeD1StackChildGroupFactoryLeftPortsSource (timeBound prepared)
end Source
/-- All actual child parse/test/conditional-log/drain work is linear in raw field bytes. -/
theorem visit_time (p:I.Child) (target:List Bool):
    V.timeBound p.1 p.2 target≤1000*(Op.endpointBytes p.1+p.2.length+target.length+1):=by
  have hc:=Op.child_payload_length p.1 p.2
  have hv:=Op.vertex_time p.1.vertex target
  have hl:=Op.word_log_time p.2
  unfold V.timeBound SemiprimeD1StackChildGroupFactoryChildParse.timeBound V.cleanupTime
  split_ifs <;> dsimp only [Op.endpointBytes] at * <;> omega
/-- One literal child-vector scan pays exactly its actual visited fields. -/
theorem inner_time (children:List I.Child) (target:List Bool) (cap:Nat)
    (hc:∀p∈children,Op.endpointBytes p.1+p.2.length≤cap):
    I.timeBound children target≤1000*(cap+target.length+1)*(children.length+1):=by
  induction children with
  | nil=>simp only [I.timeBound,List.length_nil,Nat.zero_add,Nat.mul_one];omega
  | cons p ps ih=>
    have hp:=hc p List.mem_cons_self
    have hv:=visit_time p target
    have ht:=ih (fun q h=>hc q (List.mem_cons_of_mem p h))
    simp only [I.timeBound,List.length_cons]
    nlinarith
/-- Whole actual packet-major scan, including real empty headers and final EOF. -/
theorem loop_time (buckets:List B.Bucket) (target:List Bool) (cap D:Nat)
    (hc:∀p∈buckets.flatMap (fun b=>b.children),Op.endpointBytes p.1+p.2.length≤cap)
    (hh:∀b∈buckets,b.packet.length+(I.records b.children).length+b.ports.length+1≤cap)
    (hd:(buckets.flatMap (fun b=>b.children)).length≤D):
    B.timeBound buckets target≤10000*(cap+target.length+1)*(D+1)*(buckets.length+1):=by
  induction buckets with
  | nil=>simp only [B.timeBound,List.length_nil,Nat.zero_add,Nat.mul_one];nlinarith
  | cons b bs ih=>
    have hheader:=Op.bucket_header_time b.packet (I.records b.children) b.ports
    have hhead:=hh b List.mem_cons_self
    have hinner:=inner_time b.children target cap (fun p hp=>hc p (by
      simp only [List.flatMap_cons,List.mem_append];exact Or.inl hp))
    have hlen:b.children.length≤D:=by simp only [List.flatMap_cons,List.length_append] at hd;omega
    have ht:=ih (fun p hp=>hc p (by simp only [List.flatMap_cons,List.mem_append];exact Or.inr hp))
      (fun q h=>hh q (List.mem_cons_of_mem b h))
      (by simp only [List.flatMap_cons,List.length_append] at hd;omega)
    have hstep:B.stepTime b target≤10000*(cap+target.length+1)*(D+1):=by
      dsimp only [B.stepTime]
      nlinarith
    simp only [B.timeBound,List.length_cons]
    nlinarith
/-- Actual filtered port-log reversal is bounded by its real binary vector bytes. -/
theorem port_log_length (words:List (List Bool)):
    (words.flatMap SemiprimeD1StackChildGroupFactoryWordLog.row).length≤
      (SemiprimeD1TensorTapeCodec.vectorBits words).length:=by
  change (words.flatMap SemiprimeD1StackChildGroupFactoryBucketEmit.portRow).length≤_
  rw [← SemiprimeD1StackChildGroupFactoryBucketScan.port_records_vector words]
  simp only [List.length_append,List.length_cons,List.length_nil]
  omega
/-- Full actual source: saved-word drain, copy, filter, log reversal, real unary conversion and reuse. -/
theorem source_time (before:Stack→List Bool) (buckets:List B.Bucket) (target:List Bool) (cap D G:Nat)
    (hcap:∀k,(before k).length≤cap)
    (hbs:(B.records buckets).length≤cap)
    (hd:(buckets.flatMap (fun b=>b.children)).length≤D)
    (hv:∀p∈buckets.flatMap (fun b=>b.children),SemiprimeBitArithmetic.bitValue p.2≤G):
    Source.timeBound before buckets target≤
      1000000*(cap+G+target.length+1)*(D+1)*(buckets.length+1):=by
  have hc:∀p∈buckets.flatMap (fun b=>b.children),Op.endpointBytes p.1+p.2.length≤cap:=by
    intro p hp;exact (SemiprimeD1StackChildGroupFactoryStructuralByteBounds.flattened_child_fields buckets p hp).trans hbs
  have hh:∀b∈buckets,b.packet.length+(I.records b.children).length+b.ports.length+1≤cap:=by
    intro b hb;exact (SemiprimeD1StackChildGroupFactoryStructuralByteBounds.bucket_fields buckets b hb).trans hbs
  have ht:=loop_time buckets target cap D hc hh hd
  have hcount:=SemiprimeD1StackChildGroupFactoryRowByteBounds.scope_count buckets target
  have hl:∀w∈B.portWords buckets target,w.length≤cap+G:=by
    intro w hw
    obtain ⟨p,hp,rfl⟩:=SemiprimeD1StackChildGroupFactoryRowByteBounds.scope_word buckets target w hw
    have h:=hc p hp;omega
  have hvalue:∀w∈B.portWords buckets target,SemiprimeBitArithmetic.bitValue w≤cap+G:=by
    intro w hw
    obtain ⟨p,hp,rfl⟩:=SemiprimeD1StackChildGroupFactoryRowByteBounds.scope_word buckets target w hw
    exact (hv p hp).trans (by omega)
  have hconv:=SemiprimeD1StackChildGroupFactoryPortConvertBounds.timeBound_le false
    (Source.prepared before buckets target) (B.portWords buckets target) (cap+G) rfl hl hvalue
  have hbank:=SemiprimeD1StackPortOrdinalStreamBounds.bank_length (B.portWords buckets target) (cap+G) hl
  have hlog:=port_log_length (B.portWords buckets target)
  have hg:=hcap (aux .globalPosition)
  have hD:(B.portWords buckets target).length≤D:=hcount.trans hd
  have hconv':SemiprimeD1StackChildGroupFactoryPortConvert.timeBound false
      (Source.prepared before buckets target) (B.portWords buckets target)≤10000*(D+1)*(cap+G+1):=
    hconv.trans (Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ (by omega)))
  have hbank':(SemiprimeD1TensorTapeCodec.vectorBits (B.portWords buckets target)).length≤D*(2*(cap+G)+2)+1:=
    hbank.trans (Nat.add_le_add_right (Nat.mul_le_mul_right _ hD) _)
  dsimp only [Source.timeBound]
  have hK:1≤buckets.length+1:=by omega
  let Q:Nat:=(cap+G+target.length+1)*(D+1)*(buckets.length+1)
  have hbase:1≤Q:=by dsimp only [Q];exact Nat.succ_le_of_lt (by positivity)
  have hsmall:cap+G+1≤Q:=by
    dsimp only [Q]
    exact (by omega:cap+G+1≤cap+G+target.length+1).trans
      ((Nat.le_mul_of_pos_right _ (by omega)).trans (Nat.le_mul_of_pos_right _ (by omega)))
  have hbankQ:D*(2*(cap+G)+2)+1≤3*Q:=by
    have h: (cap+G+1)*(D+1)≤Q:=by
      apply (Nat.mul_le_mul_right (D+1) (by omega:cap+G+1≤cap+G+target.length+1)).trans
      exact Nat.le_mul_of_pos_right _ (by omega)
    nlinarith
  have hloopQ:B.timeBound buckets target≤10000*Q:=by
    apply ht.trans
    have he:10000*(cap+target.length+1)*(D+1)*(buckets.length+1)=
        10000*((cap+target.length+1)*(D+1)*(buckets.length+1)):=by ring
    rw [he]
    apply Nat.mul_le_mul_left
    exact Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ (by omega))
  have hconvQ:SemiprimeD1StackChildGroupFactoryPortConvert.timeBound false
      (Source.prepared before buckets target) (B.portWords buckets target)≤10000*Q:=by
    apply hconv'.trans
    calc
      10000*(D+1)*(cap+G+1)=10000*((cap+G+1)*(D+1)):=by ring
      _≤10000*Q:=Nat.mul_le_mul_left _ ((Nat.mul_le_mul_right (D+1)
        (by omega:cap+G+1≤cap+G+target.length+1)).trans (Nat.le_mul_of_pos_right _ (by omega)))
  have he:1000000*(cap+G+target.length+1)*(D+1)*(buckets.length+1)=1000000*Q:=by
    dsimp only [Q]
    ring
  rw [he]
  omega
end RiemannGaussian.SemiprimeD1StackChildGroupFactoryLeftPortsBounds
