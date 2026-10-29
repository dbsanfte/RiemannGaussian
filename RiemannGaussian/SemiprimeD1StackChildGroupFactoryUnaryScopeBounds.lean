/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackChildGroupFactoryCounterBounds
/-! # Actual prepared duplicate-packet unary scopes have a quartic byte cap
Prepared packet vectors may repeat. Their child endpoint count is K times E,
and paid unary global IDs may occupy quadratic bytes in that product, hence
quartic in a common input-count bound. No packet uniqueness is assumed.
-/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackChildGroupFactoryUnaryScopeBounds
namespace E
export SemiprimeD1StackChildGroupFactoryBucketParse (Endpoint)
end E
namespace B
export SemiprimeD1StackChildGroupFactoryLeftPortsLoop (Bucket)
end B
namespace Code
export SemiprimeD1StackChildGroupFactoryCatalogueCodecs (buckets)
end Code
namespace C
export SemiprimeD1StackChildGroupFactoryCounterBounds (catalogue_count generated_value)
end C
namespace O
export SemiprimeD1StackPortOrdinalStream (result)
end O
open SemiprimeBitArithmetic (bitValue)
/-- Literal converted unary bytes are bounded by actual ID values, not arbitrary binary address values. -/
theorem unary_length (words:List (List Bool)) (cap:Nat) (hv:∀w∈words,bitValue w≤cap):
    (O.result words).length≤words.length*(2*cap+2)+1:=by
  have h:=SemiprimeD1StackPortOrdinalStreamBounds.bank_length
    (words.map fun w=>List.replicate (bitValue w) true) cap (by
      intro u hu
      obtain ⟨w,hw,rfl⟩:=List.mem_map.mp hu
      simpa only [List.length_replicate] using hv w hw)
  simpa only [O.result,List.length_map] using h
/-- The actual logged bucket port field is exactly the physically converted child-global IDs. -/
theorem bucket_ports (packets:List (List Bool)) (es:List E.Endpoint) (position:List Bool)
    (b:B.Bucket) (hb:b∈Code.buckets packets es position):
    b.ports=O.result (b.children.map Prod.snd):=by
  induction packets generalizing position with
  | nil=>simp only [Code.buckets,List.not_mem_nil] at hb
  | cons packet packets ih=>
    simp only [Code.buckets,List.mem_cons] at hb
    rcases hb with rfl|hb
    · rfl
    · exact ih _ hb
/-- Every observed packet contributes one real bucket, including empty and repeated packets. -/
theorem buckets_length (packets:List (List Bool)) (es:List E.Endpoint) (position:List Bool):
    (Code.buckets packets es position).length=packets.length:=by
  induction packets generalizing position with
  | nil=>rfl
  | cons packet packets ih=>simp only [Code.buckets,List.length_cons,ih]
/-- Sum of ALL actual physically emitted right-port scope fields. -/
def scopeMass (bs:List B.Bucket):Nat:=(bs.map fun b=>b.ports.length).sum
/-- Generic exact-codec byte estimate, charging the terminator in every empty bucket as well. -/
theorem scopeMass_le (bs:List B.Bucket) (cap:Nat)
    (hc:∀b∈bs,b.ports=O.result (b.children.map Prod.snd))
    (hv:∀p∈bs.flatMap (fun b=>b.children),bitValue p.2≤cap):
    scopeMass bs≤(bs.flatMap (fun b=>b.children)).length*(2*cap+2)+bs.length:=by
  induction bs with
  | nil=>simp only [scopeMass,List.map_nil,List.sum_nil,List.flatMap_nil,List.length_nil,Nat.zero_mul,Nat.add_zero,le_refl]
  | cons b bs ih=>
    have hhead:=unary_length (b.children.map Prod.snd) cap (by
      intro w hw
      obtain ⟨p,hp,rfl⟩:=List.mem_map.mp hw
      exact hv p (by simp only [List.flatMap_cons,List.mem_append];exact Or.inl hp))
    rw [←hc b List.mem_cons_self] at hhead
    simp only [List.length_map] at hhead
    have htail:=ih (fun c h=>hc c (List.mem_cons_of_mem b h)) (fun p hp=>hv p (by
      simp only [List.flatMap_cons,List.mem_append];exact Or.inr hp))
    simp only [scopeMass,List.map_cons,List.sum_cons,List.flatMap_cons,List.length_append,List.length_cons] at htail ⊢
    nlinarith
/-- Actual complete source starts the distinct child-global counter at zero: duplicate-safe scope bound. -/
theorem generated_scopeMass (packets:List (List Bool)) (es:List E.Endpoint):
    scopeMass (Code.buckets packets es [])≤
      (packets.length*es.length)*(2*(packets.length*es.length)+2)+packets.length:=by
  have h:=scopeMass_le (Code.buckets packets es []) (packets.length*es.length)
    (bucket_ports packets es []) (C.generated_value packets es)
  have hc:=C.catalogue_count packets es []
  rw [buckets_length] at h
  nlinarith
/-- A common paid count bound yields a genuine quartic, never a quadratic, prepared unary-port estimate. -/
theorem generated_scopeMass_quartic (packets:List (List Bool)) (es:List E.Endpoint) (S:Nat)
    (hk:packets.length≤S) (he:es.length≤S):
    scopeMass (Code.buckets packets es [])≤5*(S+1)^4:=by
  have h:=generated_scopeMass packets es
  have hp:packets.length*es.length≤S*S:=Nat.mul_le_mul hk he
  have hsq:(packets.length*es.length)^2≤(S*S)^2:=Nat.pow_le_pow_left hp 2
  nlinarith
end RiemannGaussian.SemiprimeD1StackChildGroupFactoryUnaryScopeBounds
