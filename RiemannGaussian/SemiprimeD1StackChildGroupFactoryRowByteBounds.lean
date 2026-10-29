/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackChildGroupFactoryUnaryScopeBounds
import RiemannGaussian.SemiprimeD1StackChildGroupFactoryOrderBounds
import RiemannGaussian.SemiprimeD1StackChildGroupFactoryVertexBodyView
/-! # Uniform actual per-old-vertex scope/order row bytes
All port words come from actual generated global IDs and all order words from
actual first-idx queries. A repeated prepared packet may repeat incidences;
the derived bound remains quartic in paid input counts and applies uniformly
to every numeric old vertex, including isolated/inactive vertices.
-/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackChildGroupFactoryRowByteBounds
namespace Inner
export SemiprimeD1StackChildGroupFactoryLeftPortsInner (portWords)
end Inner
namespace B
export SemiprimeD1StackChildGroupFactoryLeftPortsLoop (Bucket portWords)
end B
namespace E
export SemiprimeD1StackChildGroupFactoryBucketParse (Endpoint)
end E
namespace P
export SemiprimeD1StackChildGroupFactoryOldPortParse (Point)
end P
namespace Old
export SemiprimeD1StackChildGroupFactoryOldPortsLoop (orderWords)
end Old
namespace O
export SemiprimeD1StackPortOrdinalStream (result)
end O
namespace Code
export SemiprimeD1StackChildGroupFactoryCatalogueCodecs (buckets)
end Code
open SemiprimeBitArithmetic (bitValue)
/-- Real numeric-vertex filtering never adds an occurrence to a child vector. -/
theorem inner_count (children:List (E.Endpoint×List Bool)) (target:List Bool):
    (Inner.portWords children target).length≤children.length:=by
  induction children with
  | nil=>exact le_rfl
  | cons p ps ih=>
    by_cases h:bitValue p.1.vertex=bitValue target <;>
      simp only [Inner.portWords,h,ite_true,ite_false,List.length_cons] <;> omega
/-- Every output ID word is an actually emitted child's raw binary global-ID word. -/
theorem inner_word (children:List (E.Endpoint×List Bool)) (target word:List Bool)
    (hw:word∈Inner.portWords children target):∃p∈children,p.2=word:=by
  induction children with
  | nil=>simp only [Inner.portWords,List.not_mem_nil] at hw
  | cons p ps ih=>
    by_cases h:bitValue p.1.vertex=bitValue target
    · simp only [Inner.portWords,h,ite_true,List.mem_cons] at hw
      rcases hw with rfl|hw
      · exact ⟨p,List.mem_cons_self,rfl⟩
      · obtain ⟨q,hq,he⟩:=ih hw;exact ⟨q,List.mem_cons_of_mem p hq,he⟩
    · obtain ⟨q,hq,he⟩:=ih (by simpa only [Inner.portWords,h,ite_false] using hw)
      exact ⟨q,List.mem_cons_of_mem p hq,he⟩
/-- Whole packet-major left-scope filter visits only actual emitted children. -/
theorem scope_count (buckets:List B.Bucket) (target:List Bool):
    (B.portWords buckets target).length≤(buckets.flatMap (fun b=>b.children)).length:=by
  induction buckets with
  | nil=>exact le_rfl
  | cons b bs ih=>
    have hh:=inner_count b.children target
    simp only [B.portWords,List.length_append,List.flatMap_cons] at ih ⊢
    omega
/-- Exact physical global-ID lineage through all numeric-vertex filters. -/
theorem scope_word (buckets:List B.Bucket) (target word:List Bool)
    (hw:word∈B.portWords buckets target):∃p∈buckets.flatMap (fun b=>b.children),p.2=word:=by
  induction buckets with
  | nil=>simp only [B.portWords,List.not_mem_nil] at hw
  | cons b bs ih=>
    simp only [B.portWords,List.mem_append] at hw
    rcases hw with hw|hw
    · obtain ⟨p,hp,he⟩:=inner_word b.children target word hw
      exact ⟨p,by simp only [List.flatMap_cons,List.mem_append];exact Or.inl hp,he⟩
    · obtain ⟨p,hp,he⟩:=ih hw
      exact ⟨p,by simp only [List.flatMap_cons,List.mem_append];exact Or.inr hp,he⟩
/-- Actual converted left-scope bytes are paid by actual child count and derived global-ID values. -/
theorem scope_unary_length (buckets:List B.Bucket) (target:List Bool) (cap:Nat)
    (hv:∀p∈buckets.flatMap (fun b=>b.children),bitValue p.2≤cap):
    (O.result (B.portWords buckets target)).length≤
      (buckets.flatMap (fun b=>b.children)).length*(2*cap+2)+1:=by
  have h:=SemiprimeD1StackChildGroupFactoryUnaryScopeBounds.unary_length (B.portWords buckets target) cap (by
    intro w hw;obtain ⟨p,hp,rfl⟩:=scope_word buckets target w hw;exact hv p hp)
  have hc:=scope_count buckets target
  nlinarith
/-- Actual converted original-port order bytes are paid by the original list and actual child count. -/
theorem order_unary_length (buckets:List B.Bucket) (points:List P.Point) (target:List Bool):
    (O.result (Old.orderWords buckets points target)).length≤
      points.length*(2*(buckets.flatMap (fun b=>b.children)).length+2)+1:=by
  have h:=SemiprimeD1StackChildGroupFactoryUnaryScopeBounds.unary_length (Old.orderWords buckets points target)
    ((buckets.flatMap (fun b=>b.children)).length)
    (fun w hw=>(SemiprimeD1StackChildGroupFactoryOrderBounds.order_word_bounds buckets points target w hw).2)
  have hc:=SemiprimeD1StackChildGroupFactoryOrderBounds.order_count buckets points target
  nlinarith
/-- Per-vertex actual scope/order row allowance is uniformly quartic, even with duplicate packet vectors. -/
theorem generated_rows_quartic (packets:List (List Bool)) (es:List E.Endpoint) (points:List P.Point)
    (target:List Bool) (S:Nat) (hk:packets.length≤S) (he:es.length≤S) (hp:points.length≤S):
    (SemiprimeD1StackChildGroupFactoryWordLog.row (O.result (B.portWords (Code.buckets packets es []) target))).length+
      (SemiprimeD1StackChildGroupFactoryWordLog.row (O.result (Old.orderWords (Code.buckets packets es []) points target))).length+2≤
        100*(S+1)^4:=by
  have hscope:=scope_unary_length (Code.buckets packets es []) target (packets.length*es.length)
    (SemiprimeD1StackChildGroupFactoryCounterBounds.generated_value packets es)
  have horder:=order_unary_length (Code.buckets packets es []) points target
  have hc:=SemiprimeD1StackChildGroupFactoryCounterBounds.catalogue_count packets es []
  have hm:packets.length*es.length≤S*S:=Nat.mul_le_mul hk he
  have hs:(S*S)^2≤(S+1)^4:=by nlinarith
  have hc2:((Code.buckets packets es []).flatMap (fun b=>b.children)).length≤S*S:=hc.trans hm
  have hscope':(O.result (B.portWords (Code.buckets packets es []) target)).length≤(S*S)*(2*(S*S)+2)+1:=by
    nlinarith
  have horder':(O.result (Old.orderWords (Code.buckets packets es []) points target)).length≤S*(2*(S*S)+2)+1:=by
    nlinarith
  simp only [SemiprimeD1StackChildGroupFactoryWordLog.row,List.length_cons,
    SemiprimeSourceHistogramKeyBits.frame_length,List.length_nil]
  nlinarith
end RiemannGaussian.SemiprimeD1StackChildGroupFactoryRowByteBounds
