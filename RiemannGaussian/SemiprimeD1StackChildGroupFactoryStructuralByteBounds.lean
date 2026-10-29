/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackChildGroupFactoryTagSearchBounds
import RiemannGaussian.SemiprimeD1StackChildGroupFactoryOldPortParse
/-! # Raw field lengths from the actual retained nested record tapes
These are byte-layout inequalities for actual parsed records. They introduce no
new input, decoded-field supplier, or clock. In particular each field is paid by
the literal retained tape, even for repeated packets and padded numeric words.
-/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackChildGroupFactoryStructuralByteBounds
namespace B
export SemiprimeD1StackChildGroupFactoryLeftPortsLoop (Bucket payload records)
end B
namespace I
export SemiprimeD1StackChildGroupFactoryLeftPortsInner (Child records)
end I
namespace P
export SemiprimeD1StackChildGroupFactoryOldPortParse (Point payload records)
end P
namespace Op
export SemiprimeD1StackChildGroupFactoryOperationBounds (endpointBytes)
end Op
/-- Every actual six-field child's fields are bounded by its enclosing child tape. -/
theorem child_fields (children:List I.Child) (p:I.Child) (hp:p∈children):
    Op.endpointBytes p.1+p.2.length≤(I.records children).length:=by
  induction children with
  | nil=>simp only [List.not_mem_nil] at hp
  | cons q qs ih=>
    simp only [List.mem_cons] at hp
    rcases hp with rfl|hp
    · simp only [I.records,List.length_cons,SemiprimeSourceHistogramKeyBits.frame_length,
        SemiprimeD1StackChildGroupFactoryBucketEmit.payload,List.length_nil,Op.endpointBytes]
      omega
    · have h:=ih hp
      simp only [I.records,List.length_cons,SemiprimeSourceHistogramKeyBits.frame_length]
      omega
/-- Every real bucket's three physical fields are paid by the retained bucket tape. -/
theorem bucket_fields (buckets:List B.Bucket) (b:B.Bucket) (hb:b∈buckets):
    b.packet.length+(I.records b.children).length+b.ports.length+1≤(B.records buckets).length:=by
  induction buckets with
  | nil=>simp only [List.not_mem_nil] at hb
  | cons q qs ih=>
    simp only [List.mem_cons] at hb
    rcases hb with rfl|hb
    · simp only [B.records,B.payload,SemiprimeD1StackChildGroupFactoryBucketRecord.payload,
        List.length_cons,SemiprimeSourceHistogramKeyBits.frame_length,List.length_nil]
      omega
    · have h:=ih hb
      simp only [B.records,List.length_cons,SemiprimeSourceHistogramKeyBits.frame_length]
      omega
/-- Any actual packet-major child is bounded by the complete retained bucket tape. -/
theorem flattened_child_fields (buckets:List B.Bucket) (p:I.Child)
    (hp:p∈buckets.flatMap (fun b=>b.children)):
    Op.endpointBytes p.1+p.2.length≤(B.records buckets).length:=by
  obtain ⟨b,hb,hp⟩:=List.mem_flatMap.mp hp
  have hc:=child_fields b.children p hp
  have hh:=bucket_fields buckets b hb
  omega
/-- Every original endpoint's actual raw fields are paid by its enclosing tape. -/
theorem point_fields (points:List P.Point) (p:P.Point) (hp:p∈points):
    p.vertex.length+p.edge.length+p.side.length+1≤(P.records points).length:=by
  induction points with
  | nil=>simp only [List.not_mem_nil] at hp
  | cons q qs ih=>
    simp only [List.mem_cons] at hp
    rcases hp with rfl|hp
    · simp only [P.records,P.payload,List.length_cons,SemiprimeSourceHistogramKeyBits.frame_length,List.length_nil]
      omega
    · have h:=ih hp
      simp only [P.records,List.length_cons,SemiprimeSourceHistogramKeyBits.frame_length]
      omega
end RiemannGaussian.SemiprimeD1StackChildGroupFactoryStructuralByteBounds
