/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackChildGroupFactoryNativeTagOrder
/-! # Exact original old-port order stream and actual unary order bytes
Every original endpoint appears in original factor-major/owner-before-factor
order, regardless of activation. Real first-index values become the exact old
unary order tape for every vertex, including empty, isolated and inactive ones.
-/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackChildGroupFactoryNativeOrders
open SemiprimeD1StackChildGroupFactory (Inputs)
open SemiprimeBitArithmetic (bitValue)
namespace Raw
export SemiprimeD1StackChildGroupFactoryNativeTags (edgeFor rawTag edgeFor_pair)
end Raw
namespace Native
export SemiprimeD1ChildAssignmentEquiv (Tag acquired)
export SemiprimeD1ChildPortBijection (linkVertex typed_full)
end Native
namespace Pair
export SemiprimeD1StackChildGroupFactoryNativePairs (paired fieldOf fields_typed)
end Pair
namespace Fld
export SemiprimeD1StackChildGroupFactoryNativeFields (fields source ofPair)
end Fld
namespace Act
export SemiprimeD1StackChildGroupFactoryNativeActivation (originalIDs)
end Act
namespace Forward
export SemiprimeD1StackChildGroupFactoryForwardSource (rows activation)
end Forward
namespace Code
export SemiprimeD1StackChildGroupFactoryCatalogueCodecs (oldPoints)
end Code
namespace Keys
export SemiprimeD1StackChildGroupFactoryEndpointKeys (row)
end Keys
namespace P
export SemiprimeD1StackChildGroupFactoryOldPortParse (Point)
end P
namespace Old
export SemiprimeD1StackChildGroupFactoryOldPortsLoop (orderWords)
export SemiprimeD1StackChildGroupFactoryOldPortOneView (answerWord)
end Old
namespace Query
export SemiprimeD1StackChildGroupFactoryNativeTagOrder (buckets query_value_original)
end Query
/-- Exact three physical original-endpoint fields, in the original typed namespace. -/
def pointOf (n F a:Nat) (arity:Fin F→Nat) (owner:((e:Fin F)×Fin (arity e))→Fin n)
    (tag:Native.Tag arity):P.Point:=
  ⟨SemiprimeSourceHistogramHeadRefinement.numberKey (Native.linkVertex owner tag).val,
    Raw.edgeFor n F a arity owner tag.1,[tag.2]⟩
/-- Actual old-point parser bytes of one real pair have exactly its two native typed endpoint codes. -/
theorem pair_points (i:Inputs) (n F a:Nat) (arity:Fin F→Nat)
    (owner:((e:Fin F)×Fin (arity e))→Fin n) (coordinate:Nat)
    (p:((e:Fin F)×Fin (arity e))×SemiprimeD1PacketInventory.Placement)
    (hp:p∈Pair.paired n F a arity owner):
    Code.oldPoints [Keys.row i coordinate (Forward.activation a (Act.originalIDs n F a arity owner)) (Pair.fieldOf owner p)]=
      [(pointOf n F a arity owner (p.1,true)),(pointOf n F a arity owner (p.1,false))]:=by
  have he:=Raw.edgeFor_pair n F a arity owner p hp
  simp only [Code.oldPoints,List.flatMap_cons,List.flatMap_nil,List.append_nil,Keys.row,Pair.fieldOf,Fld.ofPair,
    pointOf,Native.linkVertex,ite_true,Bool.false_eq_true,ite_false,he]
/-- ENTIRE original old-point list, with exact incidence/side multiplicities and empty-factor gaps. -/
theorem points_original (i:Inputs) (n F a:Nat) (arity:Fin F→Nat)
    (owner:((e:Fin F)×Fin (arity e))→Fin n) (coordinate:Nat):
    Code.oldPoints (Forward.rows i a coordinate (Act.originalIDs n F a arity owner) (Fld.fields n F a arity owner))=
      ((SemiprimeD1CollisionOriginal.ports n F a arity).product [true,false]).map (pointOf n F a arity owner):=by
  rw [Forward.rows,Pair.fields_typed]
  have hl:=congrArg List.length (SemiprimeD1PacketReplayOriginal.sources n F 64 a arity owner)
  rw [List.length_map,SemiprimeD1IncidenceAcquisition.keys_original,List.length_map] at hl
  have hm:(Pair.paired n F a arity owner).map Prod.fst=SemiprimeD1CollisionOriginal.ports n F a arity:=
    List.map_fst_zip hl.symm.le
  rw [←hm,←Native.typed_full,List.map_flatMap]
  unfold Code.oldPoints
  rw [List.map_map,List.flatMap_map]
  apply List.flatMap_congr
  intro p hp
  exact pair_points i n F a arity owner coordinate p hp
/-- Numeric comparison of actual encoded old vertex keys is the exact original typed vertex predicate. -/
theorem point_vertex (n F a:Nat) (arity:Fin F→Nat) (owner:((e:Fin F)×Fin (arity e))→Fin n)
    (tag:Native.Tag arity) (v:Fin (n+F)) (target:List Bool) (ht:bitValue target=v.val):
    bitValue (pointOf n F a arity owner tag).vertex=bitValue target ↔Native.linkVertex owner tag=v:=by
  simp only [pointOf,SemiprimeSourceHistogramHeadRefinement.numberKey_value,ht,Fin.ext_iff]
/-- Actual answer value for any original tag is its exact native first index, including absence. -/
theorem answer_value (i:Inputs) (n F a:Nat) (arity:Fin F→Nat)
    (owner:((e:Fin F)×Fin (arity e))→Fin n) (q:Fin a) (g:Fin 64)
    (hg:bitValue i.group=g.val) (v:Fin (n+F)) (target:List Bool) (ht:bitValue target=v.val)
    (tag:Native.Tag arity):
    bitValue (Old.answerWord (Query.buckets i n F a arity owner q) (pointOf n F a arity owner tag) target)=
      (SemiprimeD1ChildTableOrder.acquire owner (Native.acquired n F 64 a arity owner q g) v).child.idxOf tag:=by
  exact Query.query_value_original i n F a arity owner q g hg v target ht tag
/-- Actual original-port filter/query visits compute the native order values in exactly their original order. -/
theorem values_from_tags (i:Inputs) (n F a:Nat) (arity:Fin F→Nat)
    (owner:((e:Fin F)×Fin (arity e))→Fin n) (q:Fin a) (g:Fin 64)
    (hg:bitValue i.group=g.val) (v:Fin (n+F)) (target:List Bool) (ht:bitValue target=v.val)
    (tags:List (Native.Tag arity)):
    (Old.orderWords (Query.buckets i n F a arity owner q) (tags.map (pointOf n F a arity owner)) target).map bitValue=
      (tags.filter (fun t=>decide (Native.linkVertex owner t=v))).map
        (fun t=>(SemiprimeD1ChildTableOrder.acquire owner (Native.acquired n F 64 a arity owner q g) v).child.idxOf t):=by
  induction tags with
  | nil=>rfl
  | cons tag tags ih=>
    have hv:=point_vertex n F a arity owner tag v target ht
    have ha:=answer_value i n F a arity owner q g hg v target ht tag
    by_cases h:Native.linkVertex owner tag=v
    · have hp:=hv.mpr h
      simp only [List.map_cons,Old.orderWords,hp,ite_true,List.filter_cons,h,decide_true,ha,ih]
    · have hp:¬bitValue (pointOf n F a arity owner tag).vertex=bitValue target:=fun he=>h (hv.mp he)
      simp only [List.map_cons,Old.orderWords,hp,ite_false,List.filter_cons,h,decide_false,Bool.false_eq_true,ih]
/-- Complete real order-word values equal the ENTIRE native old-port index list for every old vertex. -/
theorem values_original (i:Inputs) (n F a:Nat) (arity:Fin F→Nat)
    (owner:((e:Fin F)×Fin (arity e))→Fin n) (q:Fin a) (g:Fin 64)
    (hg:bitValue i.group=g.val) (v:Fin (n+F)) (target:List Bool) (ht:bitValue target=v.val):
    (Old.orderWords (Query.buckets i n F a arity owner q)
      (Code.oldPoints (Forward.rows i a q.val (Act.originalIDs n F a arity owner) (Fld.fields n F a arity owner))) target).map bitValue=
      (SemiprimeD1ChildTableOrder.acquire owner (Native.acquired n F 64 a arity owner q g) v).order:=by
  rw [points_original]
  exact values_from_tags i n F a arity owner q g hg v target ht _
/-- The REAL ordinal converter outputs EXACT native unary old-order bytes, with no canonical-word assumption. -/
theorem unary_original (i:Inputs) (n F a:Nat) (arity:Fin F→Nat)
    (owner:((e:Fin F)×Fin (arity e))→Fin n) (q:Fin a) (g:Fin 64)
    (hg:bitValue i.group=g.val) (v:Fin (n+F)) (target:List Bool) (ht:bitValue target=v.val):
    SemiprimeD1StackPortOrdinalStream.result (Old.orderWords (Query.buckets i n F a arity owner q)
      (Code.oldPoints (Forward.rows i a q.val (Act.originalIDs n F a arity owner) (Fld.fields n F a arity owner))) target)=
      SemiprimeD1TensorTapeCodec.vectorBits
        (((SemiprimeD1ChildTableOrder.acquire owner (Native.acquired n F 64 a arity owner q g) v).order).map
          (fun id=>List.replicate id true)):=by
  dsimp only [SemiprimeD1StackPortOrdinalStream.result]
  apply congrArg SemiprimeD1TensorTapeCodec.vectorBits
  have h:=congrArg (List.map (fun id=>List.replicate id true))
    (values_original i n F a arity owner q g hg v target ht)
  simpa only [List.map_map,Function.comp_def] using h
end RiemannGaussian.SemiprimeD1StackChildGroupFactoryNativeOrders
