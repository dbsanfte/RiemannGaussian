/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackChildGroupFactoryNativeScopes
import RiemannGaussian.SemiprimeD1StackChildGroupFactoryNativeTagResolution
/-! # Exact native per-vertex tag order read by the actual first-index source
The actual raw edge/side stream has the same order and byte identity as the
native resolved tag stream. This proves lookup positions, including EOF misses,
without a supplied permutation, tag map, or equality/count answer.
-/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackChildGroupFactoryNativeTagOrder
open SemiprimeD1StackChildGroupFactory (Inputs)
open SemiprimeBitArithmetic (bitValue)
namespace I
export SemiprimeD1StackChildGroupFactoryLeftPortsInner (Child)
end I
namespace B
export SemiprimeD1StackChildGroupFactoryLeftPortsLoop (Bucket)
end B
namespace M
export SemiprimeD1StackChildGroupFactoryTagIndexMeaning (tags allTags outer_value)
end M
namespace Tag
export SemiprimeD1StackChildGroupFactoryTagVisit (candidate)
end Tag
namespace N
export SemiprimeD1StackChildGroupFactoryNativeEndpoints (encode)
export SemiprimeD1StackChildGroupFactoryNativeBuckets (numbering_original)
export SemiprimeD1StackChildGroupFactoryNativeTagResolution (tags_with_vertices idxOf_map)
end N
namespace Raw
export SemiprimeD1StackChildGroupFactoryNativeTags (rawTag rawTag_injective)
end Raw
namespace Native
export SemiprimeD1ChildAssignmentEquiv (tags acquired Tag)
end Native
namespace Fld
export SemiprimeD1StackChildGroupFactoryNativeFields (source fields)
end Fld
namespace Act
export SemiprimeD1StackChildGroupFactoryNativeActivation (originalIDs)
end Act
namespace Forward
export SemiprimeD1StackChildGroupFactoryForwardBucketsSource (endpoints)
end Forward
namespace Code
export SemiprimeD1StackChildGroupFactoryCatalogueCodecs (buckets)
end Code
/-- Actual inner tag bytes are read from precisely the matching original raw endpoints. -/
theorem inner_tags (children:List I.Child) (target:List Bool):M.tags children target=
    (((children.map Prod.fst).filter (fun e=>decide (bitValue e.vertex=bitValue target))).map Tag.candidate):=by
  induction children with
  | nil=>rfl
  | cons p ps ih=>
    by_cases h:bitValue p.1.vertex=bitValue target <;>
      simp only [M.tags,List.map_cons,List.filter_cons,h,ite_true,ite_false,decide_true,decide_false,
        Bool.false_eq_true,ih]
/-- Complete actual packet-major tag bytes retain exact vertex-filtered endpoint order. -/
theorem all_tags_fields (buckets:List B.Bucket) (target:List Bool):M.allTags buckets target=
    ((((buckets.flatMap (fun b=>b.children)).map Prod.fst).filter
      (fun e=>decide (bitValue e.vertex=bitValue target))).map Tag.candidate):=by
  induction buckets with
  | nil=>rfl
  | cons b bs ih=>
    change M.tags b.children target++M.allTags bs target=_
    rw [inner_tags,ih]
    simp only [List.flatMap_cons,List.map_append,List.filter_append]
/-- Actual complete computed bucket view; only proof notation, not an additional runtime input. -/
abbrev buckets (i:Inputs) (n F a:Nat) (arity:Fin F→Nat) (owner:((e:Fin F)×Fin (arity e))→Fin n)
    (q:Fin a):List B.Bucket:=Code.buckets (Fld.source n F a arity owner).state.packets
      (Forward.endpoints i a q.val (Act.originalIDs n F a arity owner) (Fld.fields n F a arity owner)) []
/-- The actual query's WHOLE raw-tag stream is exactly the encoded acquired native local tag order. -/
theorem all_tags_original (i:Inputs) (n F a:Nat) (arity:Fin F→Nat)
    (owner:((e:Fin F)×Fin (arity e))→Fin n) (q:Fin a) (g:Fin 64)
    (hg:bitValue i.group=g.val) (v:Fin (n+F)) (target:List Bool) (ht:bitValue target=v.val):
    M.allTags (buckets i n F a arity owner q) target=
      (SemiprimeD1ChildTableOrder.acquire owner (Native.acquired n F 64 a arity owner q g) v).child.map
        (Raw.rawTag n F a arity owner):=by
  have hn:=congrArg (List.map Prod.fst) (N.numbering_original i n F a arity owner q g hg)
  have hfields:((buckets i n F a arity owner q).flatMap (fun b=>b.children)).map Prod.fst=
      (SemiprimeD1ChildGraph.acquire n F 64 a arity owner q g).factors.flatten.map N.encode:=by
    simpa only [List.map_map,Function.comp_def,List.zipIdx_map_fst] using hn
  have htags:=congrArg (fun xs:List (Fin (n+F)×List Bool)=>
      (xs.filter (fun p=>decide (p.1=v))).map Prod.snd) (N.tags_with_vertices n F a arity owner q g)
  simp only [List.filter_map,List.map_map,Function.comp_def] at htags
  rw [all_tags_fields,hfields]
  change _=((Native.tags n F 64 a arity owner q g).filter
    (fun t=>decide (SemiprimeD1ChildPortBijection.linkVertex owner t=v))).map (Raw.rawTag n F a arity owner)
  rw [htags]
  simp only [List.filter_map,List.map_map,Function.comp_def,N.encode,Tag.candidate,
    SemiprimeD1StackChildGroupFactoryTagBuild.rawTag,SemiprimeSourceHistogramHeadRefinement.numberKey_value,ht,Fin.ext_iff]
  rfl
/-- Exact actual binary first-index result equals native child.idxOf for EVERY original typed tag. -/
theorem query_value_original (i:Inputs) (n F a:Nat) (arity:Fin F→Nat)
    (owner:((e:Fin F)×Fin (arity e))→Fin n) (q:Fin a) (g:Fin 64)
    (hg:bitValue i.group=g.val) (v:Fin (n+F)) (target:List Bool) (ht:bitValue target=v.val)
    (tag:Native.Tag arity):
    bitValue (SemiprimeD1StackChildGroupFactoryTagLoopView.finalPosition (buckets i n F a arity owner q) target
      (Raw.rawTag n F a arity owner tag) [])=
      (SemiprimeD1ChildTableOrder.acquire owner (Native.acquired n F 64 a arity owner q g) v).child.idxOf tag:=by
  rw [M.outer_value,SemiprimeBitArithmetic.bitValue,Nat.zero_add,
    all_tags_original i n F a arity owner q g hg v target ht]
  exact N.idxOf_map _ (Raw.rawTag_injective n F a arity owner q g) _ _
end RiemannGaussian.SemiprimeD1StackChildGroupFactoryNativeTagOrder
