/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackChildGroupFactoryNativeBuckets
import RiemannGaussian.SemiprimeD1StackChildGroupFactoryCanonicalPorts
/-! # Exact canonical original child scopes from the real generated ID filter
The source filters the actual packet-major child stream and converts its actual
binary global IDs. Its unary scope is exactly the native canonical left ports;
no port list/permutation or equal original/generated ID namespace is assumed.
-/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackChildGroupFactoryNativeScopes
open SemiprimeD1StackChildGroupFactory (Inputs)
open SemiprimeBitArithmetic (bitValue)
namespace I
export SemiprimeD1StackChildGroupFactoryLeftPortsInner (Child portWords)
end I
namespace B
export SemiprimeD1StackChildGroupFactoryLeftPortsLoop (Bucket portWords)
end B
namespace E
export SemiprimeD1StackChildGroupFactoryBucketParse (Endpoint)
end E
namespace Code
export SemiprimeD1StackChildGroupFactoryCatalogueCodecs (buckets)
end Code
namespace N
export SemiprimeD1StackChildGroupFactoryNativeEndpoints (encode)
export SemiprimeD1StackChildGroupFactoryNativeBuckets (numbering_original)
end N
namespace Fld
export SemiprimeD1StackChildGroupFactoryNativeFields (source fields)
end Fld
namespace Act
export SemiprimeD1StackChildGroupFactoryNativeActivation (originalIDs)
end Act
namespace Forward
export SemiprimeD1StackChildGroupFactoryForwardBucketsSource (endpoints)
end Forward
/-- Actual inner numeric filtering retains exactly the same generated global-ID values. -/
theorem inner_values (children:List I.Child) (target:List Bool):
    (I.portWords children target).map bitValue=
      (((children.map (fun p=>(p.1,bitValue p.2))).filter
        (fun p=>decide (bitValue p.1.vertex=bitValue target))).map Prod.snd):=by
  induction children with
  | nil=>rfl
  | cons p ps ih=>
    by_cases h:bitValue p.1.vertex=bitValue target <;>
      simp only [I.portWords,h,ite_true,ite_false,List.map_cons,List.filter_cons,
        decide_true,decide_false,Bool.false_eq_true,ih]
/-- Actual outer filtering preserves every real packet-major ordinal and multiplicity. -/
theorem scope_values (buckets:List B.Bucket) (target:List Bool):
    (B.portWords buckets target).map bitValue=
      ((((buckets.flatMap (fun b=>b.children)).map (fun p=>(p.1,bitValue p.2))).filter
        (fun p=>decide (bitValue p.1.vertex=bitValue target))).map Prod.snd):=by
  induction buckets with
  | nil=>rfl
  | cons b bs ih=>
    simp only [B.portWords,List.flatMap_cons,List.map_append,List.filter_append,inner_values,ih]
/-- Per-vertex actual generated values are the EXACT native child canonical port list. -/
theorem values_original (i:Inputs) (n F a:Nat) (arity:Fin F→Nat)
    (owner:((e:Fin F)×Fin (arity e))→Fin n) (q:Fin a) (g:Fin 64)
    (hg:bitValue i.group=g.val) (v:Fin (n+F)) (target:List Bool) (ht:bitValue target=v.val):
    (B.portWords (Code.buckets (Fld.source n F a arity owner).state.packets
      (Forward.endpoints i a q.val (Act.originalIDs n F a arity owner) (Fld.fields n F a arity owner)) []) target).map bitValue=
      SemiprimeD1TensorNetwork.leftPorts (SemiprimeD1TensorNetworkLayout.childRows
        (SemiprimeD1ChildGraph.acquire n F 64 a arity owner q g)) v:=by
  rw [scope_values,N.numbering_original i n F a arity owner q g hg,
    SemiprimeD1StackChildGroupFactoryCanonicalPorts.leftPorts_zipIdx]
  change _=((((SemiprimeD1ChildGraph.acquire n F 64 a arity owner q g).factors.map
      (List.map SemiprimeD1ChildGraph.Endpoint.vertex)).flatten.zipIdx).filter
        (fun p=>decide (p.1=v))).map Prod.snd
  rw [←List.map_flatten,List.zipIdx_map,List.zipIdx_map]
  simp only [List.filter_map,List.map_map,Function.comp_def,Prod.map,id_eq,N.encode,
    SemiprimeSourceHistogramHeadRefinement.numberKey_value,ht,Fin.ext_iff]
/-- Exact old unary portTape bytes come from the REAL numeric-bank-to-unary converter. -/
theorem unary_original (i:Inputs) (n F a:Nat) (arity:Fin F→Nat)
    (owner:((e:Fin F)×Fin (arity e))→Fin n) (q:Fin a) (g:Fin 64)
    (hg:bitValue i.group=g.val) (v:Fin (n+F)) (target:List Bool) (ht:bitValue target=v.val):
    SemiprimeD1StackPortOrdinalStream.result
      (B.portWords (Code.buckets (Fld.source n F a arity owner).state.packets
        (Forward.endpoints i a q.val (Act.originalIDs n F a arity owner) (Fld.fields n F a arity owner)) []) target)=
      SemiprimeD1TensorTapeCodec.vectorBits ((SemiprimeD1TensorNetwork.leftPorts
        (SemiprimeD1TensorNetworkLayout.childRows (SemiprimeD1ChildGraph.acquire n F 64 a arity owner q g)) v).map
          (fun id=>List.replicate id true)):=by
  dsimp only [SemiprimeD1StackPortOrdinalStream.result]
  apply congrArg SemiprimeD1TensorTapeCodec.vectorBits
  have h:=congrArg (List.map (fun id=>List.replicate id true))
    (values_original i n F a arity owner q g hg v target ht)
  simpa only [List.map_map,Function.comp_def] using h
end RiemannGaussian.SemiprimeD1StackChildGroupFactoryNativeScopes
