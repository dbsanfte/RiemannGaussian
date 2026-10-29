/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackChildGroupFactoryNativeEndpoints
import RiemannGaussian.SemiprimeD1StackChildGroupFactoryCatalogueNumbers
/-! # Exact original child buckets and their physically generated global numbering
Observed packet order, empty buckets and repeated raw packet distinctions are
preserved. Actual binary IDs name the real packet-major endpoint ordinal; no
original occurrence IDs are identified with this separate generated namespace.
-/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackChildGroupFactoryNativeBuckets
open SemiprimeD1StackChildGroupFactory (Inputs)
namespace Code
export SemiprimeD1StackChildGroupFactoryCatalogueCodecs (buckets)
end Code
namespace Num
export SemiprimeD1StackChildGroupFactoryCatalogueNumbers (filtered ordered selected_numbered catalogue_zero)
end Num
namespace Scan
export SemiprimeD1StackChildGroupFactoryBucketLoopView (selected)
end Scan
namespace E
export SemiprimeD1StackChildGroupFactoryBucketParse (Endpoint)
end E
namespace N
export SemiprimeD1StackChildGroupFactoryNativeEndpoints (encode endpoints_original)
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
/-- Actual physical numbering never changes any original endpoint byte. -/
theorem selected_fields (es:List E.Endpoint) (packet position:List Bool):
    (Scan.selected es packet position).map Prod.fst=Num.filtered es packet:=by
  have h:=congrArg (List.map Prod.fst) (Num.selected_numbered es packet position)
  simpa only [List.map_map,List.zipIdx_map_fst,Function.comp_def] using h
/-- Every real chronological bucket retains precisely its literal packet-filtered endpoint stream. -/
theorem bucket_fields (packets:List (List Bool)) (es:List E.Endpoint) (position:List Bool):
    (Code.buckets packets es position).map (fun b=>b.children.map Prod.fst)=packets.map (Num.filtered es):=by
  induction packets generalizing position with
  | nil=>rfl
  | cons p ps ih=>simp only [Code.buckets,List.map_cons,selected_fields,ih]
/-- Literal whole packet bytes commute with typed endpoint encoding, with no normalization. -/
theorem filtered_encoded {V:Nat} (es:List (SemiprimeD1ChildGraph.Endpoint V)) (packet:List Bool):
    Num.filtered (es.map N.encode) packet=(es.filter (fun e=>decide (e.packet=packet))).map N.encode:=by
  simp only [Num.filtered,List.filter_map,Function.comp_def,N.encode]
  rfl
/-- Every acquired bucket has exactly the original native factor's endpoint bytes, including empty factors. -/
theorem factors_original (i:Inputs) (n F a:Nat) (arity:Fin F→Nat)
    (owner:((e:Fin F)×Fin (arity e))→Fin n) (q:Fin a) (g:Fin 64)
    (hg:SemiprimeBitArithmetic.bitValue i.group=g.val):
    (Code.buckets (Fld.source n F a arity owner).state.packets
      (Forward.endpoints i a q.val (Act.originalIDs n F a arity owner) (Fld.fields n F a arity owner)) []).map
        (fun b=>b.children.map Prod.fst)=
      (SemiprimeD1ChildGraph.acquire n F 64 a arity owner q g).factors.map (List.map N.encode):=by
  rw [bucket_fields,N.endpoints_original i n F a arity owner q g hg]
  change _=(SemiprimeD1ChildGraph.buckets
    (SemiprimeD1ChildGraph.acquire n F 64 a arity owner q g).endpoints
    (Fld.source n F a arity owner).state.packets).value.map (List.map N.encode)
  rw [SemiprimeD1ChildGraphSemantics.buckets_value,List.map_map]
  apply List.map_congr_left
  intro packet _
  exact filtered_encoded _ _
/-- Flattening the actual physical bucket view does not discard any counted child. -/
theorem flattened_fields (packets:List (List Bool)) (es:List E.Endpoint) (position:List Bool):
    ((Code.buckets packets es position).flatMap (fun b=>b.children)).map Prod.fst=Num.ordered packets es:=by
  have h:=congrArg List.flatten (bucket_fields packets es position)
  simpa only [←List.flatMap_def,List.map_flatMap,Num.ordered] using h
/-- All actual binary global IDs are exactly the zero-based ORIGINAL child-graph incidence order. -/
theorem numbering_original (i:Inputs) (n F a:Nat) (arity:Fin F→Nat)
    (owner:((e:Fin F)×Fin (arity e))→Fin n) (q:Fin a) (g:Fin 64)
    (hg:SemiprimeBitArithmetic.bitValue i.group=g.val):
    ((Code.buckets (Fld.source n F a arity owner).state.packets
      (Forward.endpoints i a q.val (Act.originalIDs n F a arity owner) (Fld.fields n F a arity owner)) []).flatMap
        (fun b=>b.children)).map (fun p=>(p.1,SemiprimeBitArithmetic.bitValue p.2))=
      ((SemiprimeD1ChildGraph.acquire n F 64 a arity owner q g).factors.flatten.map N.encode).zipIdx:=by
  have h:=congrArg List.flatten (factors_original i n F a arity owner q g hg)
  simp only [←List.flatMap_def,←List.map_flatMap] at h
  rw [flattened_fields] at h
  rw [Num.catalogue_zero,h]
  congr 1
  rw [←List.flatMap_id,List.map_flatMap]
  rfl
end RiemannGaussian.SemiprimeD1StackChildGroupFactoryNativeBuckets
