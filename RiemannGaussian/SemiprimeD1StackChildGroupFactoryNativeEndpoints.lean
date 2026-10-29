/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackChildGroupFactoryNativePairs
/-! # Actual complete forward endpoint catalogue is exactly the original child graph
The source emits owner BEFORE factor at each real original incidence, selecting
both/one/neither from actual computed colour flags. All raw packet/slot/edge
bytes and all original repeated incidences retain their exact order.
-/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackChildGroupFactoryNativeEndpoints
open SemiprimeD1StackChildGroupFactory (Inputs)
namespace Fld
export SemiprimeD1StackChildGroupFactoryNativeFields (source fields)
end Fld
namespace Pair
export SemiprimeD1StackChildGroupFactoryNativePairs (paired fieldOf fields_typed source_aligned owner_flag factor_flag)
end Pair
namespace Act
export SemiprimeD1StackChildGroupFactoryNativeActivation (originalIDs)
end Act
namespace Forward
export SemiprimeD1StackChildGroupFactoryForwardSource (activation rows)
export SemiprimeD1StackChildGroupFactoryForwardBucketsSource (endpoints)
end Forward
namespace Keys
export SemiprimeD1StackChildGroupFactoryEndpointKeys (row)
end Keys
namespace Code
export SemiprimeD1StackChildGroupFactoryCatalogueCodecs (selected side)
end Code
namespace E
export SemiprimeD1StackChildGroupFactoryBucketParse (Endpoint)
end E
namespace Native
export SemiprimeD1ChildGraph (Endpoint one acquire scan)
end Native
/-- Exact five-field encoding of an original typed endpoint; only its bounded vertex key is compact. -/
def encode {V:Nat} (e:Native.Endpoint V):E.Endpoint:=
  ⟨SemiprimeSourceHistogramHeadRefinement.numberKey e.vertex.val,e.packet,e.slot,e.edge,[e.side]⟩
/-- The real selected endpoint stream is the ordered concatenation of each actual two-sided visit. -/
theorem selected_flatMap (rows:List SemiprimeD1StackChildGroupFactoryEndpointLoop.Row):
    Code.selected rows=rows.flatMap (fun r=>Code.selected [r]):=by
  induction rows with
  | nil=>rfl
  | cons r rs ih=>
    simp only [Code.selected,List.flatMap_cons,ih,List.append_nil,List.append_assoc]
/-- One actual parsed occurrence emits exactly the original native two-sided endpoint bytes. -/
theorem one_original (i:Inputs) (n F a:Nat) (arity:Fin F→Nat)
    (owner:((e:Fin F)×Fin (arity e))→Fin n) (q:Fin a) (g:Fin 64)
    (hg:SemiprimeBitArithmetic.bitValue i.group=g.val)
    (p:((e:Fin F)×Fin (arity e))×SemiprimeD1PacketInventory.Placement)
    (hp:p∈Pair.paired n F a arity owner):
    Code.selected [Keys.row i q.val (Forward.activation a (Act.originalIDs n F a arity owner)) (Pair.fieldOf owner p)]=
      (Native.one owner (Fld.source n F a arity owner).padding.source.selection.cache.rows.source.dictionary
        a q.val (SemiprimeSourceHistogramPortKeys.encodeKey g.val).bits p.1 p.2).value.map encode:=by
  have hs:=Pair.source_aligned n F a arity owner p hp
  have ho:=Pair.owner_flag i n F a arity owner q g hg p
  have hf:=Pair.factor_flag i n F a arity owner q g hg p
  have hnative:=SemiprimeD1ChildGraphSemantics.one_original n F 64 a arity owner q g p.1 p.2 hs
  change Code.selected [_]=(Native.one owner
    (SemiprimeD1IncidenceAcquisition.acquire n F 64 a arity owner).selection.cache.rows.source.dictionary
      a q.val (SemiprimeSourceHistogramPortKeys.encodeKey g.val).bits p.1 p.2).value.map encode
  rw [hnative]
  simp only [Code.selected,Keys.row,Code.side,List.append_nil,List.map_append]
  simp only [ho,hf,decide_eq_true_eq]
  split_ifs <;> simp_all only [decide_true,decide_false,ite_true,ite_false,
    List.nil_append,List.append_nil,List.map_nil,List.map_cons] <;> rfl
/-- Whole actual forward catalogue equals the ENTIRE original native endpoint list, in exact order. -/
theorem endpoints_original (i:Inputs) (n F a:Nat) (arity:Fin F→Nat)
    (owner:((e:Fin F)×Fin (arity e))→Fin n) (q:Fin a) (g:Fin 64)
    (hg:SemiprimeBitArithmetic.bitValue i.group=g.val):
    Forward.endpoints i a q.val (Act.originalIDs n F a arity owner) (Fld.fields n F a arity owner)=
      (Native.acquire n F 64 a arity owner q g).endpoints.map encode:=by
  rw [Forward.endpoints,Forward.rows,Pair.fields_typed,List.map_map,selected_flatMap,List.flatMap_map]
  change _=(Native.scan owner (Fld.source n F a arity owner).padding.source.selection.cache.rows.source.dictionary
    a q.val (SemiprimeSourceHistogramPortKeys.encodeKey g.val).bits
      ((Fld.source n F a arity owner).padding.source.selection.cache.data.metadata.incidences.zip
        (Fld.source n F a arity owner).placements)).value.map encode
  have hports:(Fld.source n F a arity owner).padding.source.selection.cache.data.metadata.incidences=
      SemiprimeD1CollisionOriginal.ports n F a arity:=
    SemiprimeD1ChildGraphSemantics.original_ports n F 64 a arity owner
  rw [hports,SemiprimeD1ChildGraphSemantics.scan_value,List.map_flatMap]
  apply List.flatMap_congr
  intro p hp
  exact one_original i n F a arity owner q g hg p hp
end RiemannGaussian.SemiprimeD1StackChildGroupFactoryNativeEndpoints
