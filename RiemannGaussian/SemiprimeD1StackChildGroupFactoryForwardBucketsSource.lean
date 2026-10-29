/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackChildGroupFactoryForwardSource
import RiemannGaussian.SemiprimeD1StackChildGroupFactoryEndpointSourceView
import RiemannGaussian.SemiprimeD1StackChildGroupFactoryBucketsSource
import RiemannGaussian.SemiprimeD1StackChildGroupFactoryCatalogueCodecs
/-! # Actual thirteen-input entry through complete chronological child buckets
Generated forward endpoint bytes feed the actual packet scan directly. All
activation flags and fresh child IDs are computed by the same literal program;
no endpoint list or bucket answer is supplied as an additional runtime input.
-/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackChildGroupFactoryForwardBucketsSource
open SemiprimeD1StackChildGroupFactoryRoles SemiprimeD1StackChildGroupFactoryWiring
open SemiprimeD1StackChildGroupFactory SemiprimeD1StackChildGroupFactoryPrimitives
open SemiprimeD1StackProcedureTrace
namespace Forward
export SemiprimeD1StackChildGroupFactoryForwardSource (activation rows result timeBound source_trace)
end Forward
namespace A
export SemiprimeD1StackChildGroupFactoryActivationSource (result)
end A
namespace EV
export SemiprimeD1StackChildGroupFactoryEndpointSourceView (Protected result_other result_clean result_endpoints)
end EV
namespace Parse
export SemiprimeD1StackChildGroupFactoryEndpointParse (Fields)
end Parse
namespace Bucket
export SemiprimeD1StackChildGroupFactoryBucketsSource (result timeBound source_trace)
end Bucket
namespace BP
export SemiprimeD1StackChildGroupFactoryBucketParse (cleanRoles)
end BP
namespace Code
export SemiprimeD1StackChildGroupFactoryCatalogueCodecs (selected selected_records)
end Code
/-- Actual generated endpoint interpretation; never an extra runtime tape. -/
def endpoints (i:Inputs) (a coordinate:Nat) (ids:List (List Bool)) (fields:List Parse.Fields):=
  Code.selected (Forward.rows i a coordinate ids fields)
/-- Complete physical bank after actual forward endpoint and bucket acquisition. -/
def result (i:Inputs) (a coordinate:Nat) (ids packets:List (List Bool)) (fields:List Parse.Fields):Stack→List Bool:=
  Bucket.result (Forward.result i a coordinate ids fields) packets (endpoints i a coordinate ids fields) []
/-- Composed own clock on the actually generated forward endpoint tape. -/
def timeBound (i:Inputs) (a coordinate:Nat) (ids packets:List (List Bool)) (fields:List Parse.Fields):Nat:=
  Forward.timeBound i a coordinate ids fields+
    Bucket.timeBound (Forward.result i a coordinate ids fields) packets (endpoints i a coordinate ids fields) []
/-- All physical words outside the actual endpoint source's fixed work image retain their activation boundary bytes. -/
theorem forward_other (i:Inputs) (a coordinate:Nat) (ids:List (List Bool)) (fields:List Parse.Fields)
    (k:Stack) (hk:EV.Protected k):
    Forward.result i a coordinate ids fields k=A.result i coordinate (Forward.activation a ids) k:=
  EV.result_other _ _ k hk
/-- Every actual bucket parser destination is fresh after forward endpoint acquisition. -/
theorem forward_clean (i:Inputs) (a coordinate:Nat) (ids:List (List Bool)) (fields:List Parse.Fields):
    ∀k∈BP.cleanRoles,Forward.result i a coordinate ids fields k=[]:=by
  have hraw:=EV.result_clean (A.result i coordinate (Forward.activation a ids)) (Forward.rows i a coordinate ids fields)
    (by simp [A.result,SemiprimeD1StackChildGroupFactoryActivation.data,input,
      SemiprimeD1StackChildGroupFactoryEndpointParse.cleanRoles,aux,field])
  intro k hk
  simp only [BP.cleanRoles,List.mem_cons,List.not_mem_nil,or_false] at hk
  rcases hk with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
  · exact hraw _ (by simp [SemiprimeD1StackChildGroupFactoryEndpointParse.cleanRoles])
  · exact hraw _ (by simp [SemiprimeD1StackChildGroupFactoryEndpointParse.cleanRoles])
  · exact hraw _ (by simp [SemiprimeD1StackChildGroupFactoryEndpointParse.cleanRoles])
  · exact hraw _ (by simp [SemiprimeD1StackChildGroupFactoryEndpointParse.cleanRoles])
  · rw [forward_other _ _ _ _ _ _ (by
      constructor
      all_goals first | (intro j;fin_cases j <;> decide) | decide)]
    rfl
  · rw [forward_other _ _ _ _ _ _ (by
      constructor
      all_goals first | (intro j;fin_cases j <;> decide) | decide)]
    rfl
  · exact hraw _ (by simp [SemiprimeD1StackChildGroupFactoryEndpointParse.cleanRoles])
  · exact hraw _ (by simp [SemiprimeD1StackChildGroupFactoryEndpointParse.cleanRoles])
/-- Whole actual entry through ALL real observed packet buckets, including empty and duplicate keys. -/
theorem source_trace (i:Inputs) (a coordinate:Nat) (ids packets:List (List Bool)) (fields:List Parse.Fields)
    (hids:∀id∈ids,id∈(SemiprimeSourceCompactWordBank.acquire 64 a).ids)
    (he:i.environment=SemiprimeD1StackSourceEnvironmentEncoding.dictionary ids)
    (hc:i.catalogue=SemiprimeD1StackPacketRowsOriginal.catalogue a)
    (hi:i.colourIndex=List.replicate coordinate true)
    (hlen:ids.length=i.owners.length+i.factors.length)
    (hpairs:i.occurrences=SemiprimeD1StackChildGroupFactoryEndpointKeys.pairs fields)
    (hplacements:i.placements=SemiprimeD1StackChildGroupFactoryEndpointKeys.placements fields)
    (hdom:∀f∈fields,SemiprimeBitArithmetic.bitValue f.owner < ids.length ∧
      SemiprimeBitArithmetic.bitValue f.factor < ids.length)
    (hpackets:i.packets=SemiprimeD1TensorTapeCodec.vectorBits packets):
    ∃t≤timeBound i a coordinate ids packets fields,
      Runs program t entry (input i) (.local 9 2) (result i a coordinate ids packets fields):=by
  obtain ⟨x,hx,h0⟩:=Forward.source_trace i a coordinate ids fields hids he hc hi hlen hpairs hplacements hdom
  have fresh (k:Stack) (hk:EV.Protected k)
      (hz:A.result i coordinate (Forward.activation a ids) k=[]):Forward.result i a coordinate ids fields k=[]:=
    (forward_other _ _ _ _ _ _ hk).trans hz
  have hparse:=forward_clean i a coordinate ids fields
  have ht:Forward.result i a coordinate ids fields (aux .packets)=SemiprimeD1TensorTapeCodec.vectorBits packets:=by
    rw [forward_other _ _ _ _ _ _ (by
      constructor
      all_goals first | (intro j;fin_cases j <;> decide) | decide)]
    exact hpackets
  have hep:Forward.result i a coordinate ids fields (aux .endpoints)=
      SemiprimeD1StackChildGroupFactoryBucketParse.records (endpoints i a coordinate ids fields):=by
    rw [show Forward.result i a coordinate ids fields (aux .endpoints)=
      SemiprimeD1StackChildGroupFactoryEndpointLoopView.selectedRecords (Forward.rows i a coordinate ids fields)++[false] from rfl]
    exact (Code.selected_records _).symm
  obtain ⟨y,hy,h1⟩:=Bucket.source_trace (Forward.result i a coordinate ids fields) packets
    (endpoints i a coordinate ids fields) [] ht
    (fresh _ (by constructor;all_goals first | (intro j;fin_cases j <;> decide) | decide) rfl)
    hep (fresh _ (by constructor;all_goals first | (intro j;fin_cases j <;> decide) | decide) rfl) hparse
    (by exact EV.result_clean _ _ (by simp [A.result,SemiprimeD1StackChildGroupFactoryActivation.data,input,
      SemiprimeD1StackChildGroupFactoryEndpointParse.cleanRoles,aux,field]) _ (by simp [SemiprimeD1StackChildGroupFactoryEndpointParse.cleanRoles]))
    (fresh _ (by constructor;all_goals first | (intro j;fin_cases j <;> decide) | decide) rfl)
    (fresh _ (by constructor;all_goals first | (intro j;fin_cases j <;> decide) | decide) rfl)
    (fresh _ (by constructor;all_goals first | (intro j;fin_cases j <;> decide) | decide) rfl)
    (by intro k;apply fresh _ ?_ rfl;constructor;all_goals first | (intro j;fin_cases j <;> cases k <;> decide) | (cases k <;> decide))
    (by intro k;apply fresh _ ?_ rfl;constructor;all_goals first | (intro j;fin_cases j <;> cases k <;> decide) | (cases k <;> decide))
    (fresh _ (by constructor;all_goals first | (intro j;fin_cases j <;> decide) | decide) rfl)
    (fresh _ (by constructor;all_goals first | (intro j;fin_cases j <;> decide) | decide) rfl)
    (fresh _ (by constructor;all_goals first | (intro j;fin_cases j <;> decide) | decide) rfl)
    (fresh _ (by constructor;all_goals first | (intro j;fin_cases j <;> decide) | decide) rfl)
    (fresh _ (by constructor;all_goals first | (intro j;fin_cases j <;> decide) | decide) rfl)
    (fresh _ (by constructor;all_goals first | (intro j;fin_cases j <;> decide) | decide) rfl)
  refine ⟨x+y,?_,join h0 h1⟩
  dsimp only [timeBound];omega
end RiemannGaussian.SemiprimeD1StackChildGroupFactoryForwardBucketsSource
