/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackChildGroupFactoryExecution
/-! # Actual completed frontdoor supplies the entire subsequent vertex-source ABI
The keys, chronological original records and numbered child buckets are all
computed by the same source. No decoded list, readiness flag or answer is input.
-/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackChildGroupFactoryFrontierView
open SemiprimeD1StackChildGroupFactoryRoles SemiprimeD1StackChildGroupFactoryWiring
open SemiprimeD1StackChildGroupFactory SemiprimeD1StackProcedureTrace
namespace Forward
export SemiprimeD1StackChildGroupFactoryForwardSource (activation rows result)
end Forward
namespace A
export SemiprimeD1StackChildGroupFactoryActivationSource (result)
end A
namespace Source
export SemiprimeD1StackChildGroupFactoryForwardBucketsSource (endpoints result timeBound source_trace forward_other)
end Source
namespace EV
export SemiprimeD1StackChildGroupFactoryEndpointSourceView (Protected result_oldEndpoints)
end EV
namespace BV
export SemiprimeD1StackChildGroupFactoryBucketsSourceView (Protected result_other result_buckets result_factorHistory)
end BV
namespace Code
export SemiprimeD1StackChildGroupFactoryCatalogueCodecs (oldPoints oldPoints_records buckets buckets_records)
end Code
namespace Parse
export SemiprimeD1StackChildGroupFactoryEndpointParse (Fields)
end Parse

/-- The actual all-vertex source receives real retained records, cache and zero key. -/
theorem actual_frontier (i:Inputs) (a coordinate:Nat) (ids packets:List (List Bool)) (fields:List Parse.Fields):
    SemiprimeD1StackChildGroupFactoryVertexBody.Ready (Source.result i a coordinate ids packets fields) ∧
    Source.result i a coordinate ids packets fields (aux .oldEndpoints)=
      SemiprimeD1StackChildGroupFactoryOldPortParse.records (Code.oldPoints (Forward.rows i a coordinate ids fields)) ∧
    Source.result i a coordinate ids packets fields (aux .buckets)=
      SemiprimeD1StackChildGroupFactoryLeftPortsLoop.records
        (Code.buckets packets (Source.endpoints i a coordinate ids fields) []) ∧
    Source.result i a coordinate ids packets fields (aux .vertexKey)=[]:=by
  let before:=Source.result i a coordinate ids packets fields
  let points:=Code.oldPoints (Forward.rows i a coordinate ids fields)
  let buckets:=Code.buckets packets (Source.endpoints i a coordinate ids fields) []
  have same (k:Stack) (hb:BV.Protected k) (he:EV.Protected k):
      before k=A.result i coordinate (Forward.activation a ids) k:=by
    exact (BV.result_other _ _ _ _ _ hb).trans (Source.forward_other _ _ _ _ _ _ he)
  have hbh:Forward.result i a coordinate ids fields (aux .bucketHistory)=[]:=by
    rw [Source.forward_other _ _ _ _ _ _ (by
      constructor
      all_goals first | (intro j;fin_cases j <;> decide) | decide)]
    rfl
  have hr:=SemiprimeD1StackChildGroupFactoryBucketReady.result_ready
    (Forward.result i a coordinate ids fields) packets (Source.endpoints i a coordinate ids fields) []
    (SemiprimeD1StackChildGroupFactoryForwardReady.result_ready i a coordinate ids fields) hbh
  have hpoints:before (aux .oldEndpoints)=SemiprimeD1StackChildGroupFactoryOldPortParse.records points:=by
    rw [show before (aux .oldEndpoints)=Forward.result i a coordinate ids fields (aux .oldEndpoints) from
      BV.result_other _ _ _ _ _ (by
        constructor
        all_goals first | (intro j;fin_cases j <;> decide) | decide)]
    rw [show Forward.result i a coordinate ids fields (aux .oldEndpoints)=
      SemiprimeD1StackChildGroupFactoryEndpointLoopView.oldRecords (Forward.rows i a coordinate ids fields)++[false] from rfl]
    exact (Code.oldPoints_records _).symm
  have hbuckets:before (aux .buckets)=SemiprimeD1StackChildGroupFactoryLeftPortsLoop.records buckets:=by
    exact (Code.buckets_records _ _ _).symm
  have zero (k:Stack) (hb:BV.Protected k) (he:EV.Protected k)
      (hz:A.result i coordinate (Forward.activation a ids) k=[]):before k=[]:=(same k hb he).trans hz
  exact ⟨hr,hpoints,hbuckets,zero _
    (by constructor;all_goals first | (intro j;fin_cases j <;> decide) | decide)
    (by constructor;all_goals first | (intro j;fin_cases j <;> decide) | decide) rfl⟩
end RiemannGaussian.SemiprimeD1StackChildGroupFactoryFrontierView
