/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackChildGroupFactoryForwardReady
import RiemannGaussian.SemiprimeD1StackChildGroupFactoryBucketReady
import RiemannGaussian.SemiprimeD1StackChildGroupFactorySuffix
/-! # Whole literal thirteen-input child-group factory through true halt
Every activation, endpoint, bucket, unary scope and original-port order is
computed by the same finite controller. The decoded proof views below are
interpretations of real source words, never additional physical operands.
This remains a prepared structural-cache source; recursive child table
production, context installation and the literal N-only caller are separate.
-/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackChildGroupFactoryExecution
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
namespace Last
export SemiprimeD1StackChildGroupFactorySuffix (result timeBound source_run)
end Last
/-- Exact stopped bank, with every computed source tape and actual successful cleanup. -/
def result (i:Inputs) (a coordinate:Nat) (ids packets:List (List Bool)) (fields:List Parse.Fields):Stack→List Bool:=
  Last.result (Source.result i a coordinate ids packets fields) i.owners i.factors
    (Code.oldPoints (Forward.rows i a coordinate ids fields))
    (Code.buckets packets (Source.endpoints i a coordinate ids fields) []) []
/-- Exact true halt state; all private cleanup and the actual success byte are included. -/
def done (i:Inputs) (a coordinate:Nat) (ids packets:List (List Bool)) (fields:List Parse.Fields):C.State Stack Label:=
  ⟨none,none,none,result i a coordinate ids packets fields,[]⟩
/-- SAME-program total own clock, including value-sensitive generated-ID conversions. -/
def timeBound (i:Inputs) (a coordinate:Nat) (ids packets:List (List Bool)) (fields:List Parse.Fields):Nat:=
  Source.timeBound i a coordinate ids packets fields+
    Last.timeBound (Source.result i a coordinate ids packets fields) i.owners i.factors
      (Code.oldPoints (Forward.rows i a coordinate ids fields))
      (Code.buckets packets (Source.endpoints i a coordinate ids fields) []) []
/-- Complete actual source, including all real outer return frames and arbitrary transient flags. -/
theorem source_run_at (i:Inputs) (a coordinate:Nat) (ids packets:List (List Bool)) (fields:List Parse.Fields)
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
    ∃t≤timeBound i a coordinate ids packets fields,∀frames (start:C.State Stack Label),
      At entry (input i) frames start→C.run program t start=
        some (⟨none,none,none,result i a coordinate ids packets fields,frames⟩:C.State Stack Label):=by
  obtain ⟨x,hx,h0⟩:=Source.source_trace i a coordinate ids packets fields hids he hc hi hlen hpairs hplacements hdom hpackets
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
  have sourceWord (k:Stack) (hb:BV.Protected k) (he:EV.Protected k):
      before k=A.result i coordinate (Forward.activation a ids) k:=same k hb he
  obtain ⟨y,hy,h1⟩:=Last.source_run before i.owners i.factors points buckets []
    (sourceWord _ (by constructor;all_goals first | (intro j;fin_cases j <;> decide) | decide)
      (by constructor;all_goals first | (intro j;fin_cases j <;> decide) | decide))
    (sourceWord _ (by constructor;all_goals first | (intro j;fin_cases j <;> decide) | decide)
      (by constructor;all_goals first | (intro j;fin_cases j <;> decide) | decide))
    (zero _ (by constructor;all_goals first | (intro j;fin_cases j <;> decide) | decide)
      (by constructor;all_goals first | (intro j;fin_cases j <;> decide) | decide) rfl)
    (zero _ (by constructor;all_goals first | (intro j;fin_cases j <;> decide) | decide)
      (by constructor;all_goals first | (intro j;fin_cases j <;> decide) | decide) rfl)
    hpoints hbuckets
    (zero _ (by constructor;all_goals first | (intro j;fin_cases j <;> decide) | decide)
      (by constructor;all_goals first | (intro j;fin_cases j <;> decide) | decide) rfl) hr
    (zero _ (by constructor;all_goals first | (intro j;fin_cases j <;> decide) | decide)
      (by constructor;all_goals first | (intro j;fin_cases j <;> decide) | decide) rfl)
    (BV.result_factorHistory _ _ _ _)
    (zero _ (by constructor;all_goals first | (intro j;fin_cases j <;> decide) | decide)
      (by constructor;all_goals first | (intro j;fin_cases j <;> decide) | decide) rfl)
    (zero _ (by constructor;all_goals first | (intro j;fin_cases j <;> decide) | decide)
      (by constructor;all_goals first | (intro j;fin_cases j <;> decide) | decide) rfl)
  refine ⟨x+y,?_,?_⟩
  · dsimp only [timeBound,before,points,buckets] at hy ⊢;omega
  · intro frames start hs
    obtain ⟨mid,hm,hat⟩:=h0 frames start hs
    have hh:=h1 frames mid hat
    rw [SemiprimeD1StackReturnLink.run_add,hm,Option.bind_some]
    exact hh
/-- Whole actual prepared thirteen-word entry; there is no supplied output tape or clock operand. -/
theorem source_run (i:Inputs) (a coordinate:Nat) (ids packets:List (List Bool)) (fields:List Parse.Fields)
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
      C.run program t (initial i)=some (done i a coordinate ids packets fields):=by
  obtain ⟨t,ht,h⟩:=source_run_at i a coordinate ids packets fields hids he hc hi hlen hpairs hplacements hdom hpackets
  exact ⟨t,ht,h [] (initial i) ⟨rfl,rfl,rfl⟩⟩
end RiemannGaussian.SemiprimeD1StackChildGroupFactoryExecution
