/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackChildGroupFactoryBucketsSource
/-! # Whole actual bucket catalogue restoration, including empty packet vectors -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackChildGroupFactoryBucketsSourceView
open SemiprimeD1StackChildGroupFactoryRoles SemiprimeD1StackChildGroupFactoryBucketsSource
namespace One
export SemiprimeD1StackChildGroupFactoryBucketOneView
  (result_clean result_reuse result_endpointReader result_histories)
end One
namespace LoopDef
export SemiprimeD1StackChildGroupFactoryBucketsLoop (result atEOF)
end LoopDef
/-- Fixed physical source-bank exclusions, independent of any prepared operand. -/
structure Protected (k:Stack):Prop where
  raw:∀j,Cleanup.role j≠k
  reuse:∀j,Reuse.role j≠k
  packetReader:k≠aux .packetReader
  endpointReader:k≠aux .endpointReader
  bucketHistory:k≠aux .bucketHistory
  portHistory:k≠aux .portHistory
  globalPosition:k≠aux .globalPosition
  factorHistory:k≠aux .factorHistory
  buckets:k≠aux .buckets
/-- All actual source/cache words outside fixed work and outputs remain byte-identical. -/
theorem result_other (before:Stack→List Bool) (packets:List (List Bool)) (es:List Parse.Endpoint)
    (position:List Bool) (k:Stack) (hk:Protected k):result before packets es position k=before k:=by
  simp only [result,Function.update_of_ne hk.buckets,Function.update_of_ne hk.factorHistory]
  rw [View.result_other _ _ _ _ _ hk.raw hk.reuse hk.packetReader hk.endpointReader hk.bucketHistory
    hk.portHistory hk.globalPosition hk.factorHistory]
  exact Function.update_of_ne hk.packetReader _ _
/-- Parser/raw fields are clean after every real observed-packet iteration. -/
theorem loop_clean (packets:List (List Bool)) (before:Stack→List Bool) (es:List Parse.Endpoint) (position:List Bool)
    (hz:∀k∈Parse.cleanRoles,before k=[]):∀k∈Parse.cleanRoles,Loop.result packets before es position k=[]:=by
  induction packets generalizing before position with
  | nil=>
    intro k hk
    simp only [Parse.cleanRoles,List.mem_cons,List.not_mem_nil,or_false] at hk
    rcases hk with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
    all_goals simpa [LoopDef.result,LoopDef.atEOF,aux,field] using hz _ (by simp [Parse.cleanRoles,aux,field])
  | cons packet packets ih=>exact ih _ _ (One.result_clean _ _ _ _ _ hz)
/-- The actual packet/converter reuse word is empty even when no packet was present. -/
theorem loop_reuse (packets:List (List Bool)) (before:Stack→List Bool) (es:List Parse.Endpoint) (position:List Bool)
    (hz:∀j,before (Reuse.role j)=[]):∀j,Loop.result packets before es position (Reuse.role j)=[]:=by
  induction packets generalizing before position with
  | nil=>
    intro j
    exact (Function.update_of_ne (by fin_cases j <;> decide : Reuse.role j≠aux .packetReader) _ _).trans (hz j)
  | cons packet packets ih=>exact ih _ _ (One.result_reuse _ _ _ _ _)
/-- Real endpoint EOF consumption or retained initial emptiness makes its work reader empty. -/
theorem loop_endpointReader (packets:List (List Bool)) (before:Stack→List Bool) (es:List Parse.Endpoint) (position:List Bool)
    (hz:before (aux .endpointReader)=[]):Loop.result packets before es position (aux .endpointReader)=[]:=by
  induction packets generalizing before position with
  | nil=>simpa [LoopDef.result,LoopDef.atEOF,aux] using hz
  | cons packet packets ih=>exact ih _ _ (One.result_endpointReader _ _ _ _ _)
/-- Both real row histories are physically empty at each completed bucket boundary. -/
theorem loop_histories (packets:List (List Bool)) (before:Stack→List Bool) (es:List Parse.Endpoint) (position:List Bool)
    (hb:before (aux .bucketHistory)=[]) (hp:before (aux .portHistory)=[]):
    Loop.result packets before es position (aux .bucketHistory)=[] ∧
      Loop.result packets before es position (aux .portHistory)=[]:=by
  induction packets generalizing before position with
  | nil=>constructor
         · simpa [LoopDef.result,LoopDef.atEOF,aux] using hb
         · simpa [LoopDef.result,LoopDef.atEOF,aux] using hp
  | cons packet packets ih=>exact ih _ _ (One.result_histories _ _ _ _ _).1 (One.result_histories _ _ _ _ _).2
/-- The complete source preserves actual parser freshness through the final real bucket reversal. -/
theorem result_clean (before:Stack→List Bool) (packets:List (List Bool)) (es:List Parse.Endpoint) (position:List Bool)
    (hz:∀k∈Parse.cleanRoles,before k=[]):∀k∈Parse.cleanRoles,result before packets es position k=[]:=by
  have hz':∀k∈Parse.cleanRoles,copied before packets k=[]:=by simpa [copied,Parse.cleanRoles,aux,field] using hz
  have h:=loop_clean packets (copied before packets) es position hz'
  intro k hk
  simp only [Parse.cleanRoles,List.mem_cons,List.not_mem_nil,or_false] at hk
  rcases hk with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
  all_goals simpa [result,aux,field] using h _ (by simp [Parse.cleanRoles,aux,field])
/-- All fifteen reuse roles, including all twelve converter allocations, are actually empty. -/
theorem result_reuse (before:Stack→List Bool) (packets:List (List Bool)) (es:List Parse.Endpoint) (position:List Bool)
    (hz:∀j,before (Reuse.role j)=[]):∀j,result before packets es position (Reuse.role j)=[]:=by
  have hz':∀j,copied before packets (Reuse.role j)=[]:=by
    intro j
    exact (Function.update_of_ne (by fin_cases j <;> decide : Reuse.role j≠aux .packetReader) _ _).trans (hz j)
  have h:=loop_reuse packets (copied before packets) es position hz'
  intro j
  have hn:Reuse.role j≠aux .buckets:=by fin_cases j <;> decide
  have hf:Reuse.role j≠aux .factorHistory:=by fin_cases j <;> decide
  simpa only [result,Function.update_of_ne hn,Function.update_of_ne hf] using h j
/-- Single reuse word restoration requires only its own actual initial emptiness. -/
theorem loop_reuse_word (packets:List (List Bool)) (before:Stack→List Bool) (es:List Parse.Endpoint) (position:List Bool)
    (j:Fin 15) (hz:before (Reuse.role j)=[]):Loop.result packets before es position (Reuse.role j)=[]:=by
  induction packets generalizing before position with
  | nil=>exact (Function.update_of_ne (by fin_cases j <;> decide : Reuse.role j≠aux .packetReader) _ _).trans hz
  | cons packet packets ih=>exact ih _ _ (One.result_reuse _ _ _ _ _ j)
/-- Single reuse role after the actual final reversal, including the zero-packet case. -/
theorem result_reuse_word (before:Stack→List Bool) (packets:List (List Bool)) (es:List Parse.Endpoint) (position:List Bool)
    (j:Fin 15) (hz:before (Reuse.role j)=[]):result before packets es position (Reuse.role j)=[]:=by
  have hz':copied before packets (Reuse.role j)=[]:=
    (Function.update_of_ne (by fin_cases j <;> decide : Reuse.role j≠aux .packetReader) _ _).trans hz
  have h:=loop_reuse_word packets (copied before packets) es position j hz'
  have hn:Reuse.role j≠aux .buckets:=by fin_cases j <;> decide
  have hf:Reuse.role j≠aux .factorHistory:=by fin_cases j <;> decide
  simpa only [result,Function.update_of_ne hn,Function.update_of_ne hf] using h
/-- Actual endpoint-reader emptiness survives the complete catalogue reversal. -/
theorem result_endpointReader (before:Stack→List Bool) (packets:List (List Bool)) (es:List Parse.Endpoint) (position:List Bool)
    (hz:before (aux .endpointReader)=[]):result before packets es position (aux .endpointReader)=[]:=by
  have h:=loop_endpointReader packets (copied before packets) es position (by simpa [copied,aux] using hz)
  simpa [result,aux] using h
/-- Both real per-bucket histories remain empty after the final catalogue reversal. -/
theorem result_histories (before:Stack→List Bool) (packets:List (List Bool)) (es:List Parse.Endpoint) (position:List Bool)
    (hb:before (aux .bucketHistory)=[]) (hp:before (aux .portHistory)=[]):
    result before packets es position (aux .bucketHistory)=[] ∧ result before packets es position (aux .portHistory)=[]:=by
  have h:=loop_histories packets (copied before packets) es position
    (by simpa [copied,aux] using hb) (by simpa [copied,aux] using hp)
  constructor
  · simpa [result,aux] using h.1
  · simpa [result,aux] using h.2
/-- The actual source clears its completed bucket-log history with a genuine reversal. -/
theorem result_factorHistory (before:Stack→List Bool) (packets:List (List Bool)) (es:List Parse.Endpoint) (position:List Bool):
    result before packets es position (aux .factorHistory)=[]:=rfl
/-- Exact emitted bucket tape, with every observed empty or duplicate bucket retained. -/
theorem result_buckets (before:Stack→List Bool) (packets:List (List Bool)) (es:List Parse.Endpoint) (position:List Bool):
    result before packets es position (aux .buckets)=View.records packets es position++[false]:=rfl
end RiemannGaussian.SemiprimeD1StackChildGroupFactoryBucketsSourceView
