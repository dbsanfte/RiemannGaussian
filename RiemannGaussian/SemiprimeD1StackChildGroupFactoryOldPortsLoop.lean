/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackChildGroupFactoryOldPortOneView
/-! # Entire actual original-port ordering loop for one old vertex
Twenty fixed physical fresh roles are proved restored after EVERY whole query.
Every real old record is parsed; matching vertices execute the full nested
first-index source and retain original old-port order and multiplicities.
-/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackChildGroupFactoryOldPortsLoop
open SemiprimeD1StackChildGroupFactoryRoles SemiprimeD1StackChildGroupFactoryWiring
open SemiprimeD1StackChildGroupFactory SemiprimeD1StackChildGroupFactoryPrimitives
open SemiprimeD1StackProcedureTrace
namespace One
export SemiprimeD1StackChildGroupFactoryOldPortOne (result timeBound source_trace)
end One
namespace OV
export SemiprimeD1StackChildGroupFactoryOldPortOneView
  (result_other result_oldReader result_work result_answer result_local result_tag answerWord result_orderHistory)
end OV
namespace Parse
export SemiprimeD1StackChildGroupFactoryOldPortParse (Point records cleanRoles)
end Parse
namespace Header
export SemiprimeD1StackChildGroupFactoryBucketHeader (cleanRoles)
end Header
namespace Child
export SemiprimeD1StackChildGroupFactoryChildParse (cleanRoles)
end Child
namespace Buckets
export SemiprimeD1StackChildGroupFactoryLeftPortsLoop (Bucket records)
end Buckets
namespace Early
export SemiprimeD1StackChildGroupFactoryTagEarlyClear (role)
end Early
namespace Log
export SemiprimeD1StackChildGroupFactoryWordLog (row)
end Log
open SemiprimeBitArithmetic (bitValue)
/-- The twenty actual original-query work/parser/buffer roles; fixed before all input bytes. -/
def freshRole:Fin 20→Stack
  | 0=>aux .outerReader
  | 1=>aux .childReader
  | 2=>aux .endpointReader
  | 3=>aux .rowBuffer
  | 4=>aux .ownerKey
  | 5=>aux .sourceKey
  | 6=>aux .slotWord
  | 7=>aux .edgeWord
  | 8=>aux .sideWord
  | 9=>aux .globalPosition
  | 10=>aux .candidateTag
  | 11=>aux .answerPosition
  | 12=>aux .localPosition
  | 13=>aux .tagWord
  | 14=>aux .packetKey
  | 15=>aux .paddingKey
  | 16=>field (.inl .scratch)
  | 17=>field (.inr ())
  | 18=>aux .frameBuffer
  | 19=>aux .copyScratch
  | _=>aux .copyScratch
/-- Real data-only freshness, not a runtime flag or an answer promise. -/
def Fresh (before:Stack→List Bool):Prop:=∀j,before (freshRole j)=[]
/-- Actual oldFresh destinations are among the same twenty physical fresh roles. -/
theorem oldFresh (before:Stack→List Bool) (hf:Fresh before):∀k∈Parse.cleanRoles,before k=[]:=by
  intro k hk
  simp only [Parse.cleanRoles,List.mem_cons,List.not_mem_nil,or_false] at hk
  rcases hk with rfl|rfl|rfl|rfl|rfl|rfl
  · exact hf 4
  · exact hf 7
  · exact hf 8
  · exact hf 3
  · exact hf 16
  · exact hf 17
/-- Actual headerFresh destinations are among the same twenty physical fresh roles. -/
theorem headerFresh (before:Stack→List Bool) (hf:Fresh before):∀k∈Header.cleanRoles,before k=[]:=by
  intro k hk
  simp only [Header.cleanRoles,List.mem_cons,List.not_mem_nil,or_false] at hk
  rcases hk with rfl|rfl|rfl|rfl|rfl|rfl
  · exact hf 1
  · exact hf 14
  · exact hf 2
  · exact hf 15
  · exact hf 16
  · exact hf 17
/-- Actual childFresh destinations are among the same twenty physical fresh roles. -/
theorem childFresh (before:Stack→List Bool) (hf:Fresh before):∀k∈Child.cleanRoles,before k=[]:=by
  intro k hk
  simp only [Child.cleanRoles,List.mem_cons,List.not_mem_nil,or_false] at hk
  rcases hk with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
  · exact hf 4
  · exact hf 5
  · exact hf 6
  · exact hf 7
  · exact hf 8
  · exact hf 9
  · exact hf 3
  · exact hf 16
  · exact hf 17
/-- Every complete actual original-port iteration restores the entire real fresh bank. -/
theorem fresh_step (before:Stack→List Bool) (buckets:List Buckets.Bucket) (p:Parse.Point) (tail target:List Bool)
    (hf:Fresh before):Fresh (One.result before buckets p tail target):=by
  have hw:=OV.result_work before buckets p tail target (headerFresh before hf) (childFresh before hf) (hf 0) (hf 10)
  intro j
  fin_cases j
  · exact hw 0
  · exact hw 1
  · exact hw 2
  · exact hw 3
  · exact hw 4
  · exact hw 5
  · exact hw 6
  · exact hw 7
  · exact hw 8
  · exact hw 9
  · exact hw 10
  · exact OV.result_answer _ _ _ _ _ (hf 11)
  · exact OV.result_local _ _ _ _ _ (hf 12)
  · exact OV.result_tag _ _ _ _ _ (hf 13)
  · exact (OV.result_other _ _ _ _ _ (freshRole 14) (by intro k;fin_cases k <;> decide)
      (by decide) (by decide) (by decide) (by decide) (by decide)).trans (hf 14)
  · exact (OV.result_other _ _ _ _ _ (freshRole 15) (by intro k;fin_cases k <;> decide)
      (by decide) (by decide) (by decide) (by decide) (by decide)).trans (hf 15)
  · exact (OV.result_other _ _ _ _ _ (freshRole 16) (by intro k;fin_cases k <;> decide)
      (by decide) (by decide) (by decide) (by decide) (by decide)).trans (hf 16)
  · exact (OV.result_other _ _ _ _ _ (freshRole 17) (by intro k;fin_cases k <;> decide)
      (by decide) (by decide) (by decide) (by decide) (by decide)).trans (hf 17)
  · exact (OV.result_other _ _ _ _ _ (freshRole 18) (by intro k;fin_cases k <;> decide)
      (by decide) (by decide) (by decide) (by decide) (by decide)).trans (hf 18)
  · exact (OV.result_other _ _ _ _ _ (freshRole 19) (by intro k;fin_cases k <;> decide)
      (by decide) (by decide) (by decide) (by decide) (by decide)).trans (hf 19)
/-- Exact actual binary answer words in original old-port order. -/
def orderWords (buckets:List Buckets.Bucket):List Parse.Point→List Bool→List (List Bool)
  | [],_=>[]
  | p::ps,target=>if bitValue p.vertex=bitValue target then OV.answerWord buckets p target::orderWords buckets ps target
    else orderWords buckets ps target
/-- Actual EOF leaves the original-port reader physically empty. -/
def atEOF (before:Stack→List Bool):Stack→List Bool:=Function.update before (aux .oldReader) []
/-- Full actual original-port loop bank. -/
def result:List Parse.Point→(Stack→List Bool)→List Buckets.Bucket→List Bool→Stack→List Bool
  | [],before,_,_=>atEOF before
  | p::ps,before,buckets,target=>result ps (One.result before buckets p (Parse.records ps) target) buckets target
/-- Own complete actual query clocks and final real EOF pair. -/
def timeBound:List Parse.Point→(Stack→List Bool)→List Buckets.Bucket→List Bool→Nat
  | [],_,_,_=>2
  | p::ps,before,buckets,target=>One.timeBound before buckets p (Parse.records ps) target+
      timeBound ps (One.result before buckets p (Parse.records ps) target) buckets target
/-- Exact original-port EOF instructions, including a real empty-suffix test. -/
theorem eof_trace (before:Stack→List Bool) (hr:before (aux .oldReader)=[false]):
    Runs program 2 (.local 11 7) before (.local 14 9) (atEOF before):=by
  have h0:=pop_run (.local 11 7) abort (.local 11 8) (.local 11 9) (aux .oldReader) before [false] rfl hr
  simp only [List.head?_cons,List.tail_cons,SemiprimeD1StackBytecode.choose] at h0
  have h1:=peek_run (.local 11 8) (.local 14 9) abort abort (aux .oldReader) (atEOF before) [] rfl (Function.update_self _ _ _)
  simp only [List.head?_nil,SemiprimeD1StackBytecode.choose] at h1
  exact join h0 h1
/-- Entire actual old-port loop, executing each needed real query rather than an idxOf/getter opcode. -/
theorem source_trace (points:List Parse.Point) (before:Stack→List Bool) (buckets:List Buckets.Bucket) (target:List Bool)
    (hi:before (aux .oldReader)=Parse.records points) (hs:before (aux .buckets)=Buckets.records buckets)
    (ht:before (aux .vertexKey)=target) (hf:Fresh before) (ha:∀k,before (arithmetic k)=[]):
    Runs program (timeBound points before buckets target) (.local 11 7) before (.local 14 9)
      (result points before buckets target):=by
  induction points generalizing before with
  | nil=>exact eof_trace before hi
  | cons p ps ih=>
    have h0:=One.source_trace before buckets p (Parse.records ps) target hi (oldFresh before hf) hs (hf 0)
      (headerFresh before hf) (childFresh before hf) ht (hf 13) (hf 12) (hf 10) (hf 11) (hf 18) (hf 19)
      ha
    let after:=One.result before buckets p (Parse.records ps) target
    have hi':after (aux .oldReader)=Parse.records ps:=OV.result_oldReader _ _ _ _ _
    have hs':after (aux .buckets)=Buckets.records buckets:=
      (OV.result_other _ _ _ _ _ _ (by intro j;fin_cases j <;> decide) (by decide) (by decide)
        (by decide) (by decide) (by decide)).trans hs
    have ht':after (aux .vertexKey)=target:=
      (OV.result_other _ _ _ _ _ _ (by intro j;fin_cases j <;> decide) (by decide) (by decide)
        (by decide) (by decide) (by decide)).trans ht
    have ha':∀k,after (arithmetic k)=[]:=by
      intro k
      exact (OV.result_other _ _ _ _ _ _ (by intro j;fin_cases j <;> simp [Early.role,arithmetic,aux])
        (by simp [arithmetic,aux]) (by simp [arithmetic,aux]) (by simp [arithmetic,aux])
        (by simp [arithmetic,aux]) (by simp [arithmetic,aux])).trans (ha k)
    exact join h0 (ih after hi' hs' ht' (fresh_step _ _ _ _ _ hf) ha')
end RiemannGaussian.SemiprimeD1StackChildGroupFactoryOldPortsLoop
