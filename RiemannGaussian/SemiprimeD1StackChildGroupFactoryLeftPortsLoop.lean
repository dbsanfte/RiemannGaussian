/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackChildGroupFactoryLeftPortsInner
import RiemannGaussian.SemiprimeD1StackChildGroupFactoryBucketHeader
/-! # Entire actual nested bucket filter for one old vertex
Every actual bucket header and child vector is scanned in exact packet-major
order. Empty buckets remain real parsed records. No adjacency/order is supplied.
-/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackChildGroupFactoryLeftPortsLoop
open SemiprimeD1StackChildGroupFactoryRoles SemiprimeD1StackChildGroupFactoryWiring
open SemiprimeD1StackChildGroupFactory SemiprimeD1StackChildGroupFactoryPrimitives
open SemiprimeD1StackProcedureTrace
namespace Inner
export SemiprimeD1StackChildGroupFactoryLeftPortsInner
  (Child records portWords result timeBound source_trace result_reader result_other result_clean result_portHistory)
end Inner
namespace Parse
export SemiprimeD1StackChildGroupFactoryChildParse (cleanRoles)
end Parse
namespace Cleanup
export SemiprimeD1StackChildGroupFactoryChildCleanup (role)
end Cleanup
namespace Header
export SemiprimeD1StackChildGroupFactoryBucketHeader (pc cleanRoles result timeBound source_trace)
end Header
open SemiprimeSourceHistogramKeyBits (frame)
/-- Proof interpretation of an actual parsed three-field bucket, never an input host structure. -/
structure Bucket where
  /-- Whole observed raw packet key, retaining its padding. -/
  packet:List Bool
  /-- Actual ordered acquired children of this packet. -/
  children:List Inner.Child
  /-- Actual unary canonical right-port tape. -/
  ports:List Bool
/-- Exact actual nested bucket payload. -/
def payload (b:Bucket):List Bool:=
  SemiprimeD1StackChildGroupFactoryBucketRecord.payload b.packet (Inner.records b.children) b.ports
/-- Actual outer bucket-vector grammar. -/
def records:List Bucket→List Bool
  | []=>[false]
  | b::bs=>true::frame (payload b) (records bs)
/-- Exact actual left-port words in packet-major child order, retaining repeated prepared buckets. -/
def portWords:List Bucket→List Bool→List (List Bool)
  | [],_=>[]
  | b::bs,target=>Inner.portWords b.children target++portWords bs target
/-- Actual parsed header boundary, before reading the child vector. -/
def head (before:Stack→List Bool) (b:Bucket) (tail:List Bool):Stack→List Bool:=
  Header.result before (Inner.records b.children) tail
/-- Complete actual one-bucket scan boundary. -/
def step (before:Stack→List Bool) (b:Bucket) (tail target:List Bool):Stack→List Bool:=
  Inner.result b.children (head before b tail) target
/-- Literal header parse/drains and the entire actual child scan. -/
def stepTime (b:Bucket) (target:List Bool):Nat:=
  Header.timeBound b.packet (Inner.records b.children) b.ports+Inner.timeBound b.children target
/-- Actual one-bucket source path including empty observed buckets. -/
theorem step_trace (before:Stack→List Bool) (b:Bucket) (tail target:List Bool)
    (hi:before (aux .outerReader)=true::frame (payload b) tail)
    (hh:∀k∈Header.cleanRoles,before k=[]) (hz:∀k∈Parse.cleanRoles,before k=[])
    (ht:before (aux .vertexKey)=target) (hb:before (aux .frameBuffer)=[])
    (hc:before (aux .copyScratch)=[]) (ha:∀k,before (arithmetic k)=[]):
    Runs program (stepTime b target) (.local 9 7) before (.local 9 7) (step before b tail target):=by
  have h0:=Header.source_trace false before b.packet (Inner.records b.children) b.ports tail hi hh
  change Runs program _ (.local 9 7) before (.local 9 20) (head before b tail) at h0
  have h1:=Inner.source_trace b.children (head before b tail) target rfl
    (by simpa [head,Header.result,Parse.cleanRoles,aux,field] using hz)
    (by simpa [head,Header.result,aux] using ht) (by simpa [head,Header.result,aux] using hb)
    (by simpa [head,Header.result,aux] using hc) (by intro k;simpa [head,Header.result,aux,arithmetic] using ha k)
  exact join h0 h1
/-- Complete actual per-bucket retention outside real child fields, both readers and the port log. -/
theorem step_other (before:Stack→List Bool) (b:Bucket) (tail target:List Bool) (k:Stack)
    (hf:∀j,Cleanup.role j≠k) (he:k≠aux .endpointReader) (ho:k≠aux .outerReader) (hp:k≠aux .portHistory):
    step before b tail target k=before k:=by
  rw [step,Inner.result_other _ _ _ k hf he hp]
  simp only [head,Header.result,Function.update_of_ne he,Function.update_of_ne ho]
/-- Actual outer suffix is retained during the complete child scan. -/
theorem step_outerReader (before:Stack→List Bool) (b:Bucket) (tail target:List Bool):
    step before b tail target (aux .outerReader)=tail:=by
  rw [step,Inner.result_other _ _ _ _ (by intro j;fin_cases j <;> decide) (by decide) (by decide)]
  rfl
/-- Actual child reader is empty at the next bucket. -/
theorem step_endpointReader (before:Stack→List Bool) (b:Bucket) (tail target:List Bool):
    step before b tail target (aux .endpointReader)=[]:=Inner.result_reader _ _ _
/-- Every child parser/private role is restored at the per-bucket boundary. -/
theorem step_clean (before:Stack→List Bool) (b:Bucket) (tail target:List Bool)
    (hz:∀k∈Parse.cleanRoles,before k=[]):∀k∈Parse.cleanRoles,step before b tail target k=[]:=by
  apply Inner.result_clean
  simpa [head,Header.result,Parse.cleanRoles,aux,field] using hz
/-- Every actual header destination/parser role is ready for the next outer bucket. -/
theorem step_headerClean (before:Stack→List Bool) (b:Bucket) (tail target:List Bool)
    (hh:∀k∈Header.cleanRoles,before k=[]):∀k∈Header.cleanRoles,step before b tail target k=[]:=by
  intro k hk
  simp only [Header.cleanRoles,List.mem_cons,List.not_mem_nil,or_false] at hk
  rcases hk with rfl|rfl|rfl|rfl|rfl|rfl
  · exact (step_other _ _ _ _ _ (by intro j;fin_cases j <;> decide) (by decide) (by decide) (by decide)).trans
      (hh _ (by simp [Header.cleanRoles]))
  · exact (step_other _ _ _ _ _ (by intro j;fin_cases j <;> decide) (by decide) (by decide) (by decide)).trans
      (hh _ (by simp [Header.cleanRoles]))
  · exact step_endpointReader _ _ _ _
  all_goals
    exact (step_other _ _ _ _ _ (by intro j;fin_cases j <;> decide) (by decide) (by decide) (by decide)).trans
      (hh _ (by simp [Header.cleanRoles]))
/-- Physical outer EOF consumes the actual FALSE before its final EOF peek. -/
def atEOF (before:Stack→List Bool):Stack→List Bool:=Function.update before (aux .outerReader) []
/-- Entire actual nested scan bank. -/
def result:List Bucket→(Stack→List Bool)→List Bool→Stack→List Bool
  | [],before,_=>atEOF before
  | b::bs,before,target=>result bs (step before b (records bs) target) target
/-- Whole actual header and child-source clock, including real final EOF instructions. -/
def timeBound:List Bucket→List Bool→Nat
  | [],_=>2
  | b::bs,target=>stepTime b target+timeBound bs target
/-- Exact two actual EOF instructions at the outer bucket boundary. -/
theorem eof_run (before:Stack→List Bool) (ho:before (aux .outerReader)=[false]):
    Runs program 2 (.local 9 7) before (.local 10 18) (atEOF before):=by
  have h0:=pop_run (.local 9 7) abort (.local 9 8) (.local 9 9) (aux .outerReader) before [false] rfl ho
  simp only [List.head?_cons,List.tail_cons,SemiprimeD1StackBytecode.choose] at h0
  have h1:=peek_run (.local 9 8) (.local 10 18) abort abort (aux .outerReader) (atEOF before) [] rfl
    (Function.update_self _ _ _)
  simp only [List.head?_nil,SemiprimeD1StackBytecode.choose] at h1
  exact join h0 h1
/-- Entire actual nested scan, with every header/child call, cleanup and real return counted. -/
theorem source_trace (buckets:List Bucket) (before:Stack→List Bool) (target:List Bool)
    (hi:before (aux .outerReader)=records buckets)
    (hh:∀k∈Header.cleanRoles,before k=[]) (hz:∀k∈Parse.cleanRoles,before k=[])
    (ht:before (aux .vertexKey)=target) (hb:before (aux .frameBuffer)=[])
    (hc:before (aux .copyScratch)=[]) (ha:∀k,before (arithmetic k)=[]):
    Runs program (timeBound buckets target) (.local 9 7) before (.local 10 18) (result buckets before target):=by
  induction buckets generalizing before with
  | nil=>exact eof_run before hi
  | cons b bs ih=>
    have h0:=step_trace before b (records bs) target hi hh hz ht hb hc ha
    let after:=step before b (records bs) target
    have hi':after (aux .outerReader)=records bs:=step_outerReader _ _ _ _
    have hh':∀k∈Header.cleanRoles,after k=[]:=step_headerClean _ _ _ _ hh
    have hz':∀k∈Parse.cleanRoles,after k=[]:=step_clean _ _ _ _ hz
    have ht':after (aux .vertexKey)=target:=
      (step_other _ _ _ _ _ (by intro j;fin_cases j <;> decide) (by decide) (by decide) (by decide)).trans ht
    have hb':after (aux .frameBuffer)=[]:=
      (step_other _ _ _ _ _ (by intro j;fin_cases j <;> decide) (by decide) (by decide) (by decide)).trans hb
    have hc':after (aux .copyScratch)=[]:=
      (step_other _ _ _ _ _ (by intro j;fin_cases j <;> decide) (by decide) (by decide) (by decide)).trans hc
    have ha':∀k,after (arithmetic k)=[]:=by
      intro k
      exact (step_other _ _ _ _ _ (by intro j;fin_cases j <;> simp [Cleanup.role,arithmetic,aux])
        (by simp [arithmetic,aux]) (by simp [arithmetic,aux]) (by simp [arithmetic,aux])).trans (ha k)
    exact join h0 (ih after hi' hh' hz' ht' hb' hc' ha')
end RiemannGaussian.SemiprimeD1StackChildGroupFactoryLeftPortsLoop
