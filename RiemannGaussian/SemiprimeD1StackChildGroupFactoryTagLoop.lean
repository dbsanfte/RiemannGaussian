/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackChildGroupFactoryTagInnerView
import RiemannGaussian.SemiprimeD1StackChildGroupFactoryLeftPortsLoop
/-! # Entire actual nested first-index search through acquired bucket bytes
The real source parses each visited bucket header and child vector, stops at
its first actual match, or physically reaches outer EOF. No found bit, index,
permutation, decoded tag, scope or clock is a runtime operand.
-/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackChildGroupFactoryTagLoop
open SemiprimeD1StackChildGroupFactoryRoles SemiprimeD1StackChildGroupFactoryWiring
open SemiprimeD1StackChildGroupFactory SemiprimeD1StackChildGroupFactoryPrimitives
open SemiprimeD1StackProcedureTrace
namespace Inner
export SemiprimeD1StackChildGroupFactoryTagInner (found next result timeBound source_trace)
end Inner
namespace IV
export SemiprimeD1StackChildGroupFactoryTagInnerView (finalPosition result_other result_clean result_reader result_candidate result_position)
end IV
namespace Encoding
export SemiprimeD1StackChildGroupFactoryLeftPortsInner (records)
end Encoding
namespace Buckets
export SemiprimeD1StackChildGroupFactoryLeftPortsLoop (Bucket payload records)
end Buckets
namespace Parse
export SemiprimeD1StackChildGroupFactoryChildParse (cleanRoles)
end Parse
namespace Header
export SemiprimeD1StackChildGroupFactoryBucketHeader (result cleanRoles timeBound source_trace)
end Header
namespace Cleanup
export SemiprimeD1StackChildGroupFactoryChildCleanup (role)
end Cleanup
/-- Actual raw parsed-header boundary. -/
def head (before:Stack→List Bool) (b:Buckets.Bucket) (tail:List Bool):Stack→List Bool:=
  Header.result before (Encoding.records b.children) tail
/-- Exact actual one-bucket first-hit/exhaustion boundary. -/
def step (before:Stack→List Bool) (b:Buckets.Bucket) (tail target tag position:List Bool):Stack→List Bool:=
  Inner.result b.children (head before b tail) target tag position
/-- Both actual header and actually executed child-prefix clocks. -/
def stepTime (b:Buckets.Bucket) (target tag position:List Bool):Nat:=
  Header.timeBound b.packet (Encoding.records b.children) b.ports+Inner.timeBound b.children target tag position
/-- Real header+child source, with a next site computed by the actual child tests. -/
theorem step_trace (before:Stack→List Bool) (b:Buckets.Bucket) (tail target tag position:List Bool)
    (hi:before (aux .outerReader)=true::SemiprimeSourceHistogramKeyBits.frame (Buckets.payload b) tail)
    (hh:∀k∈Header.cleanRoles,before k=[]) (hz:∀k∈Parse.cleanRoles,before k=[])
    (ht:before (aux .vertexKey)=target) (htag:before (aux .tagWord)=tag)
    (hp:before (aux .localPosition)=position) (hcan:before (aux .candidateTag)=[])
    (hc:before (aux .copyScratch)=[]) (ha:∀k,before (arithmetic k)=[]):
    Runs program (stepTime b target tag position) (.local 11 28) before (Inner.next b.children target tag)
      (step before b tail target tag position):=by
  have h0:=Header.source_trace true before b.packet (Encoding.records b.children) b.ports tail hi hh
  change Runs program _ (.local 11 28) before (.local 12 9) (head before b tail) at h0
  have h1:=Inner.source_trace b.children (head before b tail) target tag position rfl
    (by simpa [head,Header.result,Parse.cleanRoles,aux,field] using hz)
    (by simpa [head,Header.result,aux] using ht) (by simpa [head,Header.result,aux] using htag)
    (by simpa [head,Header.result,aux] using hp) (by simpa [head,Header.result,aux] using hcan)
    (by simpa [head,Header.result,aux] using hc) (by intro k;simpa [head,Header.result,aux,arithmetic] using ha k)
  exact join h0 h1
/-- Complete actual cache retention outside child/search data and both readers. -/
theorem step_other (before:Stack→List Bool) (b:Buckets.Bucket) (tail target tag position:List Bool) (k:Stack)
    (hf:∀j,Cleanup.role j≠k) (he:k≠aux .endpointReader) (ho:k≠aux .outerReader)
    (hcan:k≠aux .candidateTag) (hp:k≠aux .localPosition):step before b tail target tag position k=before k:=by
  rw [step,IV.result_other _ _ _ _ _ k hf he hcan hp]
  simp only [head,Header.result,Function.update_of_ne he,Function.update_of_ne ho]
/-- Actual current outer suffix, even at an early hit where it will be physically drained later. -/
theorem step_outerReader (before:Stack→List Bool) (b:Buckets.Bucket) (tail target tag position:List Bool):
    step before b tail target tag position (aux .outerReader)=tail:=by
  rw [step,IV.result_other _ _ _ _ _ _ (by intro j;fin_cases j <;> decide) (by decide) (by decide) (by decide)]
  rfl
/-- Exact physically computed local position after this actual bucket prefix. -/
theorem step_position (before:Stack→List Bool) (b:Buckets.Bucket) (tail target tag position:List Bool)
    (hp:before (aux .localPosition)=position):
    step before b tail target tag position (aux .localPosition)=IV.finalPosition b.children target tag position:=by
  exact IV.result_position _ _ _ _ _ (by simpa [head,Header.result,aux] using hp)
/-- Only actual exhausted buckets promise child-parser freshness. -/
theorem step_clean (before:Stack→List Bool) (b:Buckets.Bucket) (tail target tag position:List Bool)
    (hz:∀k∈Parse.cleanRoles,before k=[]) (hf:Inner.found b.children target tag=false):
    ∀k∈Parse.cleanRoles,step before b tail target tag position k=[]:=by
  apply IV.result_clean
  · simpa [head,Header.result,Parse.cleanRoles,aux,field] using hz
  · exact hf
/-- Only actual exhausted buckets promise a fresh temporary candidate tag. -/
theorem step_candidate (before:Stack→List Bool) (b:Buckets.Bucket) (tail target tag position:List Bool)
    (hc:before (aux .candidateTag)=[]) (hf:Inner.found b.children target tag=false):
    step before b tail target tag position (aux .candidateTag)=[]:=by
  exact IV.result_candidate _ _ _ _ _ (by simpa [head,Header.result,aux] using hc) hf
/-- Only actual exhausted buckets promise every header/parser destination is fresh again. -/
theorem step_headerClean (before:Stack→List Bool) (b:Buckets.Bucket) (tail target tag position:List Bool)
    (hh:∀k∈Header.cleanRoles,before k=[]) (hf:Inner.found b.children target tag=false):
    ∀k∈Header.cleanRoles,step before b tail target tag position k=[]:=by
  intro k hk
  simp only [Header.cleanRoles,List.mem_cons,List.not_mem_nil,or_false] at hk
  rcases hk with rfl|rfl|rfl|rfl|rfl|rfl
  · exact (step_other _ _ _ _ _ _ _ (by intro j;fin_cases j <;> decide) (by decide) (by decide) (by decide) (by decide)).trans
      (hh _ (by simp [Header.cleanRoles]))
  · exact (step_other _ _ _ _ _ _ _ (by intro j;fin_cases j <;> decide) (by decide) (by decide) (by decide) (by decide)).trans
      (hh _ (by simp [Header.cleanRoles]))
  · exact IV.result_reader _ _ _ _ _ hf
  all_goals
    exact (step_other _ _ _ _ _ _ _ (by intro j;fin_cases j <;> decide) (by decide) (by decide) (by decide) (by decide)).trans
      (hh _ (by simp [Header.cleanRoles]))
/-- The actual first-hit outcome of the complete physical nested scan. -/
def found:List Buckets.Bucket→List Bool→List Bool→Bool
  | [],_,_=>false
  | b::bs,target,tag=>if Inner.found b.children target tag=true then true else found bs target tag
/-- Actual literal found/exhausted search continuation. -/
def next (buckets:List Buckets.Bucket) (target tag:List Bool):Label:=
  if found buckets target tag=true then .local 13 19 else .local 13 31
/-- Physical outer EOF consumes its real terminator and tests actual EOF. -/
def atEOF (before:Stack→List Bool):Stack→List Bool:=Function.update before (aux .outerReader) []
/-- Full actual short-circuit or physical-EOF bank of the complete search. -/
def result:List Buckets.Bucket→(Stack→List Bool)→List Bool→List Bool→List Bool→Stack→List Bool
  | [],before,_,_,_=>atEOF before
  | b::bs,before,target,tag,position=>if Inner.found b.children target tag=true then step before b (Buckets.records bs) target tag position
    else result bs (step before b (Buckets.records bs) target tag position) target tag (IV.finalPosition b.children target tag position)
/-- Sum only actually executed bucket/child-prefix clocks and two actual final EOF instructions. -/
def timeBound:List Buckets.Bucket→List Bool→List Bool→List Bool→Nat
  | [],_,_,_=>2
  | b::bs,target,tag,position=>stepTime b target tag position+
      if Inner.found b.children target tag=true then 0 else timeBound bs target tag (IV.finalPosition b.children target tag position)
/-- Exact real outer-EOF instructions before copying the computed missing-index answer. -/
theorem eof_trace (before:Stack→List Bool) (ho:before (aux .outerReader)=[false]):
    Runs program 2 (.local 11 28) before (.local 13 31) (atEOF before):=by
  have h0:=pop_run (.local 11 28) abort (.local 11 29) (.local 11 30) (aux .outerReader) before [false] rfl ho
  simp only [List.head?_cons,List.tail_cons,SemiprimeD1StackBytecode.choose] at h0
  have h1:=peek_run (.local 11 29) (.local 13 31) abort abort (aux .outerReader) (atEOF before) [] rfl (Function.update_self _ _ _)
  simp only [List.head?_nil,SemiprimeD1StackBytecode.choose] at h1
  exact join h0 h1
/-- Whole actual first-index nested search, from real framed bucket bytes alone. -/
theorem source_trace (buckets:List Buckets.Bucket) (before:Stack→List Bool) (target tag position:List Bool)
    (hi:before (aux .outerReader)=Buckets.records buckets)
    (hh:∀k∈Header.cleanRoles,before k=[]) (hz:∀k∈Parse.cleanRoles,before k=[])
    (ht:before (aux .vertexKey)=target) (htag:before (aux .tagWord)=tag)
    (hp:before (aux .localPosition)=position) (hcan:before (aux .candidateTag)=[])
    (hc:before (aux .copyScratch)=[]) (ha:∀k,before (arithmetic k)=[]):
    Runs program (timeBound buckets target tag position) (.local 11 28) before (next buckets target tag)
      (result buckets before target tag position):=by
  induction buckets generalizing before position with
  | nil=>simpa only [timeBound,next,found,Bool.false_eq_true,ite_false,result] using eof_trace before hi
  | cons b bs ih=>
    have h0:=step_trace before b (Buckets.records bs) target tag position hi hh hz ht htag hp hcan hc ha
    by_cases hf:Inner.found b.children target tag=true
    · have h0':Runs program (stepTime b target tag position) (.local 11 28) before (.local 13 19)
          (step before b (Buckets.records bs) target tag position):=by simpa only [Inner.next,hf,ite_true] using h0
      simpa [timeBound,result,found,next,hf] using h0'
    · have hnf:Inner.found b.children target tag=false:=by
        cases hval:Inner.found b.children target tag with
        | false=>rfl
        | true=>exact False.elim (hf hval)
      have h0':Runs program (stepTime b target tag position) (.local 11 28) before (.local 11 28)
          (step before b (Buckets.records bs) target tag position):=by simpa only [Inner.next,hf,Bool.false_eq_true,ite_false] using h0
      let after:=step before b (Buckets.records bs) target tag position
      have hi':after (aux .outerReader)=Buckets.records bs:=step_outerReader _ _ _ _ _ _
      have hh':∀k∈Header.cleanRoles,after k=[]:=step_headerClean _ _ _ _ _ _ hh hnf
      have hz':∀k∈Parse.cleanRoles,after k=[]:=step_clean _ _ _ _ _ _ hz hnf
      have ht':after (aux .vertexKey)=target:=
        (step_other _ _ _ _ _ _ _ (by intro j;fin_cases j <;> decide) (by decide) (by decide) (by decide) (by decide)).trans ht
      have htag':after (aux .tagWord)=tag:=
        (step_other _ _ _ _ _ _ _ (by intro j;fin_cases j <;> decide) (by decide) (by decide) (by decide) (by decide)).trans htag
      have hp':after (aux .localPosition)=IV.finalPosition b.children target tag position:=step_position _ _ _ _ _ _ hp
      have hcan':after (aux .candidateTag)=[]:=step_candidate _ _ _ _ _ _ hcan hnf
      have hc':after (aux .copyScratch)=[]:=
        (step_other _ _ _ _ _ _ _ (by intro j;fin_cases j <;> decide) (by decide) (by decide) (by decide) (by decide)).trans hc
      have ha':∀k,after (arithmetic k)=[]:=by
        intro k
        exact (step_other _ _ _ _ _ _ _ (by intro j;fin_cases j <;> simp [Cleanup.role,arithmetic,aux])
          (by simp [arithmetic,aux]) (by simp [arithmetic,aux]) (by simp [arithmetic,aux]) (by simp [arithmetic,aux])).trans (ha k)
      have h1:=ih after (IV.finalPosition b.children target tag position) hi' hh' hz' ht' htag' hp' hcan' hc' ha'
      have hwhole:=join h0' h1
      simpa only [timeBound,result,found,hf,Bool.false_eq_true,ite_false,next] using hwhole
end RiemannGaussian.SemiprimeD1StackChildGroupFactoryTagLoop
