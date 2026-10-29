/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackChildGroupFactoryTagVisitView
import RiemannGaussian.SemiprimeD1StackChildGroupFactoryLeftPortsInner
/-! # Actual first-match child-vector search with a physical binary local counter
The actual source stops at its first whole-tag match. At physical child EOF it
returns to the outer bucket scan. Predicates/results below are specifications
of actual bytes and source branches, never runtime verdict/counter suppliers.
-/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackChildGroupFactoryTagInner
open SemiprimeD1StackChildGroupFactoryRoles SemiprimeD1StackChildGroupFactoryWiring
open SemiprimeD1StackChildGroupFactory SemiprimeD1StackChildGroupFactoryPrimitives
open SemiprimeD1StackProcedureTrace
namespace Visit
export SemiprimeD1StackChildGroupFactoryTagVisit (next candidate result timeBound source_trace)
end Visit
namespace View
export SemiprimeD1StackChildGroupFactoryTagVisitView
  (hit advance result_reader result_clean result_other result_position result_candidate)
end View
namespace Parse
export SemiprimeD1StackChildGroupFactoryChildParse (cleanRoles)
end Parse
namespace Encoding
export SemiprimeD1StackChildGroupFactoryLeftPortsInner (Child records)
end Encoding
namespace Cleanup
export SemiprimeD1StackChildGroupFactoryChildCleanup (role)
end Cleanup
open SemiprimeBitArithmetic (bitValue)
/-- Constructive decidability of the actual numeric-vertex/literal-tag test. -/
instance hitDecidable (e:SemiprimeD1StackChildGroupFactoryBucketParse.Endpoint) (target tag:List Bool):
    Decidable (View.hit e target tag):=
  inferInstanceAs (Decidable (bitValue e.vertex=bitValue target ∧ tag=Visit.candidate e))
/-- Whether actual numeric-vertex/literal-tag source tests find a match before physical EOF. -/
def found:List Encoding.Child→List Bool→List Bool→Bool
  | [],_,_=>false
  | p::ps,target,tag=>if View.hit p.1 target tag then true else found ps target tag
/-- Actual real found or exhausted-child continuation, chosen by actual source tests. -/
def next (children:List Encoding.Child) (target tag:List Bool):Label:=
  if found children target tag=true then .local 13 19 else .local 11 28
/-- The actual child EOF pop/peek leaves its reader empty. -/
def atEOF (before:Stack→List Bool):Stack→List Bool:=Function.update before (aux .endpointReader) []
/-- Full physical bank at the actual first-hit or exhausted-child boundary. -/
def result:List Encoding.Child→(Stack→List Bool)→List Bool→List Bool→List Bool→Stack→List Bool
  | [],before,_,_,_=>atEOF before
  | p::ps,before,target,tag,position=>if View.hit p.1 target tag then
      Visit.result before p.1 p.2 (Encoding.records ps) target tag position
    else result ps (Visit.result before p.1 p.2 (Encoding.records ps) target tag position)
      target tag (View.advance p.1 target position)
/-- Only the actual executed prefix is paid; no later child is visited after a real hit. -/
def timeBound:List Encoding.Child→List Bool→List Bool→List Bool→Nat
  | [],_,_,_=>2
  | p::ps,target,tag,position=>Visit.timeBound p.1 p.2 target tag position+
      if View.hit p.1 target tag then 0 else timeBound ps target tag (View.advance p.1 target position)
/-- Exact real child-EOF instructions before the next outer bucket. -/
theorem eof_trace (before:Stack→List Bool) (hr:before (aux .endpointReader)=[false]):
    Runs program 2 (.local 12 9) before (.local 11 28) (atEOF before):=by
  have h0:=pop_run (.local 12 9) abort (.local 12 10) (.local 12 11) (aux .endpointReader) before [false] rfl hr
  simp only [List.head?_cons,List.tail_cons,SemiprimeD1StackBytecode.choose] at h0
  have h1:=peek_run (.local 12 10) (.local 11 28) abort abort (aux .endpointReader) (atEOF before) [] rfl
    (Function.update_self _ _ _)
  simp only [List.head?_nil,SemiprimeD1StackBytecode.choose] at h1
  exact join h0 h1
/-- Entire actual first-match child scan, preserving every real outer return frame. -/
theorem source_trace (children:List Encoding.Child) (before:Stack→List Bool) (target tag position:List Bool)
    (hi:before (aux .endpointReader)=Encoding.records children)
    (hz:∀k∈Parse.cleanRoles,before k=[])
    (ht:before (aux .vertexKey)=target) (htag:before (aux .tagWord)=tag)
    (hp:before (aux .localPosition)=position) (hcan:before (aux .candidateTag)=[])
    (hc:before (aux .copyScratch)=[]) (ha:∀k,before (arithmetic k)=[]):
    Runs program (timeBound children target tag position) (.local 12 9) before (next children target tag)
      (result children before target tag position):=by
  induction children generalizing before position with
  | nil=>simpa only [timeBound,next,found,Bool.false_eq_true,ite_false,result] using eof_trace before hi
  | cons p ps ih=>
    have h0:=Visit.source_trace before p.1 p.2 (Encoding.records ps) target tag position hi hz ht htag hp hcan hc ha
    by_cases h:View.hit p.1 target tag
    · have hh:bitValue p.1.vertex=bitValue target ∧ tag=Visit.candidate p.1:=h
      have h0':Runs program (Visit.timeBound p.1 p.2 target tag position) (.local 12 9) before (.local 13 19)
          (Visit.result before p.1 p.2 (Encoding.records ps) target tag position):=by
        simpa [Visit.next,hh] using h0
      simpa [timeBound,result,found,h,next] using h0'
    · have hh:¬(bitValue p.1.vertex=bitValue target ∧ tag=Visit.candidate p.1):=h
      have h0':Runs program (Visit.timeBound p.1 p.2 target tag position) (.local 12 9) before (.local 12 9)
          (Visit.result before p.1 p.2 (Encoding.records ps) target tag position):=by
        simpa only [Visit.next,hh,ite_false] using h0
      let after:=Visit.result before p.1 p.2 (Encoding.records ps) target tag position
      have hi':after (aux .endpointReader)=Encoding.records ps:=View.result_reader _ _ _ _ _ _ _ h
      have hz':∀k∈Parse.cleanRoles,after k=[]:=View.result_clean _ _ _ _ _ _ _ hz h
      have ht':after (aux .vertexKey)=target:=
        (View.result_other _ _ _ _ _ _ _ _ (by intro j;fin_cases j <;> decide) (by decide) (by decide) (by decide)).trans ht
      have htag':after (aux .tagWord)=tag:=
        (View.result_other _ _ _ _ _ _ _ _ (by intro j;fin_cases j <;> decide) (by decide) (by decide) (by decide)).trans htag
      have hp':after (aux .localPosition)=View.advance p.1 target position:=View.result_position _ _ _ _ _ _ _ hp h
      have hcan':after (aux .candidateTag)=[]:=View.result_candidate _ _ _ _ _ _ _ hcan h
      have hc':after (aux .copyScratch)=[]:=
        (View.result_other _ _ _ _ _ _ _ _ (by intro j;fin_cases j <;> decide) (by decide) (by decide) (by decide)).trans hc
      have ha':∀k,after (arithmetic k)=[]:=by
        intro k
        exact (View.result_other _ _ _ _ _ _ _ _ (by intro j;fin_cases j <;> simp [Cleanup.role,arithmetic,aux])
          (by simp [arithmetic,aux]) (by simp [arithmetic,aux]) (by simp [arithmetic,aux])).trans (ha k)
      have h1:=ih after (View.advance p.1 target position) hi' hz' ht' htag' hp' hcan' hc' ha'
      have hwhole:=join h0' h1
      simpa only [timeBound,result,found,h,ite_false,next] using hwhole
end RiemannGaussian.SemiprimeD1StackChildGroupFactoryTagInner
