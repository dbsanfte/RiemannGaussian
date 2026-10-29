/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackChildGroupFactoryLeftPortVisitView
/-! # Entire actual child-vector filter for one old vertex's left ports
The actual numeric vertex test reads every physical six-field child endpoint.
Only its physically parsed global-ID word contributes to the real port log.
-/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackChildGroupFactoryLeftPortsInner
open SemiprimeD1StackChildGroupFactoryRoles SemiprimeD1StackChildGroupFactoryWiring
open SemiprimeD1StackChildGroupFactory SemiprimeD1StackChildGroupFactoryPrimitives
open SemiprimeD1StackProcedureTrace
namespace Visit
export SemiprimeD1StackChildGroupFactoryLeftPortVisit (result timeBound source_trace)
end Visit
namespace View
export SemiprimeD1StackChildGroupFactoryLeftPortVisitView (result_reader result_clean result_other result_portHistory)
end View
namespace Parse
export SemiprimeD1StackChildGroupFactoryBucketParse (Endpoint)
export SemiprimeD1StackChildGroupFactoryChildParse (cleanRoles)
end Parse
namespace Cleanup
export SemiprimeD1StackChildGroupFactoryChildCleanup (role)
end Cleanup
namespace Log
export SemiprimeD1StackChildGroupFactoryWordLog (row)
end Log
open SemiprimeSourceHistogramKeyBits (frame)
open SemiprimeBitArithmetic (bitValue)
/-- Proof interpretation of the six actual words: original endpoint and its actual child-global ID. -/
abbrev Child:=Parse.Endpoint×List Bool
/-- Exact nested child endpoint vector grammar. -/
def records:List Child→List Bool
  | []=>[false]
  | p::ps=>true::frame (SemiprimeD1StackChildGroupFactoryBucketEmit.payload p.1 p.2) (records ps)
/-- The actual numeric-matching global-ID words, in exact physical child order. -/
def portWords:List Child→List Bool→List (List Bool)
  | [],_=>[]
  | p::ps,target=>if bitValue p.1.vertex=bitValue target then p.2::portWords ps target else portWords ps target
/-- Physical EOF consumes the actual FALSE before returning to the outer bucket scan. -/
def atEOF (before:Stack→List Bool):Stack→List Bool:=Function.update before (aux .endpointReader) []
/-- Full actual repeated-filter bank. -/
def result:List Child→(Stack→List Bool)→List Bool→Stack→List Bool
  | [],before,_=>atEOF before
  | p::ps,before,target=>result ps (Visit.result before p.1 p.2 (records ps) target) target
/-- Own sum of complete literal child visits and the two actual final EOF instructions. -/
def timeBound:List Child→List Bool→Nat
  | [],_=>2
  | p::ps,target=>Visit.timeBound p.1 p.2 target+timeBound ps target
/-- Exact terminating instruction pair. -/
theorem eof_run (before:Stack→List Bool) (hr:before (aux .endpointReader)=[false]):
    Runs program 2 (.local 9 20) before (.local 9 7) (atEOF before):=by
  have h0:=pop_run (.local 9 20) abort (.local 9 21) (.local 9 22) (aux .endpointReader) before [false] rfl hr
  simp only [List.head?_cons,List.tail_cons,SemiprimeD1StackBytecode.choose] at h0
  have h1:=peek_run (.local 9 21) (.local 9 7) abort abort (aux .endpointReader) (atEOF before) [] rfl
    (Function.update_self _ _ _)
  simp only [List.head?_nil,SemiprimeD1StackBytecode.choose] at h1
  exact join h0 h1
/-- Entire actual child vector, with real padded-key numeric equality and all fresh roles restored. -/
theorem source_trace (children:List Child) (before:Stack→List Bool) (target:List Bool)
    (hi:before (aux .endpointReader)=records children) (hz:∀k∈Parse.cleanRoles,before k=[])
    (ht:before (aux .vertexKey)=target) (hb:before (aux .frameBuffer)=[])
    (hc:before (aux .copyScratch)=[]) (ha:∀k,before (arithmetic k)=[]):
    Runs program (timeBound children target) (.local 9 20) before (.local 9 7) (result children before target):=by
  induction children generalizing before with
  | nil=>exact eof_run before hi
  | cons p ps ih=>
    have h0:=Visit.source_trace before p.1 p.2 (records ps) target hi hz ht hb hc ha
    let after:=Visit.result before p.1 p.2 (records ps) target
    have hi':after (aux .endpointReader)=records ps:=View.result_reader _ _ _ _ _
    have hz':∀k∈Parse.cleanRoles,after k=[]:=View.result_clean _ _ _ _ _ hz
    have ht':after (aux .vertexKey)=target:=
      (View.result_other _ _ _ _ _ _ (by intro j;fin_cases j <;> decide) (by decide) (by decide)).trans ht
    have hb':after (aux .frameBuffer)=[]:=
      (View.result_other _ _ _ _ _ _ (by intro j;fin_cases j <;> decide) (by decide) (by decide)).trans hb
    have hc':after (aux .copyScratch)=[]:=
      (View.result_other _ _ _ _ _ _ (by intro j;fin_cases j <;> decide) (by decide) (by decide)).trans hc
    have ha':∀k,after (arithmetic k)=[]:=by
      intro k
      exact (View.result_other _ _ _ _ _ _ (by intro j;fin_cases j <;> simp [Cleanup.role,arithmetic,aux])
        (by simp [arithmetic,aux]) (by simp [arithmetic,aux])).trans (ha k)
    exact join h0 (ih after hi' hz' ht' hb' hc' ha')
/-- Every nested child scan leaves its actual reader physically empty. -/
theorem result_reader (children:List Child) (before:Stack→List Bool) (target:List Bool):
    result children before target (aux .endpointReader)=[]:=by
  induction children generalizing before with
  | nil=>rfl
  | cons p ps ih=>exact ih _
/-- Full actual cache retention outside the six child fields, reader and selected port log. -/
theorem result_other (children:List Child) (before:Stack→List Bool) (target:List Bool) (k:Stack)
    (hf:∀j,Cleanup.role j≠k) (hr:k≠aux .endpointReader) (hh:k≠aux .portHistory):
    result children before target k=before k:=by
  induction children generalizing before with
  | nil=>simp only [result,atEOF,Function.update_of_ne hr]
  | cons p ps ih=>rw [result,ih];exact View.result_other _ _ _ _ _ _ hf hr hh
/-- All actual parser and raw fields remain fresh at the whole inner-loop boundary. -/
theorem result_clean (children:List Child) (before:Stack→List Bool) (target:List Bool)
    (hz:∀k∈Parse.cleanRoles,before k=[]):
    ∀k∈Parse.cleanRoles,result children before target k=[]:=by
  induction children generalizing before with
  | nil=>
    intro k hk
    have hn:k≠aux .endpointReader:=by
      intro he;subst k;simp [Parse.cleanRoles,aux,field] at hk
    simpa only [result,atEOF,Function.update_of_ne hn] using hz k hk
  | cons p ps ih=>exact ih _ (View.result_clean _ _ _ _ _ hz)
/-- Exact ordered selected port history; no sorting/permutation answer is an input. -/
theorem result_portHistory (children:List Child) (before:Stack→List Bool) (target:List Bool):
    result children before target (aux .portHistory)=
      ((portWords children target).flatMap Log.row).reverse++before (aux .portHistory):=by
  induction children generalizing before with
  | nil=>simp only [result,atEOF,portWords,List.flatMap_nil,List.reverse_nil,List.nil_append];rfl
  | cons p ps ih=>
    rw [result,ih,View.result_portHistory]
    by_cases h:bitValue p.1.vertex=bitValue target <;>
      simp [portWords,h,List.reverse_append,List.append_assoc]
end RiemannGaussian.SemiprimeD1StackChildGroupFactoryLeftPortsInner
