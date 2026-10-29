/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackChildGroupFactoryBucketVisitView
/-! # Entire actual EOF-bounded endpoint scan for one observed raw packet
The real scan visits the physical endpoint vector once and assigns actual fresh
binary positions to exactly its literal raw-packet matches. Empty buckets are valid.
-/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackChildGroupFactoryBucketLoop
open SemiprimeD1StackChildGroupFactoryRoles SemiprimeD1StackChildGroupFactoryWiring
open SemiprimeD1StackChildGroupFactory SemiprimeD1StackChildGroupFactoryPrimitives
open SemiprimeD1StackProcedureTrace
namespace Visit
export SemiprimeD1StackChildGroupFactoryBucketVisit (result timeBound source_trace)
end Visit
namespace View
export SemiprimeD1StackChildGroupFactoryBucketVisitView (nextPosition result_reader result_position result_clean result_other)
end View
namespace Parse
export SemiprimeD1StackChildGroupFactoryBucketParse (Endpoint cleanRoles records)
end Parse
namespace Cleanup
export SemiprimeD1StackChildGroupFactoryBucketCleanup (role)
end Cleanup
/-- Physical source EOF consumes the actual terminating FALSE and tests that no suffix remains. -/
def atEOF (before:Stack→List Bool):Stack→List Bool:=Function.update before (aux .endpointReader) []
/-- Full actual scan result, carrying its physically incremented binary position. -/
def result:List Parse.Endpoint→(Stack→List Bool)→List Bool→List Bool→Stack→List Bool
  | [],before,_,_=>atEOF before
  | e::es,before,packet,position=>result es
      (Visit.result before e (Parse.records es) packet position) packet (View.nextPosition e packet position)
/-- Whole own trace sum, with exactly one real EOF pop and one real EOF peek at termination. -/
def timeBound:List Parse.Endpoint→List Bool→List Bool→Nat
  | [],_,_=>2
  | e::es,packet,position=>Visit.timeBound e packet position+timeBound es packet (View.nextPosition e packet position)
/-- Actual terminating instruction pair. -/
theorem eof_run (before:Stack→List Bool) (hr:before (aux .endpointReader)=[false]):
    Runs program 2 (.local 6 23) before (.local 8 4) (atEOF before):=by
  have h0:=pop_run (.local 6 23) abort (.local 6 24) (.local 6 25) (aux .endpointReader) before [false] rfl hr
  simp only [List.head?_cons,List.tail_cons,SemiprimeD1StackBytecode.choose] at h0
  have h1:=peek_run (.local 6 24) (.local 8 4) abort abort (aux .endpointReader) (atEOF before) [] rfl
    (Function.update_self _ _ _)
  simp only [List.head?_nil,SemiprimeD1StackBytecode.choose] at h1
  exact join h0 h1
/-- Complete actual raw-packet scan, preserving source data and real caller return cells. -/
theorem source_trace (es:List Parse.Endpoint) (before:Stack→List Bool) (packet position:List Bool)
    (hi:before (aux .endpointReader)=Parse.records es)
    (hz:∀k∈Parse.cleanRoles,before k=[])
    (hp:before (aux .packetKey)=packet) (hpos:before (aux .globalPosition)=position)
    (hb:before (aux .frameBuffer)=[]) (hc:before (aux .copyScratch)=[])
    (ha:∀k,before (arithmetic k)=[]):
    Runs program (timeBound es packet position) (.local 6 23) before (.local 8 4) (result es before packet position):=by
  induction es generalizing before position with
  | nil=>exact eof_run before hi
  | cons e es ih=>
    have h0:=Visit.source_trace before e (Parse.records es) packet position hi hz hp hpos hb hc ha
    let after:=Visit.result before e (Parse.records es) packet position
    have hi':after (aux .endpointReader)=Parse.records es:=View.result_reader _ _ _ _ _
    have hz':∀k∈Parse.cleanRoles,after k=[]:=View.result_clean _ _ _ _ _ hz
    have hp':after (aux .packetKey)=packet:=
      (View.result_other _ _ _ _ _ (aux .packetKey) (by intro j;fin_cases j <;> decide)
        (by decide) (by decide) (by decide) (by decide)).trans hp
    have hpos':after (aux .globalPosition)=View.nextPosition e packet position:=View.result_position _ _ _ _ _ hpos
    have hb':after (aux .frameBuffer)=[]:=
      (View.result_other _ _ _ _ _ (aux .frameBuffer) (by intro j;fin_cases j <;> decide)
        (by decide) (by decide) (by decide) (by decide)).trans hb
    have hc':after (aux .copyScratch)=[]:=
      (View.result_other _ _ _ _ _ (aux .copyScratch) (by intro j;fin_cases j <;> decide)
        (by decide) (by decide) (by decide) (by decide)).trans hc
    have ha':∀k,after (arithmetic k)=[]:=by
      intro k
      exact (View.result_other _ _ _ _ _ (arithmetic k)
        (by intro j;fin_cases j <;> simp [Cleanup.role,arithmetic,aux])
        (by simp [arithmetic,aux]) (by simp [arithmetic,aux]) (by simp [arithmetic,aux])
        (by simp [arithmetic,aux])).trans (ha k)
    exact join h0 (ih after (View.nextPosition e packet position) hi' hz' hp' hpos' hb' hc' ha')
end RiemannGaussian.SemiprimeD1StackChildGroupFactoryBucketLoop
