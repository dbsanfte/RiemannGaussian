/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackChildGroupFactoryEndpointOccurrenceView
/-! # Entire actual EOF-controlled paired endpoint loop
The Row structure describes actual acquired bytes and computed lookup results
for the proof. It is never a runtime input, getter, iterator, or instruction.
-/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackChildGroupFactoryEndpointLoop
open SemiprimeD1StackChildGroupFactoryRoles SemiprimeD1StackChildGroupFactoryWiring
open SemiprimeD1StackChildGroupFactory SemiprimeD1StackChildGroupFactoryPrimitives
open SemiprimeD1StackProcedureTrace
namespace Occ
export SemiprimeD1StackChildGroupFactoryEndpointOccurrence (timeBound result source_trace)
end Occ
namespace View
export SemiprimeD1StackChildGroupFactoryEndpointOccurrenceView
  (result_other result_pair result_placement result_clean)
end View
namespace Parse
export SemiprimeD1StackChildGroupFactoryEndpointParse (Fields payload cleanRoles)
end Parse
namespace Cleanup
export SemiprimeD1StackChildGroupFactoryEndpointCleanup (role)
end Cleanup
open SemiprimeSourceHistogramKeyBits (frame)
/-- Proof-side interpretation of one actual pair and placement and both computed map reads. -/
structure Row where
  /-- Raw fields physically parsed from the two real source tapes. -/
  fields:Parse.Fields
  /-- Actual owner lookup output, not an input classification. -/
  ownerFlag:Bool
  /-- Actual factor lookup output, not an input classification. -/
  factorFlag:Bool
  /-- Actual owner query's unread dictionary suffix. -/
  ownerUnread:List Bool
  /-- Actual factor query's unread dictionary suffix. -/
  factorUnread:List Bool
/-- Exactly the actual two-field pair grammar with its FALSE terminator. -/
def pairs:List Row→List Bool
  | []=>[false]
  | row::rows=>true::frame row.fields.owner (frame row.fields.factor (pairs rows))
/-- Exactly the actual placement-vector grammar, retaining every original row and field. -/
def placements:List Row→List Bool
  | []=>[false]
  | row::rows=>true::frame (Parse.payload row.fields) (placements rows)
/-- All classification obligations concern actual real lookup values, never advised bits. -/
def Valid (entries:List (List Bool×List Bool)) (rows:List Row):Prop:=
  ∀row∈rows,SemiprimeD1StackOwnerLookup.result row.fields.owner entries []=([row.ownerFlag],row.ownerUnread) ∧
    SemiprimeD1StackOwnerLookup.result row.fields.factor entries []=([row.factorFlag],row.factorUnread)
/-- Exact physical stop of the real paired EOF protocol. -/
def atEOF (before:Stack→List Bool):Stack→List Bool:=
  Function.update (Function.update before (aux .pairReader) []) (aux .placementReader) []
/-- Whole actual bank after the same repeated incidence acquisition, including the actual paired EOF pops. -/
def result:List Row→(Stack→List Bool)→Stack→List Bool
  | [],before=>atEOF before
  | row::rows,before=>result rows (Occ.result row.ownerFlag row.factorFlag before row.fields (pairs rows) (placements rows))
/-- Every summand comes from the same actual source; both source suffixes stop at their real EOF. -/
def timeBound (entries:List (List Bool×List Bool)):List Row→Nat
  | []=>4
  | row::rows=>Occ.timeBound row.ownerFlag row.factorFlag row.fields
      (SemiprimeD1StackOwnerLookup.records entries []) row.ownerUnread row.factorUnread entries+timeBound entries rows
/-- Both FALSEs and both physical EOF peeks are executed. -/
theorem eof_run (before:Stack→List Bool) (hp:before (aux .pairReader)=[false])
    (hm:before (aux .placementReader)=[false]):
    Runs program 4 (.local 2 20) before (.local 6 13) (atEOF before):=by
  have h0:=pop_run (.local 2 20) abort (.local 2 21) (.local 2 24)
    (aux .pairReader) before [false] rfl hp
  simp only [List.head?_cons,List.tail_cons,SemiprimeD1StackBytecode.choose] at h0
  let b:=Function.update before (aux .pairReader) []
  have h1:=peek_run (.local 2 21) (.local 2 22) abort abort (aux .pairReader) b [] rfl
    (Function.update_self _ _ _)
  simp only [List.head?_nil,SemiprimeD1StackBytecode.choose] at h1
  have hm':b (aux .placementReader)=[false]:=by simpa [b,aux] using hm
  have h2:=pop_run (.local 2 22) abort (.local 2 23) abort (aux .placementReader) b [false] rfl hm'
  simp only [List.head?_cons,List.tail_cons,SemiprimeD1StackBytecode.choose] at h2
  have h3:=peek_run (.local 2 23) (.local 6 13) abort abort (aux .placementReader) (atEOF before) [] rfl
    (Function.update_self _ _ _)
  simp only [List.head?_nil,SemiprimeD1StackBytecode.choose] at h3
  exact join h0 (join h1 (join h2 h3))
/-- Entire physically acquired paired loop preserves all other words and REAL outer returns. -/
theorem source_trace (entries:List (List Bool×List Bool)) (rows:List Row) (before:Stack→List Bool)
    (hpair:before (aux .pairReader)=pairs rows) (hplacement:before (aux .placementReader)=placements rows)
    (hclean:∀k∈Parse.cleanRoles,before k=[])
    (hside:before (aux .sideWord)=[]) (hr:before (aux .rowBuffer)=[])
    (hb:before (aux .frameBuffer)=[]) (hc:before (aux .copyScratch)=[])
    (hl:∀k,before (lookup k)=[])
    (hm:before (aux .activationMap)=SemiprimeD1StackOwnerLookup.records entries [])
    (hv:Valid entries rows):
    Runs program (timeBound entries rows) (.local 2 20) before (.local 6 13) (result rows before):=by
  induction rows generalizing before with
  | nil=>exact eof_run before hpair hplacement
  | cons row rows ih=>
    obtain ⟨ho,hf⟩:=hv row List.mem_cons_self
    have h0:=Occ.source_trace row.ownerFlag row.factorFlag before row.fields
      (pairs rows) (placements rows) row.ownerUnread row.factorUnread entries
      hpair hplacement hclean hside hr hb hc hl hm ho hf
    let after:=Occ.result row.ownerFlag row.factorFlag before row.fields (pairs rows) (placements rows)
    have hp':after (aux .pairReader)=pairs rows:=View.result_pair _ _ _ _ _ _
    have hm':after (aux .placementReader)=placements rows:=View.result_placement _ _ _ _ _ _
    have hz:∀k∈Parse.cleanRoles,after k=[]:=View.result_clean _ _ _ _ _ _ hclean
    have hs':after (aux .sideWord)=[]:=
      (View.result_other _ _ _ _ _ _ (aux .sideWord) (by intro j;fin_cases j <;> decide)
        (by decide) (by decide) (by decide) (by decide)).trans hside
    have hr':after (aux .rowBuffer)=[]:=
      (View.result_other _ _ _ _ _ _ (aux .rowBuffer) (by intro j;fin_cases j <;> decide)
        (by decide) (by decide) (by decide) (by decide)).trans hr
    have hb':after (aux .frameBuffer)=[]:=
      (View.result_other _ _ _ _ _ _ (aux .frameBuffer) (by intro j;fin_cases j <;> decide)
        (by decide) (by decide) (by decide) (by decide)).trans hb
    have hc':after (aux .copyScratch)=[]:=
      (View.result_other _ _ _ _ _ _ (aux .copyScratch) (by intro j;fin_cases j <;> decide)
        (by decide) (by decide) (by decide) (by decide)).trans hc
    have hl':∀k,after (lookup k)=[]:=by
      intro k
      exact (View.result_other _ _ _ _ _ _ (lookup k)
        (by intro j;fin_cases j <;> simp [Cleanup.role,lookup,aux])
        (by simp [lookup,aux]) (by simp [lookup,aux]) (by simp [lookup,aux])
        (by simp [lookup,aux])).trans (hl k)
    have hmap:after (aux .activationMap)=SemiprimeD1StackOwnerLookup.records entries []:=
      (View.result_other _ _ _ _ _ _ (aux .activationMap) (by intro j;fin_cases j <;> decide)
        (by decide) (by decide) (by decide) (by decide)).trans hm
    have ht:Valid entries rows:=fun r h=>hv r (List.mem_cons_of_mem _ h)
    have h1:=ih after hp' hm' hz hs' hr' hb' hc' hl' hmap ht
    exact join h0 h1
end RiemannGaussian.SemiprimeD1StackChildGroupFactoryEndpointLoop
