/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackChildGroupFactoryTagEarlyClear
import RiemannGaussian.SemiprimeD1StackChildGroupFactoryTagAnswer
/-! # Actual found/exhausted answer-copy, paid early cleanup and ordered logging
The Boolean theorem index identifies an ALREADY reached literal found or EOF
site. It is never an extra runtime input or an advised search classification.
-/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackChildGroupFactoryTagComplete
open SemiprimeD1StackChildGroupFactoryRoles SemiprimeD1StackChildGroupFactoryWiring
open SemiprimeD1StackChildGroupFactory SemiprimeD1StackChildGroupFactoryPrimitives
open SemiprimeD1StackProcedureTrace
namespace Early
export SemiprimeD1StackChildGroupFactoryTagEarlyClear (result timeBound source_trace result_other role)
end Early
namespace Answer
export SemiprimeD1StackChildGroupFactoryTagAnswer (result timeBound source_trace)
end Answer
/-- The two literal source sites reached only by the real preceding search. -/
def start (found:Bool):Label:=if found then .local 13 19 else .local 13 31
/-- Actual copy continuation, with no uncounted early-stop byte disposal. -/
def copiedPC (found:Bool):Label:=if found then .local 13 20 else .local 14 0
/-- Actual preserving copy of the physically computed local position to the physical answer. -/
def copied (before:Stack→List Bool) (position:List Bool):Stack→List Bool:=
  Function.update before (aux .answerPosition) position
/-- Only a real hit requires draining its unread nested-source suffixes/current fields. -/
def cleared (found:Bool) (before:Stack→List Bool) (position:List Bool):Stack→List Bool:=
  if found then Early.result (copied before position) else copied before position
/-- Actual final original-port loop boundary. -/
def result (found:Bool) (before:Stack→List Bool) (position:List Bool):Stack→List Bool:=
  Answer.result (cleared found before position) position
/-- All actual answer-copy/conditional unread-byte drains/logger/local-erasure clocks. -/
def timeBound (found:Bool) (before:Stack→List Bool) (position tag:List Bool):Nat:=
  (5*position.length+4)+(if found then Early.timeBound (copied before position) else 0)+
    Answer.timeBound position position tag
/-- Real finishing source from either already reached actual search continuation. -/
theorem source_trace (found:Bool) (before:Stack→List Bool) (position tag:List Bool)
    (hp:before (aux .localPosition)=position) (ha:before (aux .answerPosition)=[])
    (ht:before (aux .tagWord)=tag) (hb:before (aux .frameBuffer)=[]) (hc:before (aux .copyScratch)=[]):
    Runs program (timeBound found before position tag) (start found) before (.local 11 7) (result found before position):=by
  have h0:=copy_call 36 (start found) (copiedPC found) (by cases found <;> rfl) before position [] hp ha hc
  simp only [List.append_nil] at h0
  change Runs program _ _ before _ (copied before position) at h0
  have hp':copied before position (aux .localPosition)=position:=by simpa [copied,aux] using hp
  have ht':copied before position (aux .tagWord)=tag:=by simpa [copied,aux] using ht
  have hb':copied before position (aux .frameBuffer)=[]:=by simpa [copied,aux] using hb
  have hc':copied before position (aux .copyScratch)=[]:=by simpa [copied,aux] using hc
  cases found with
  | false=>
    have h1:=Answer.source_trace (copied before position) position position tag rfl hp' ht' hb' hc'
    have hwhole:=join h0 h1
    simpa only [timeBound,start,copiedPC,result,cleared,Bool.false_eq_true,ite_false,Nat.add_zero] using hwhole
  | true=>
    have h1:=Early.source_trace (copied before position)
    have ha'':Early.result (copied before position) (aux .answerPosition)=position:=
      (Early.result_other _ _ (by intro j;fin_cases j <;> decide)).trans (Function.update_self _ _ _)
    have hp'':Early.result (copied before position) (aux .localPosition)=position:=
      (Early.result_other _ _ (by intro j;fin_cases j <;> decide)).trans hp'
    have ht'':Early.result (copied before position) (aux .tagWord)=tag:=
      (Early.result_other _ _ (by intro j;fin_cases j <;> decide)).trans ht'
    have hb'':Early.result (copied before position) (aux .frameBuffer)=[]:=
      (Early.result_other _ _ (by intro j;fin_cases j <;> decide)).trans hb'
    have hc'':Early.result (copied before position) (aux .copyScratch)=[]:=
      (Early.result_other _ _ (by intro j;fin_cases j <;> decide)).trans hc'
    have h2:=Answer.source_trace (Early.result (copied before position)) position position tag ha'' hp'' ht'' hb'' hc''
    have hwhole:=join h0 (join h1 h2)
    simpa only [timeBound,start,copiedPC,result,cleared,ite_true,Nat.add_assoc] using hwhole
end RiemannGaussian.SemiprimeD1StackChildGroupFactoryTagComplete
