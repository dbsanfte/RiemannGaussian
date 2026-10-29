/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackChildGroupFactoryBucketLoop
/-! # Exact selected endpoint/port order of the actual complete packet scan
Repeated prepared packets preserve their repeated endpoint occurrences. Fresh
positions are actual binary successors, never original occurrence IDs.
-/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackChildGroupFactoryBucketLoopView
open SemiprimeD1StackChildGroupFactoryRoles SemiprimeD1StackChildGroupFactoryBucketLoop
namespace VV
export SemiprimeD1StackChildGroupFactoryBucketVisitView
  (result_reader result_position result_clean result_other result_bucketHistory result_portHistory)
end VV
namespace Rows
export SemiprimeD1StackChildGroupFactoryBucketEmit (row portRow payload)
end Rows
namespace Inc
export SemiprimeD1StackChildGroupFactoryBucketIncrement (successor)
end Inc
/-- Actual ordered matches, annotated by the actual counter at emission. -/
def selected:List Parse.Endpoint→List Bool→List Bool→List (Parse.Endpoint×List Bool)
  | [],_,_=>[]
  | e::es,packet,position=>if e.packet=packet then
      (e,position)::selected es packet (Inc.successor position) else selected es packet position
/-- Actual final counter after all matching emissions. -/
def finalPosition:List Parse.Endpoint→List Bool→List Bool→List Bool
  | [],_,position=>position
  | e::es,packet,position=>finalPosition es packet (View.nextPosition e packet position)
/-- Raw exact chronological child-endpoint record stream before its single FALSE terminator. -/
def records (es:List Parse.Endpoint) (packet position:List Bool):List Bool:=
  (selected es packet position).flatMap (fun p=>Rows.row p.1 p.2)
/-- Actual emitted binary port words, in the exact same child order. -/
def portWords (es:List Parse.Endpoint) (packet position:List Bool):List (List Bool):=
  (selected es packet position).map Prod.snd
/-- Raw exact chronological binary port-record stream before its FALSE terminator. -/
def portRecords (es:List Parse.Endpoint) (packet position:List Bool):List Bool:=
  (portWords es packet position).flatMap Rows.portRow
/-- Whole actual reader ends empty. -/
theorem result_reader (es:List Parse.Endpoint) (before:Stack→List Bool) (packet position:List Bool):
    result es before packet position (aux .endpointReader)=[]:=by
  induction es generalizing before position with
  | nil=>rfl
  | cons e es ih=>exact ih _ _
/-- Full actual fresh binary counter after the scan. -/
theorem result_position (es:List Parse.Endpoint) (before:Stack→List Bool) (packet position:List Bool)
    (hp:before (aux .globalPosition)=position):
    result es before packet position (aux .globalPosition)=finalPosition es packet position:=by
  induction es generalizing before position with
  | nil=>simpa [result,atEOF,aux,finalPosition] using hp
  | cons e es ih=>exact ih _ _ (VV.result_position _ _ _ _ _ hp)
/-- All source caches outside the parser, histories and counter retain their actual bytes. -/
theorem result_other (es:List Parse.Endpoint) (before:Stack→List Bool) (packet position:List Bool) (k:Stack)
    (hf:∀j,Cleanup.role j≠k) (hr:k≠aux .endpointReader) (hb:k≠aux .bucketHistory)
    (hp:k≠aux .portHistory) (hg:k≠aux .globalPosition):
    result es before packet position k=before k:=by
  induction es generalizing before position with
  | nil=>simp only [result,atEOF,Function.update_of_ne hr]
  | cons e es ih=>rw [result,ih];exact VV.result_other _ _ _ _ _ _ hf hr hb hp hg
/-- All actual parser and payload fresh roles are restored at the complete scan boundary. -/
theorem result_clean (es:List Parse.Endpoint) (before:Stack→List Bool) (packet position:List Bool)
    (hz:∀k∈Parse.cleanRoles,before k=[]):
    ∀k∈Parse.cleanRoles,result es before packet position k=[]:=by
  induction es generalizing before position with
  | nil=>
    intro k hk
    have hn:k≠aux .endpointReader:=by
      intro he
      subst k
      simp [Parse.cleanRoles,aux,SemiprimeD1StackChildGroupFactoryRoles.field] at hk
    simpa only [result,atEOF,Function.update_of_ne hn] using hz k hk
  | cons e es ih=>exact ih _ _ (VV.result_clean _ _ _ _ _ hz)
/-- Complete actual selected endpoint history in exact original scan order. -/
theorem result_bucketHistory (es:List Parse.Endpoint) (before:Stack→List Bool) (packet position:List Bool):
    result es before packet position (aux .bucketHistory)=(records es packet position).reverse++before (aux .bucketHistory):=by
  induction es generalizing before position with
  | nil=>simp only [result,atEOF,records,selected,List.flatMap_nil,List.reverse_nil,List.nil_append];rfl
  | cons e es ih=>
    rw [result,ih,VV.result_bucketHistory]
    by_cases h:e.packet=packet <;>
      simp [records,selected,View.nextPosition,h,List.reverse_append,List.append_assoc]
/-- Binary port history is the corresponding exact chronological selected-ID stream. -/
theorem result_portHistory (es:List Parse.Endpoint) (before:Stack→List Bool) (packet position:List Bool):
    result es before packet position (aux .portHistory)=(portRecords es packet position).reverse++before (aux .portHistory):=by
  induction es generalizing before position with
  | nil=>simp only [result,atEOF,portRecords,portWords,selected,List.map_nil,List.flatMap_nil,List.reverse_nil,List.nil_append];rfl
  | cons e es ih=>
    rw [result,ih,VV.result_portHistory]
    by_cases h:e.packet=packet <;>
      simp [portRecords,portWords,selected,View.nextPosition,h,List.reverse_append,List.append_assoc]
end RiemannGaussian.SemiprimeD1StackChildGroupFactoryBucketLoopView
