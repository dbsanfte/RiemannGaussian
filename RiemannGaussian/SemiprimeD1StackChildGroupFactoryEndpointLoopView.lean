/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackChildGroupFactoryEndpointLoop
/-! # Exact ordered real endpoint logs and whole-loop cache retention -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackChildGroupFactoryEndpointLoopView
open SemiprimeD1StackChildGroupFactoryRoles SemiprimeD1StackChildGroupFactoryEndpointLoop
namespace Old
export SemiprimeD1StackChildGroupFactoryEndpointOldLog (row)
end Old
namespace Emit
export SemiprimeD1StackChildGroupFactoryEndpointEmit (row)
end Emit
namespace OV
export SemiprimeD1StackChildGroupFactoryEndpointOccurrenceView
  (result_other result_oldHistory result_endpointHistory selectedRow)
end OV
/-- Exact original old-tag row bytes, owner BEFORE factor at every incidence. -/
def oldRecords:List Row→List Bool
  | []=>[]
  | row::rows=>Old.row true row.fields.owner row.fields.edge++Old.row false row.fields.factor row.fields.edge++oldRecords rows
/-- Only a computed TRUE lookup result contributes an actual selected record. -/
def chosen (owner flag:Bool) (f:Parse.Fields):List Bool:=
  if flag then Emit.row owner (if owner then f.owner else f.factor) f.packet f.slot f.edge else []
/-- Exact raw selected row stream, with every retained occurrence in original owner-before-factor order. -/
def selectedRecords:List Row→List Bool
  | []=>[]
  | row::rows=>chosen true row.ownerFlag row.fields++chosen false row.factorFlag row.fields++selectedRecords rows
/-- Conditional history bytes are the reverse of the actual conditional record bytes. -/
theorem chosen_reverse (owner flag:Bool) (f:Parse.Fields):
    (chosen owner flag f).reverse=OV.selectedRow owner flag f:=by cases flag <;> rfl
/-- Exact old-tag history of the entire actual repeated source. -/
theorem result_oldHistory (rows:List Row) (before:Stack→List Bool):
    result rows before (aux .oldHistory)=(oldRecords rows).reverse++before (aux .oldHistory):=by
  induction rows generalizing before with
  | nil=>rfl
  | cons row rows ih=>
    rw [result,ih,OV.result_oldHistory]
    simp only [oldRecords,List.reverse_append,List.append_assoc]
/-- Exact selected-record history, preserving both/one/neither endpoint outcomes without reordering. -/
theorem result_endpointHistory (rows:List Row) (before:Stack→List Bool):
    result rows before (aux .endpointHistory)=(selectedRecords rows).reverse++before (aux .endpointHistory):=by
  induction rows generalizing before with
  | nil=>rfl
  | cons row rows ih=>
    rw [result,ih,OV.result_endpointHistory,←chosen_reverse false row.factorFlag row.fields,
      ←chosen_reverse true row.ownerFlag row.fields]
    simp only [selectedRecords,List.reverse_append,List.append_assoc]
/-- Every physical role outside source readers, generated histories and parsed fields is retained literally. -/
theorem result_other (rows:List Row) (before:Stack→List Bool) (k:Stack)
    (hf:∀j,Cleanup.role j≠k) (hp:k≠aux .pairReader) (hm:k≠aux .placementReader)
    (ho:k≠aux .oldHistory) (he:k≠aux .endpointHistory):
    result rows before k=before k:=by
  induction rows generalizing before with
  | nil=>simp only [result,atEOF,Function.update_of_ne hm,Function.update_of_ne hp]
  | cons row rows ih=>
    rw [result,ih]
    exact OV.result_other _ _ _ _ _ _ k hf hp hm ho he
/-- Every actually completed pair source leaves both physical source readers empty. -/
theorem result_readers (rows:List Row) (before:Stack→List Bool):
    result rows before (aux .pairReader)=[] ∧ result rows before (aux .placementReader)=[]:=by
  induction rows generalizing before with
  | nil=>exact ⟨rfl,rfl⟩
  | cons row rows ih=>exact ih _
/-- All real lookup words retain their physically clear boundary state throughout the entire loop. -/
theorem result_lookup (rows:List Row) (before:Stack→List Bool) (k:SemiprimeD1StackChildGroupFactoryRoles.L.Stack):
    result rows before (lookup k)=before (lookup k):=
  result_other rows before (lookup k) (by intro j;fin_cases j <;> simp [Cleanup.role,lookup,aux])
    (by simp [lookup,aux]) (by simp [lookup,aux]) (by simp [lookup,aux]) (by simp [lookup,aux])
end RiemannGaussian.SemiprimeD1StackChildGroupFactoryEndpointLoopView
