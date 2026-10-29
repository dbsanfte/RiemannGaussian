/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackChildGroupFactoryLeftPortVisit
/-! # Exact actual left-port visit boundary, with all six child fields cleared -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackChildGroupFactoryLeftPortVisitView
open SemiprimeD1StackChildGroupFactoryRoles SemiprimeD1StackChildGroupFactoryLeftPortVisit
open SemiprimeBitArithmetic (bitValue)
namespace Cleanup
export SemiprimeD1StackChildGroupFactoryChildCleanup (result_role result_other)
end Cleanup
/-- Actual endpoint-reader suffix, after real parsing and complete field disposal. -/
theorem result_reader (before:Stack→List Bool) (e:Parse.Endpoint) (position tail target:List Bool):
    result before e position tail target (aux .endpointReader)=tail:=by
  by_cases h:bitValue e.vertex=bitValue target <;> simp [result,h,logged,parsed,Parse.result,Cleanup.result,aux]
/-- All six raw child fields, including the actual global ID, are physically empty. -/
theorem result_role (before:Stack→List Bool) (e:Parse.Endpoint) (position tail target:List Bool) (j:Fin 6):
    result before e position tail target (Cleanup.role j)=[]:=by
  rw [result]
  exact Cleanup.result_role _ _
/-- Complete retention outside the six cleared fields, reader and selected port log. -/
theorem result_other (before:Stack→List Bool) (e:Parse.Endpoint) (position tail target:List Bool) (k:Stack)
    (hf:∀j,Cleanup.role j≠k) (hr:k≠aux .endpointReader) (hh:k≠aux .portHistory):
    result before e position tail target k=before k:=by
  rw [result,Cleanup.result_other _ _ hf]
  have h0:=Ne.symm (hf 0)
  have h1:=Ne.symm (hf 1)
  have h2:=Ne.symm (hf 2)
  have h3:=Ne.symm (hf 3)
  have h4:=Ne.symm (hf 4)
  have h5:=Ne.symm (hf 5)
  simp only [Cleanup.role] at h0 h1 h2 h3 h4 h5
  by_cases h:bitValue e.vertex=bitValue target <;>
    simp only [h,ite_true,ite_false,logged,parsed,Parse.result,
      Function.update_of_ne hh,Function.update_of_ne h5,Function.update_of_ne h4,
      Function.update_of_ne h3,Function.update_of_ne h2,Function.update_of_ne h1,
      Function.update_of_ne h0,Function.update_of_ne hr]
/-- Every real parser/private field is fresh before the next actual endpoint. -/
theorem result_clean (before:Stack→List Bool) (e:Parse.Endpoint) (position tail target:List Bool)
    (hz:∀k∈Parse.cleanRoles,before k=[]):
    ∀k∈Parse.cleanRoles,result before e position tail target k=[]:=by
  intro k hk
  simp only [Parse.cleanRoles,List.mem_cons,List.not_mem_nil,or_false] at hk
  rcases hk with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
  · exact result_role _ _ _ _ _ 0
  · exact result_role _ _ _ _ _ 1
  · exact result_role _ _ _ _ _ 2
  · exact result_role _ _ _ _ _ 3
  · exact result_role _ _ _ _ _ 4
  · exact result_role _ _ _ _ _ 5
  all_goals
    exact (result_other _ _ _ _ _ _ (by intro j;fin_cases j <;> decide) (by decide) (by decide)).trans
      (hz _ (by simp [Parse.cleanRoles]))
/-- Exactly numeric-matching vertices append the physically acquired global ID word. -/
theorem result_portHistory (before:Stack→List Bool) (e:Parse.Endpoint) (position tail target:List Bool):
    result before e position tail target (aux .portHistory)=
      (if bitValue e.vertex=bitValue target then (Log.row position).reverse else [])++before (aux .portHistory):=by
  by_cases h:bitValue e.vertex=bitValue target <;> simp [result,h,logged,parsed,Parse.result,Cleanup.result,aux]
end RiemannGaussian.SemiprimeD1StackChildGroupFactoryLeftPortVisitView
