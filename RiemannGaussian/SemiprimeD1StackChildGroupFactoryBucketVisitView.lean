/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackChildGroupFactoryBucketVisit
/-! # Full physical boundary and exact child-global meaning of a real bucket visit -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackChildGroupFactoryBucketVisitView
open SemiprimeD1StackChildGroupFactoryRoles SemiprimeD1StackChildGroupFactoryBucketVisit
namespace Rows
export SemiprimeD1StackChildGroupFactoryBucketEmit (row portRow)
end Rows
/-- The actual counter advances only for a literally identical whole raw packet. -/
def nextPosition (e:Parse.Endpoint) (packet position:List Bool):List Bool:=
  if e.packet=packet then Inc.successor position else position
/-- Full input-reader suffix after the actual parse. -/
theorem result_reader (before:Stack→List Bool) (e:Parse.Endpoint) (tail packet position:List Bool):
    result before e tail packet position (aux .endpointReader)=tail:=by
  by_cases h:e.packet=packet <;> simp [result,h,emitted,parsed,Parse.result,Cleanup.result,Emit.result,aux]
/-- Actual binary counter result, preserving source padding whenever this endpoint does not match. -/
theorem result_position (before:Stack→List Bool) (e:Parse.Endpoint) (tail packet position:List Bool)
    (hp:before (aux .globalPosition)=position):
    result before e tail packet position (aux .globalPosition)=nextPosition e packet position:=by
  simp only [aux] at hp
  by_cases h:e.packet=packet <;> simp [result,h,nextPosition,emitted,parsed,Parse.result,Cleanup.result,Emit.result,aux,hp]
/-- Every parsed raw-field tape is really cleared. -/
theorem result_role (before:Stack→List Bool) (e:Parse.Endpoint) (tail packet position:List Bool) (j:Fin 5):
    result before e tail packet position (Cleanup.role j)=[]:=by
  fin_cases j <;> by_cases h:e.packet=packet <;> simp [result,h,Cleanup.result,Cleanup.role,aux]
/-- Actual cache retention outside raw fields, the input reader, the two logs and the fresh counter. -/
theorem result_other (before:Stack→List Bool) (e:Parse.Endpoint) (tail packet position:List Bool) (k:Stack)
    (hf:∀j,Cleanup.role j≠k) (hr:k≠aux .endpointReader) (hb:k≠aux .bucketHistory)
    (hp:k≠aux .portHistory) (hg:k≠aux .globalPosition):
    result before e tail packet position k=before k:=by
  rw [result,SemiprimeD1StackChildGroupFactoryBucketCleanup.result_other _ k hf]
  have h0:=Ne.symm (hf 0)
  have h1:=Ne.symm (hf 1)
  have h2:=Ne.symm (hf 2)
  have h3:=Ne.symm (hf 3)
  have h4:=Ne.symm (hf 4)
  simp only [Cleanup.role] at h0 h1 h2 h3 h4
  by_cases h:e.packet=packet <;>
    simp only [h,ite_true,ite_false,emitted,Emit.result,parsed,Parse.result,
      Function.update_of_ne hg,Function.update_of_ne hp,Function.update_of_ne hb,
      Function.update_of_ne h4,Function.update_of_ne h3,Function.update_of_ne h2,
      Function.update_of_ne h1,Function.update_of_ne h0,Function.update_of_ne hr]
/-- All parser and payload fresh roles are physically restored before the next actual endpoint. -/
theorem result_clean (before:Stack→List Bool) (e:Parse.Endpoint) (tail packet position:List Bool)
    (hz:∀k∈Parse.cleanRoles,before k=[]):
    ∀k∈Parse.cleanRoles,result before e tail packet position k=[]:=by
  intro k hk
  simp only [Parse.cleanRoles,List.mem_cons,List.not_mem_nil,or_false] at hk
  rcases hk with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
  · exact result_role before e tail packet position 0
  · exact result_role before e tail packet position 1
  · exact result_role before e tail packet position 2
  · exact result_role before e tail packet position 3
  · exact result_role before e tail packet position 4
  all_goals
    exact (result_other before e tail packet position _
      (by intro j;fin_cases j <;> decide) (by decide) (by decide) (by decide) (by decide)).trans
        (hz _ (by simp [Parse.cleanRoles]))
/-- Actual selected bucket log, with all original bytes and the actual fresh position. -/
theorem result_bucketHistory (before:Stack→List Bool) (e:Parse.Endpoint) (tail packet position:List Bool):
    result before e tail packet position (aux .bucketHistory)=
      (if e.packet=packet then (Rows.row e position).reverse else [])++before (aux .bucketHistory):=by
  by_cases h:e.packet=packet <;> simp [result,h,emitted,parsed,Parse.result,Cleanup.result,Emit.result,aux]
/-- Actual corresponding binary-port log in exactly the same selected endpoint order. -/
theorem result_portHistory (before:Stack→List Bool) (e:Parse.Endpoint) (tail packet position:List Bool):
    result before e tail packet position (aux .portHistory)=
      (if e.packet=packet then (Rows.portRow position).reverse else [])++before (aux .portHistory):=by
  by_cases h:e.packet=packet <;> simp [result,h,emitted,parsed,Parse.result,Cleanup.result,Emit.result,aux]
end RiemannGaussian.SemiprimeD1StackChildGroupFactoryBucketVisitView
