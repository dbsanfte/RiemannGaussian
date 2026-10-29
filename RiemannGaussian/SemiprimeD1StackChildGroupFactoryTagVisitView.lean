/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackChildGroupFactoryTagVisit
/-! # Exact actual found/continue boundaries of the literal first-index visit -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackChildGroupFactoryTagVisitView
open SemiprimeD1StackChildGroupFactoryRoles SemiprimeD1StackChildGroupFactoryTagVisit
open SemiprimeBitArithmetic (bitValue)
namespace Cleanup
export SemiprimeD1StackChildGroupFactoryChildCleanup (role result_role result_other)
end Cleanup
/-- Actual numeric-vertex AND literal whole-tag predicate. It is not an input verdict. -/
def hit (e:Parse.Endpoint) (target tag:List Bool):Prop:=bitValue e.vertex=bitValue target ∧ tag=candidate e
/-- The physically executed next binary counter for a nonmatching child. -/
def advance (e:Parse.Endpoint) (target position:List Bool):List Bool:=
  if bitValue e.vertex=bitValue target then Inc.successor position else position
/-- A first actual hit preserves its parsed candidate and branches before any later child is read. -/
theorem result_hit (before:Stack→List Bool) (e:Parse.Endpoint) (global tail target tag position:List Bool)
    (hh:hit e target tag):result before e global tail target tag position=built before e global tail:=by
  simp only [result,hh.1,hh.2,ite_true]
/-- Actual physical reader suffix after a nonmatching child. -/
theorem result_reader (before:Stack→List Bool) (e:Parse.Endpoint) (global tail target tag position:List Bool)
    (hh:¬hit e target tag):result before e global tail target tag position (aux .endpointReader)=tail:=by
  by_cases hv:bitValue e.vertex=bitValue target
  · have he:tag≠candidate e:=fun h=>hh ⟨hv,h⟩
    simp [result,hv,he,parsed,Parse.result,Cleanup.result,aux]
  · simp [result,hv,parsed,Parse.result,Cleanup.result,aux]
/-- All six actual fields are erased on both continuing paths. -/
theorem result_role (before:Stack→List Bool) (e:Parse.Endpoint) (global tail target tag position:List Bool) (j:Fin 6)
    (hh:¬hit e target tag):result before e global tail target tag position (Cleanup.role j)=[]:=by
  by_cases hv:bitValue e.vertex=bitValue target
  · have he:tag≠candidate e:=fun h=>hh ⟨hv,h⟩
    simp only [result,hv,he,ite_true,ite_false]
    exact Cleanup.result_role _ _
  · simp only [result,hv,ite_false]
    exact Cleanup.result_role _ _
/-- Actual per-vertex position advances only after a same-vertex different whole tag. -/
theorem result_position (before:Stack→List Bool) (e:Parse.Endpoint) (global tail target tag position:List Bool)
    (hp:before (aux .localPosition)=position) (hh:¬hit e target tag):
    result before e global tail target tag position (aux .localPosition)=advance e target position:=by
  simp only [aux] at hp
  by_cases hv:bitValue e.vertex=bitValue target
  · have he:tag≠candidate e:=fun h=>hh ⟨hv,h⟩
    simp [result,hv,he,advance,Cleanup.result,aux]
  · simp [result,hv,advance,Cleanup.result,parsed,Parse.result,aux,hp]
/-- All other source/cache words are retained, on the found path and both continuing paths. -/
theorem result_other (before:Stack→List Bool) (e:Parse.Endpoint) (global tail target tag position:List Bool) (k:Stack)
    (hf:∀j,Cleanup.role j≠k) (hr:k≠aux .endpointReader) (hc:k≠aux .candidateTag) (hp:k≠aux .localPosition):
    result before e global tail target tag position k=before k:=by
  have h0:=Ne.symm (hf 0)
  have h1:=Ne.symm (hf 1)
  have h2:=Ne.symm (hf 2)
  have h3:=Ne.symm (hf 3)
  have h4:=Ne.symm (hf 4)
  have h5:=Ne.symm (hf 5)
  simp only [Cleanup.role] at h0 h1 h2 h3 h4 h5
  by_cases hv:bitValue e.vertex=bitValue target
  · by_cases he:tag=candidate e
    · simp only [result,hv,he,ite_true,built,parsed,Parse.result,Function.update_of_ne hc,
        Function.update_of_ne h5,Function.update_of_ne h4,Function.update_of_ne h3,
        Function.update_of_ne h2,Function.update_of_ne h1,Function.update_of_ne h0,Function.update_of_ne hr]
    · simp only [result,hv,he,ite_true,ite_false]
      rw [Cleanup.result_other _ k hf]
      simp only [parsed,Parse.result,Function.update_of_ne hp,Function.update_of_ne h5,Function.update_of_ne h4,
        Function.update_of_ne h3,Function.update_of_ne h2,Function.update_of_ne h1,Function.update_of_ne h0,Function.update_of_ne hr]
  · simp only [result,hv,ite_false]
    rw [Cleanup.result_other _ k hf]
    simp only [parsed,Parse.result,Function.update_of_ne h5,Function.update_of_ne h4,
      Function.update_of_ne h3,Function.update_of_ne h2,Function.update_of_ne h1,Function.update_of_ne h0,Function.update_of_ne hr]
/-- All parser and payload roles are fresh before the next actual continuing visit. -/
theorem result_clean (before:Stack→List Bool) (e:Parse.Endpoint) (global tail target tag position:List Bool)
    (hz:∀k∈Parse.cleanRoles,before k=[]) (hh:¬hit e target tag):
    ∀k∈Parse.cleanRoles,result before e global tail target tag position k=[]:=by
  intro k hk
  simp only [Parse.cleanRoles,List.mem_cons,List.not_mem_nil,or_false] at hk
  rcases hk with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
  · exact result_role _ _ _ _ _ _ _ 0 hh
  · exact result_role _ _ _ _ _ _ _ 1 hh
  · exact result_role _ _ _ _ _ _ _ 2 hh
  · exact result_role _ _ _ _ _ _ _ 3 hh
  · exact result_role _ _ _ _ _ _ _ 4 hh
  · exact result_role _ _ _ _ _ _ _ 5 hh
  all_goals
    exact (result_other _ _ _ _ _ _ _ _ (by intro j;fin_cases j <;> decide) (by decide) (by decide) (by decide)).trans
      (hz _ (by simp [Parse.cleanRoles]))
/-- The actual candidate word is empty again on both continuing paths. -/
theorem result_candidate (before:Stack→List Bool) (e:Parse.Endpoint) (global tail target tag position:List Bool)
    (hc:before (aux .candidateTag)=[]) (hh:¬hit e target tag):
    result before e global tail target tag position (aux .candidateTag)=[]:=by
  simp only [aux] at hc
  by_cases hv:bitValue e.vertex=bitValue target
  · have he:tag≠candidate e:=fun h=>hh ⟨hv,h⟩
    simp [result,hv,he,Cleanup.result,parsed,Parse.result,aux,hc]
  · simp [result,hv,Cleanup.result,parsed,Parse.result,aux,hc]
end RiemannGaussian.SemiprimeD1StackChildGroupFactoryTagVisitView
