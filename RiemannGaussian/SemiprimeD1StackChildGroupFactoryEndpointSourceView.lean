/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackChildGroupFactoryEndpointSource
/-! # Exact actual forward-source caller retention and parser restoration -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackChildGroupFactoryEndpointSourceView
open SemiprimeD1StackChildGroupFactoryRoles SemiprimeD1StackChildGroupFactoryEndpointSource
namespace One
export SemiprimeD1StackChildGroupFactoryEndpointOccurrenceView (result_clean)
end One
/-- Actual fixed source workspace exclusions; no input-dependent map or answer. -/
structure Protected (k:Stack):Prop where
  raw:∀j,Cleanup.role j≠k
  pair:k≠aux .pairReader
  placement:k≠aux .placementReader
  endpointHistory:k≠aux .endpointHistory
  endpoints:k≠aux .endpoints
  oldHistory:k≠aux .oldHistory
  oldEndpoints:k≠aux .oldEndpoints
/-- Every protected physical word survives all original repeated endpoint visits and final reversals. -/
theorem result_other (before:Stack→List Bool) (rows:List Loop.Row) (k:Stack) (hk:Protected k):
    result before rows k=before k:=by
  simp only [result,Function.update_of_ne hk.oldEndpoints,Function.update_of_ne hk.oldHistory,
    Function.update_of_ne hk.endpoints,Function.update_of_ne hk.endpointHistory]
  rw [View.result_other _ _ _ hk.raw hk.pair hk.placement hk.oldHistory hk.endpointHistory]
  simp only [copied,Function.update_of_ne hk.placement,Function.update_of_ne hk.pair]
/-- The complete actual original-pair loop restores every parser/raw destination. -/
theorem loop_clean (rows:List Loop.Row) (before:Stack→List Bool)
    (hc:∀k∈Parse.cleanRoles,before k=[]):∀k∈Parse.cleanRoles,Loop.result rows before k=[]:=by
  induction rows generalizing before with
  | nil=>
    intro k hk
    simp only [Parse.cleanRoles,List.mem_cons,List.not_mem_nil,or_false] at hk
    rcases hk with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
    all_goals simpa [Loop.result,SemiprimeD1StackChildGroupFactoryEndpointLoop.atEOF,aux,field] using hc _ (by simp [Parse.cleanRoles,aux,field])
  | cons r rows ih=>exact ih _ (One.result_clean r.ownerFlag r.factorFlag before r.fields _ _ hc)
/-- The actual whole forward source leaves its complete parser/raw bank clean. -/
theorem result_clean (before:Stack→List Bool) (rows:List Loop.Row)
    (hc:∀k∈Parse.cleanRoles,before k=[]):∀k∈Parse.cleanRoles,result before rows k=[]:=by
  have hc':∀k∈Parse.cleanRoles,copied before rows k=[]:=by simpa [copied,Parse.cleanRoles,aux,field] using hc
  have hl:=loop_clean rows (copied before rows) hc'
  intro k hk
  simp only [Parse.cleanRoles,List.mem_cons,List.not_mem_nil,or_false] at hk
  rcases hk with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
  all_goals simpa [result,aux,field] using hl _ (by simp [Parse.cleanRoles,aux,field])
/-- The selected endpoint vector is the exact literal emitted forward stream. -/
theorem result_endpoints (before:Stack→List Bool) (rows:List Loop.Row):
    result before rows (aux .endpoints)=View.selectedRecords rows++[false]:=rfl
/-- The old endpoint vector always includes both sides in original order. -/
theorem result_oldEndpoints (before:Stack→List Bool) (rows:List Loop.Row):
    result before rows (aux .oldEndpoints)=View.oldRecords rows++[false]:=rfl
end RiemannGaussian.SemiprimeD1StackChildGroupFactoryEndpointSourceView
