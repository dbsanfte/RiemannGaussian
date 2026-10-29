/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackPortOwnerRouting
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 2000000
set_option maxRecDepth 32000
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackPortOwnerRoutingAcquisition
open SemiprimeD1StackPortOwnerRouting
open SemiprimeD1StackProcedureTrace (Runs included_call runs_trans)
open SemiprimeD1StackPortOwnerRecipeCalls (update_rel)
namespace Rel
export SemiprimeD1StackMultiplierLink (DataRel)
end Rel
/-- Literal physical partition of BOTH actual sources, real lookup and fresh parsed/work roles. -/
def data (m:Map.Stack→List Bool) (s:Scope.Stack→List Bool) (l:Lookup.Stack→List Bool)
    (f:Fin 9→List Bool) (a:Aux→List Bool) : Stack→List Bool :=
  Sum.elim m (Sum.elim s (Sum.elim l (Sum.elim f a)))
/-- Map acquisition aliases no scoped-source, lookup or outer role. -/
theorem map_injective : Function.Injective mapStack :=Sum.inl_injective
/-- Scoped-port acquisition aliases no retained map/lookup/outer role. -/
theorem scope_injective : Function.Injective scopeStack :=Sum.inr_injective.comp Sum.inl_injective
/-- Actual real-copy operands are distinct for all three static call sites. -/
theorem copy_injective : ∀part:Fin 3,Function.Injective (copyStack part) := by decide
/-- Literal scope-source projection. -/
theorem data_scope (m:Map.Stack→List Bool) (s:Scope.Stack→List Bool) (l:Lookup.Stack→List Bool)
    (f:Fin 9→List Bool) (a:Aux→List Bool) (k:Scope.Stack) :data m s l f a (scopeStack k)=s k:=rfl
/-- Actual scope-source update, preserving every other physical role. -/
theorem update_scope (m:Map.Stack→List Bool) (s:Scope.Stack→List Bool) (l:Lookup.Stack→List Bool)
    (f:Fin 9→List Bool) (a:Aux→List Bool) (k:Scope.Stack) (word:List Bool) :
    Function.update (data m s l f a) (scopeStack k) word=data m (Function.update s k word) l f a := by
  funext j;rcases j with j|j
  · exact Function.update_of_ne (by intro h;cases h) _ _
  · rcases j with j|j
    · change Function.update (data m s l f a) (scopeStack k) word (scopeStack j)=(Function.update s k word) j
      simp only [Function.update_apply,data_scope,scope_injective.eq_iff]
    · exact Function.update_of_ne (by intro h;cases h) _ _
/-- Every actual preserving copy pays its full physical source traversal. -/
theorem copy_call (part:Fin 3) (store:Stack→List Bool) (pc next:Label)
    (hc:program pc=.call (.copy part 0) next) (hs:store (aux .copyScratch)=[]) :
    Runs program (5*(store (copyStack part 0)).length+4) pc store next
      (Function.update store (copyStack part 1) (store (copyStack part 0)++store (copyStack part 1))) := by
  let word:=store (copyStack part 0)
  let tail:=store (copyStack part 1)
  let before:=SemiprimeD1StackCopy.state 0 none word tail []
  let after:=SemiprimeD1StackCopy.done word (word++tail)
  have hi:Rel.DataRel (copyStack part) store before.store store:=by
    constructor
    · intro k;fin_cases k <;> simp [before,SemiprimeD1StackCopy.state,SemiprimeD1StackCopy.payload,copyStack,word,tail,hs]
    · intro k _;rfl
  apply included_call program (copyStack part) (Label.copy part) (copy_injective part)
    SemiprimeD1StackCopy.code 0 (fun _=>rfl) pc next hc _ before after
  · rfl
  · rfl
  · exact SemiprimeD1StackCopy.copy_words word tail none
  · exact hi
  · have he:Function.update before.store (1:Fin 3) (word++tail)=after.store:=by
      funext k;fin_cases k <;> rfl
    simpa only [he] using update_rel (copyStack part) (copy_injective part) store before.store store hi 1 (word++tail)
/-- Actual N-only E-map acquisition inside this routing source, with all other physical banks retained. -/
theorem map_call (bits:List Bool) (hc:SemiprimeSourceCompactBits.Compact bits)
    (hN:0<SemiprimeBitArithmetic.bitValue bits) (s:Scope.Stack→List Bool) (l:Lookup.Stack→List Bool)
    (f:Fin 9→List Bool) (a:Aux→List Bool) :
    ∃time≤SemiprimeD1StackOwnerCatalogueBounds.polynomial bits.length+1,
      Runs program time (.local .acquireMap) (data (Map.input bits) s l f a) (.local .acquireScope)
        (data (SemiprimeD1StackOwnerCatalogueExecution.done bits).data s l f a) := by
  obtain ⟨time,ht,hr⟩:=SemiprimeD1StackOwnerCatalogueBounds.source_run_polynomial bits hc hN
  refine ⟨time+1,Nat.add_le_add_right ht 1,?_⟩
  apply SemiprimeD1StackProcedureInclusion.included_call program mapStack Label.map map_injective
    Map.program (.local .main) (fun _=>rfl) (.local .acquireMap) (.local .acquireScope) rfl time
    (SemiprimeD1StackOwnerCatalogue.initial bits) (SemiprimeD1StackOwnerCatalogueExecution.done bits)
    _ _ rfl rfl rfl rfl hr
  · exact ⟨fun _=>rfl,fun _ _=>rfl⟩
  · constructor
    · intro k;rfl
    · intro k hk;rcases k with k|k
      · exact False.elim (hk k rfl)
      · rfl
/-- Actual N-only factor-major scoped-port acquisition inside this SAME routing source. -/
theorem scope_call (bits:List Bool) (hb:bits≠[]) (m:Map.Stack→List Bool) (l:Lookup.Stack→List Bool)
    (f:Fin 9→List Bool) (a:Aux→List Bool) :
    ∃time≤10^111*(bits.length+1)^30+1,
      Runs program time (.local .acquireScope) (data m (Scope.input bits) l f a) (.local .copyPorts)
        (data m (SemiprimeD1StackPortScopeExecution.done bits).data l f a) := by
  obtain ⟨time,ht,hr⟩:=SemiprimeD1StackPortScopeBounds.source_run_polynomial bits hb
  refine ⟨time+1,Nat.add_le_add_right ht 1,?_⟩
  apply SemiprimeD1StackProcedureInclusion.included_call program scopeStack Label.scope scope_injective
    Scope.program (.local .main) (fun _=>rfl) (.local .acquireScope) (.local .copyPorts) rfl time
    (SemiprimeD1StackPortScopeRecords.initial bits) (SemiprimeD1StackPortScopeExecution.done bits)
    _ _ rfl rfl rfl rfl hr
  · exact ⟨fun _=>rfl,fun _ _=>rfl⟩
  · constructor
    · intro k;rfl
    · intro k hk;rcases k with k|k
      · rfl
      · rcases k with k|k
        · exact False.elim (hk k rfl)
        · rfl
/-- The authoritative scoped source also starts with one physical copy of binary N alone. -/
theorem scope_input_single (bits:List Bool) : Scope.input bits=fun k=>if k=Scope.originalInput then bits else [] := by
  funext k;rcases k with k|k
  · change SemiprimeD1StackPortOrdinalBank.input bits k=_
    rw [SemiprimeD1StackPortScopeExecution.source_input]
    simp only [SemiprimeD1StackPortScopeRecords.originalInput,SemiprimeD1StackPortScopeRecords.sourceStack,
      Sum.inl.injEq]
  · rfl
/-- A real binary-N destination write creates precisely the old scoped-source initial store. -/
theorem scope_initial_write (bits:List Bool) :
    Function.update (fun _:Scope.Stack=>[]) Scope.originalInput bits=Scope.input bits := by
  rw [scope_input_single]
  funext k;simp only [Function.update_apply]
/-- All newly allocated routing roles are empty before N acquisition. -/
def fresh (m:Map.Stack→List Bool) (s:Scope.Stack→List Bool) : Stack→List Bool :=
  data m s (fun _=>[]) (fun _=>[]) (fun _=>[])
/-- Literal initial routing store is the map's binary-N input with every other role empty. -/
theorem input_fresh (bits:List Bool) :input bits=fresh (Map.input bits) (fun _=>[]) := by
  funext k;rcases k with k|k
  · rfl
  · rcases k with k|k
    · rfl
    · rcases k with k|k
      · rfl
      · rcases k with k|k <;> rfl
/-- The second N-only acquisition receives its binary input via an ACTUAL preserving Copy call. -/
theorem copy_N (bits:List Bool) :
    Runs program (5*bits.length+4) (.local .main) (input bits) (.local .acquireMap)
      (fresh (Map.input bits) (Scope.input bits)) := by
  have h:=copy_call 0 (input bits) (.local .main) (.local .acquireMap) rfl rfl
  have hn:input bits (copyStack 0 0)=bits:=by
    change Map.input bits Map.originalInput=bits
    rw [SemiprimeD1StackOwnerCatalogueResources.input_single]
    exact ite_eq_left rfl
  have hd:input bits (copyStack 0 1)=[]:=rfl
  rw [hn,hd,List.append_nil] at h
  change Runs program _ _ _ _ (Function.update (input bits) (scopeStack Scope.originalInput) bits) at h
  rw [input_fresh] at h
  simpa only [input_fresh,fresh,update_scope,scope_initial_write] using h
/-- Exact BOTH actual acquired source stores, before the scoped reader is copied. -/
def acquired (bits:List Bool) : Stack→List Bool :=
  fresh (SemiprimeD1StackOwnerCatalogueExecution.done bits).data (SemiprimeD1StackPortScopeExecution.done bits).data
/-- Full binary-N-only physical acquisition of the original E map AND factor-major scoped-port tape. -/
theorem sources_run (bits:List Bool) (hc:SemiprimeSourceCompactBits.Compact bits)
    (hN:0<SemiprimeBitArithmetic.bitValue bits) :
    ∃time≤5*bits.length+4+(SemiprimeD1StackOwnerCatalogueBounds.polynomial bits.length+1)+
      (10^111*(bits.length+1)^30+1),
      Runs program time (.local .main) (input bits) (.local .copyPorts) (acquired bits) := by
  have hb:bits≠[]:=by intro h;subst bits;exact Nat.lt_irrefl _ hN
  obtain ⟨m,hm,hmr⟩:=map_call bits hc hN (Scope.input bits) (fun _=>[]) (fun _=>[]) (fun _=>[])
  obtain ⟨s,hs,hsr⟩:=scope_call bits hb (SemiprimeD1StackOwnerCatalogueExecution.done bits).data
    (fun _=>[]) (fun _=>[]) (fun _=>[])
  have h:=runs_trans program _ _ _ _ _ _ _ _ (copy_N bits) (runs_trans program _ _ _ _ _ _ _ _ hmr hsr)
  refine ⟨(5*bits.length+4)+(m+s),by omega,h⟩
end RiemannGaussian.SemiprimeD1StackPortOwnerRoutingAcquisition
