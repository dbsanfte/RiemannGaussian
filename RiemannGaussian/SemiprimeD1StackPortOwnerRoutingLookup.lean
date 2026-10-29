/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackPortOwnerRoutingKey
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 2000000
set_option maxRecDepth 32000
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackPortOwnerRoutingLookup
open SemiprimeD1StackPortOwnerRouting SemiprimeD1StackPortOwnerRoutingAcquisition
open SemiprimeD1StackPortOwnerRoutingView
open SemiprimeD1StackProcedureTrace (Runs runs_trans)
/-- Real nested numeric lookup call, including its actual parser/comparison and final halt. -/
theorem lookup_call (m:Map.Stack→List Bool) (s:Scope.Stack→List Bool) (w:Fin 9→List Bool)
    (a:Aux→List Bool) (query:List Bool) (rows:List (List Bool×List Bool)) :
    Runs program (SemiprimeD1StackOwnerLookupExecution.loopTime query rows+2) (.local .lookup)
      (data m s (SemiprimeD1StackOwnerLookup.initial query (SemiprimeD1StackOwnerLookup.records rows [])).data w a)
      (.local .emitTag) (data m s (SemiprimeD1StackOwnerLookup.done query rows []).data w a) := by
  apply SemiprimeD1StackProcedureInclusion.included_call program lookupStack Label.lookup lookup_injective
    Lookup.program .loop (fun _=>rfl) (.local .lookup) (.local .emitTag) rfl
    (SemiprimeD1StackOwnerLookupExecution.loopTime query rows+1)
    (SemiprimeD1StackOwnerLookup.initial query (SemiprimeD1StackOwnerLookup.records rows []))
    (SemiprimeD1StackOwnerLookup.done query rows []) _ _ rfl rfl rfl rfl
    (SemiprimeD1StackOwnerLookupExecution.source_run query rows [])
  · exact ⟨fun _=>rfl,fun _ _=>rfl⟩
  · constructor
    · intro k;rfl
    · intro k hk;rcases k with k|k
      · rfl
      · rcases k with k|k
        · rfl
        · rcases k with k|k
          · exact False.elim (hk k rfl)
          · rfl
/-- Key-only actual lookup state has precisely the physically framed query and empty map reader. -/
theorem key_state (m:Map.Stack→List Bool) (s:Scope.Stack→List Bool) (w:Fin 9→List Bool) (a:Aux→List Bool) :
    SemiprimeD1StackPortOwnerRoutingKey.store m s w a 6=
      data m s (SemiprimeD1StackOwnerLookup.initial (SemiprimeD1PortOwnerRoutingSpec.query w) []).data w a := by
  unfold SemiprimeD1StackPortOwnerRoutingKey.store
  congr 1
  funext k;rcases k with k|k
  · cases k <;> rfl
  · cases k <;> rfl
/-- The retained actual complete E-map is copied into the real lookup reader for this occurrence. -/
theorem map_copy (m:Map.Stack→List Bool) (s:Scope.Stack→List Bool) (w:Fin 9→List Bool)
    (a:Aux→List Bool) (hs:a .copyScratch=[]) :
    Runs program (5*(m (SemiprimeD1StackOwnerCatalogue.aux .output)).length+4) (.local .copyMap)
      (SemiprimeD1StackPortOwnerRoutingKey.store m s w a 6) (.local .lookup)
      (data m s (SemiprimeD1StackOwnerLookup.initial (SemiprimeD1PortOwnerRoutingSpec.query w)
        (m (SemiprimeD1StackOwnerCatalogue.aux .output))).data w a) := by
  rw [key_state]
  have h:=copy_call 2
    (data m s (SemiprimeD1StackOwnerLookup.initial (SemiprimeD1PortOwnerRoutingSpec.query w) []).data w a)
    (.local .copyMap) (.local .lookup) rfl hs
  change Runs program _ _ _ _ (Function.update _ (lookupStack (.inr .reader))
    (m (SemiprimeD1StackOwnerCatalogue.aux .output)++[])) at h
  rw [List.append_nil,update_lookup] at h
  have he:Function.update (SemiprimeD1StackOwnerLookup.initial (SemiprimeD1PortOwnerRoutingSpec.query w) []).data
      (.inr .reader) (m (SemiprimeD1StackOwnerCatalogue.aux .output))=
      (SemiprimeD1StackOwnerLookup.initial (SemiprimeD1PortOwnerRoutingSpec.query w)
        (m (SemiprimeD1StackOwnerCatalogue.aux .output))).data:=by
    funext k;rcases k with k|k
    · cases k <;> rfl
    · cases k <;> rfl
  rw [he] at h
  exact h
/-- SAME-source actual preserved E-map copy followed by actual numeric owner lookup. -/
theorem copy_lookup_run (m:Map.Stack→List Bool) (s:Scope.Stack→List Bool) (w:Fin 9→List Bool)
    (a:Aux→List Bool) (hs:a .copyScratch=[]) (rows:List (List Bool×List Bool))
    (hm:m (SemiprimeD1StackOwnerCatalogue.aux .output)=SemiprimeD1StackOwnerLookup.records rows []) :
    ∃time≤5*(SemiprimeD1StackOwnerLookup.records rows []).length+
      SemiprimeD1StackOwnerLookupBounds.runBound (SemiprimeD1PortOwnerRoutingSpec.query w) rows+5,
      Runs program time (.local .copyMap) (SemiprimeD1StackPortOwnerRoutingKey.store m s w a 6)
        (.local .emitTag) (data m s (SemiprimeD1StackOwnerLookup.done (SemiprimeD1PortOwnerRoutingSpec.query w) rows []).data w a) := by
  have hcopy:=map_copy m s w a hs
  rw [hm] at hcopy
  have hlook:=lookup_call m s w a (SemiprimeD1PortOwnerRoutingSpec.query w) rows
  have h:=runs_trans program _ _ _ _ _ _ _ _ hcopy hlook
  refine ⟨_,?_,h⟩
  have ht:=SemiprimeD1StackOwnerLookupBounds.time_le (SemiprimeD1PortOwnerRoutingSpec.query w) rows
  omega
end RiemannGaussian.SemiprimeD1StackPortOwnerRoutingLookup
