/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackOwnerFibreCatalogue
import RiemannGaussian.SemiprimeD1StackOwnerFibreRetained
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 2000000
set_option maxRecDepth 32000
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackOwnerFibreCatalogueSource
open SemiprimeD1StackOwnerFibreCatalogue
open SemiprimeD1StackProcedureTrace (Runs included_call runs_trans)
open SemiprimeD1StackPortOwnerRecipeCalls (update_rel)
open SemiprimeBitArithmetic (bitValue)
namespace Rel
export SemiprimeD1StackMultiplierLink (DataRel)
end Rel
/-- Literal physical routing/filter/private-role store, with no semantic state in control. -/
def data (s:R.Stack→List Bool) (f:V.Stack→List Bool) (a:Aux→List Bool) : Stack→List Bool :=
  Sum.elim s (Sum.elim f a)
/-- Fresh physical filter/outer work after actual routing, retaining the complete upstream source state. -/
def clean (s:R.Stack→List Bool) (count ids:List Bool) : Stack→List Bool :=
  data s (fun _=>[]) (fun k=>match k with | .ownerCount=>count | .readerIds=>ids | _=>[])
/-- Source inclusion aliases no owner-filter or fresh E-loop role. -/
theorem source_injective :Function.Injective source:=Sum.inl_injective
/-- All three actual preserving-copy sites use three distinct data roles. -/
theorem copy_injective :∀part:Fin 3,Function.Injective (copyStack part):=by decide
/-- Actual source's original-N-only initial store, before any E/M/owner acquisition. -/
theorem input_clean (bits:List Bool) :input bits=clean (R.input bits) [] []:=by
  funext k;rcases k with k|k
  · rfl
  · rcases k with k|k
    · rfl
    · cases k <;> rfl
/-- The actual retained E tally is derived from the SAME original edge-source count. -/
theorem original_count (bits:List Bool) (hN:0<bitValue bits) :
    (SemiprimeD1StackPortOwnerRoutingExecution.done bits hN).data
      (SemiprimeD1StackPortOwnerRouting.mapStack
        (SemiprimeD1StackOwnerCatalogue.source SemiprimeD1StackRootScopeBank.wireCount))=
      List.replicate (SemiprimePublicAcquiredExecution.wireCount (bitValue bits)) true := by
  rw [SemiprimeD1StackOwnerFibreRetained.routing_map,SemiprimeD1StackOwnerFibreRetained.catalogue_root]
  rw [(SemiprimeD1StackRootScopeBankExecution.result_counts bits).2,
    SemiprimeD1StackRootScopeBankOriginal.wire_count bits]
/-- The actual retained bank is M=2E words, never substituted by an E-word bank. -/
theorem original_ids (bits:List Bool) (hN:0<bitValue bits) :
    (SemiprimeD1StackPortOwnerRoutingExecution.done bits hN).data
      (SemiprimeD1StackPortOwnerRouting.mapStack
        (SemiprimeD1StackOwnerCatalogue.source SemiprimeD1StackRootScopeBank.ids))=
      SemiprimeD1TensorTapeCodec.vectorBits
        (SemiprimeD1OrdinalBankSpec.words (2*SemiprimePublicAcquiredExecution.wireCount (bitValue bits))) := by
  rw [SemiprimeD1StackOwnerFibreRetained.routing_map,SemiprimeD1StackOwnerFibreRetained.catalogue_root]
  calc
    _=SemiprimeD1StackRootScopeBankExecution.result bits SemiprimeD1StackRootScopeBank.ids:=rfl
    _=SemiprimeD1TensorTapeCodec.vectorBits
      (SemiprimeD1OrdinalBankSpec.words (SemiprimeD1StackRootScopeBankExecution.occurrenceCount bits)):=
        SemiprimeD1StackRootScopeBankExecution.result_ids bits
    _=_:=congrArg (SemiprimeD1TensorTapeCodec.vectorBits∘SemiprimeD1OrdinalBankSpec.words)
      (SemiprimeD1StackOwnerCatalogueOriginalMetadata.occurrences_original bits)
/-- SAME actual N-only routing source is called once inside all-owner fibre acquisition. -/
theorem routing_call (bits:List Bool) (hc:SemiprimeSourceCompactBits.Compact bits) (hN:0<bitValue bits) :
    ∃time≤SemiprimeD1StackPortOwnerRoutingBounds.polynomial bits.length+1,
      Runs program time (.local .main) (input bits) (.local .copyCount)
        (clean (SemiprimeD1StackPortOwnerRoutingExecution.done bits hN).data [] []) := by
  obtain ⟨t,ht,hr⟩:=SemiprimeD1StackPortOwnerRoutingBounds.source_run_polynomial bits hc hN
  refine ⟨t+1,Nat.add_le_add_right ht 1,?_⟩
  apply SemiprimeD1StackProcedureInclusion.included_call program source Label.source source_injective
    R.program (.local .main) (fun _=>rfl) (.local .main) (.local .copyCount) rfl t
    (SemiprimeD1StackPortOwnerRouting.initial bits) (SemiprimeD1StackPortOwnerRoutingExecution.done bits hN)
    _ _ rfl rfl rfl rfl hr
  · constructor
    · intro k;rfl
    · intro k _;rfl
  · constructor
    · intro k;rfl
    · intro k hk;rcases k with k|k
      · exact False.elim (hk k rfl)
      · rcases k with k|k
        · rfl
        · cases k <;> rfl
/-- Actual whole-preserving copies of E, all M IDs or the complete routed tape. -/
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
  · have he:Function.update before.store (1:Fin 3) (word++tail)=after.store:=by funext k;fin_cases k <;> rfl
    simpa only [he] using update_rel (copyStack part) (copy_injective part) store before.store store hi 1 (word++tail)
/-- Exact private E-loop tally update by its actual preserving copy. -/
theorem clean_count (s:R.Stack→List Bool) (count ids next:List Bool) :
    Function.update (clean s count ids) (aux .ownerCount) next=clean s next ids := by
  funext k;rcases k with k|k
  · rfl
  · rcases k with k|k
    · rfl
    · cases k <;> simp [clean,data,aux]
/-- Exact private M-bank reader update by its actual preserving copy. -/
theorem clean_ids (s:R.Stack→List Bool) (count ids next:List Bool) :
    Function.update (clean s count ids) (aux .readerIds) next=clean s count next := by
  funext k;rcases k with k|k
  · rfl
  · rcases k with k|k
    · rfl
    · cases k <;> simp [clean,data,aux]
/-- The ACTUAL retained original E tally bytes, used only to describe copied input. -/
def countBytes (bits:List Bool) (hN:0<bitValue bits) : List Bool :=
  (SemiprimeD1StackPortOwnerRoutingExecution.done bits hN).data
    (SemiprimeD1StackPortOwnerRouting.mapStack
      (SemiprimeD1StackOwnerCatalogue.source SemiprimeD1StackRootScopeBank.wireCount))
/-- The ACTUAL retained whole M-ID bank bytes, never an independently supplied owner list. -/
def idBytes (bits:List Bool) (hN:0<bitValue bits) : List Bool :=
  (SemiprimeD1StackPortOwnerRoutingExecution.done bits hN).data
    (SemiprimeD1StackPortOwnerRouting.mapStack
      (SemiprimeD1StackOwnerCatalogue.source SemiprimeD1StackRootScopeBank.ids))
/-- Exact actually reached owner-loop entry with both newly copied private readers. -/
def ready (bits:List Bool) (hN:0<bitValue bits) : Stack→List Bool :=
  clean (SemiprimeD1StackPortOwnerRoutingExecution.done bits hN).data (countBytes bits hN) (idBytes bits hN)
/-- Actual routing and BOTH complete preserving reader/tally copies are all charged. -/
def budget (bits:List Bool) (hN:0<bitValue bits) : Nat :=
  SemiprimeD1StackPortOwnerRoutingBounds.polynomial bits.length+1+
    (5*(countBytes bits hN).length+4)+(5*(idBytes bits hN).length+4)
/-- Closed actual N-only owner-fibre iterator acquisition prefix: no owner key, count or bank advice. -/
theorem acquisition_run (bits:List Bool) (hc:SemiprimeSourceCompactBits.Compact bits) (hN:0<bitValue bits) :
    ∃time≤budget bits hN,Runs program time (.local .main) (input bits) (.local .loop) (ready bits hN) := by
  obtain ⟨time,ht,hr⟩:=routing_call bits hc hN
  let s:=(SemiprimeD1StackPortOwnerRoutingExecution.done bits hN).data
  have hc:=copy_call 0 (clean s [] []) (.local .copyCount) (.local .copyIds) rfl rfl
  change Runs program (5*(countBytes bits hN).length+4) (.local .copyCount) (clean s [] [])
    (.local .copyIds) (Function.update (clean s [] []) (aux .ownerCount) (countBytes bits hN++[])) at hc
  rw [List.append_nil,clean_count] at hc
  have hi:=copy_call 1 (clean s (countBytes bits hN) []) (.local .copyIds) (.local .loop) rfl rfl
  change Runs program (5*(idBytes bits hN).length+4) (.local .copyIds) (clean s (countBytes bits hN) [])
    (.local .loop) (Function.update (clean s (countBytes bits hN) []) (aux .readerIds) (idBytes bits hN++[])) at hi
  rw [List.append_nil,clean_ids] at hi
  have h:=runs_trans program _ _ _ _ _ _ _ _ hr (runs_trans program _ _ _ _ _ _ _ _ hc hi)
  refine ⟨_,?_,h⟩
  unfold budget
  omega
end RiemannGaussian.SemiprimeD1StackOwnerFibreCatalogueSource
