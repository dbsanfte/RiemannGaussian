/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackOwnerFibreCatalogueView
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 2000000
set_option maxRecDepth 32000
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackOwnerFibreCatalogueCalls
open SemiprimeD1StackOwnerFibreCatalogue SemiprimeD1StackOwnerFibreCatalogueSource
open SemiprimeD1StackOwnerFibreCatalogueView
open SemiprimeD1StackProcedureTrace (Runs included_call runs_trans one_base)
open SemiprimeD1StackPortOwnerRecipeCalls (update_rel)
open SemiprimeSourceHistogramKeyBits (frame)
namespace Rel
export SemiprimeD1StackMultiplierLink (DataRel)
end Rel
/-- The actual next-owner parser's four roles cannot alias. -/
theorem field_injective :Function.Injective fieldStack:=by decide
/-- Physically parse the actual next M-bank payload directly into the real owner filter query. -/
theorem field_call (store:Stack→List Bool) (word tail:List Bool)
    (hi:store (aux .readerIds)=frame word tail) (ho:store (fibreStack (.inr .query))=[])
    (hs:store (aux .fieldScratch)=[]) (hv:store (aux .valid)=[]) :
    Runs program (8*word.length+7) (.local .field) store (.local .valid)
      (Function.update (Function.update (Function.update store (aux .readerIds) tail)
        (fibreStack (.inr .query)) word) (aux .valid) [true]) := by
  let before:=SemiprimeD1TensorTapeFieldBytecode.initial (frame word tail) []
  let after:SemiprimeD1StackBytecode.State F.Stack F.Label:=
    ⟨none,none,Sum.elim (SemiprimeD1TensorTapeFieldMachine.contents tail [] word) (fun _=>[true])⟩
  have hin:Rel.DataRel fieldStack store before.store store:=by
    constructor
    · intro k;rcases k with k|k
      · cases k <;> simp [fieldStack,before,SemiprimeD1TensorTapeFieldBytecode.initial,
          SemiprimeD1TensorTapeFieldMachine.contents,hi,ho,hs]
      · cases k;exact hv
    · intro k _;rfl
  apply included_call program fieldStack Label.field field_injective F.code
    (F.active .tagPop (none,false)) (fun _=>rfl) (.local .field) (.local .valid)
    rfl (8*word.length+6) before after
  · rfl
  · rfl
  · exact SemiprimeD1TensorTapeFieldBytecode.framed_run word tail []
  · exact hin
  · have h0:=update_rel fieldStack field_injective store before.store store hin (.inl .input) tail
    have h1:=update_rel fieldStack field_injective store _ _ h0 (.inl .output) word
    have h2:=update_rel fieldStack field_injective store _ _ h1 (.inr ()) [true]
    have he:Function.update (Function.update (Function.update before.store (.inl .input) tail)
        (.inl .output) word) (.inr ()) [true]=after.store:=by
      funext k;rcases k with k|k <;> cases k <;> rfl
    simpa only [he,fieldStack] using h2
/-- Actual filter source call includes every physical comparison, selected frame and final reversal. -/
theorem filter_call (s:R.Stack→List Bool) (a:Aux→List Bool) (query:List Bool)
    (rows:List (List Bool×List Bool)) :
    Runs program (SemiprimeD1StackOwnerFibreExecution.totalTime query rows+1) (.local .filter)
      (data s (SemiprimeD1StackOwnerFibre.initial query (SemiprimeD1StackOwnerFibre.records rows [])).data a)
      (.local .emitTag) (data s (SemiprimeD1StackOwnerFibre.done query rows []).data a) := by
  apply SemiprimeD1StackProcedureInclusion.included_call program fibreStack Label.fibre fibre_injective
    V.program .loop (fun _=>rfl) (.local .filter) (.local .emitTag) rfl
    (SemiprimeD1StackOwnerFibreExecution.totalTime query rows)
    (SemiprimeD1StackOwnerFibre.initial query (SemiprimeD1StackOwnerFibre.records rows []))
    (SemiprimeD1StackOwnerFibre.done query rows []) _ _ rfl rfl rfl rfl
    (SemiprimeD1StackOwnerFibreExecution.source_run query rows [])
  · exact ⟨fun _=>rfl,fun _ _=>rfl⟩
  · constructor
    · intro k;rfl
    · intro k hk;rcases k with k|k
      · rfl
      · rcases k with k|k
        · exact False.elim (hk k rfl)
        · rfl
end RiemannGaussian.SemiprimeD1StackOwnerFibreCatalogueCalls
