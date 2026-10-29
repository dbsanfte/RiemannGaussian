/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackOwnerCatalogueRecord
import RiemannGaussian.SemiprimeD1StackProcedureInclusion
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 2000000
set_option maxRecDepth 32000
set_option synthInstance.maxSize 131072
namespace RiemannGaussian.SemiprimeD1StackOwnerCatalogueCalls
open SemiprimeD1StackOwnerCatalogue SemiprimeD1StackOwnerCatalogueSource
open SemiprimeD1StackOwnerCatalogueFields
open SemiprimeD1StackProcedureTrace (Runs)
open SemiprimeD1StackPortOwnerRecipeCalls (update_rel)
namespace Rel
export SemiprimeD1StackMultiplierLink (DataRel)
end Rel
/-- Actual equality-call operands cannot alias. -/
theorem equality_injective : Function.Injective equalityStack := by decide
/-- The actual acquired metadata, parsed endpoint operands and private arithmetic work are distinct. -/
theorem recipe_injective : Function.Injective recipeStack := by decide
/-- The actual equality subroutine preserves its source record and physically copies its sentinel key. -/
theorem equality_call (store:Stack→List Bool) (ho:store (aux .equalityKey)=[])
    (hs:store (aux .equalityScratch)=[]) :
    Runs program (5*(store (aux .record)).length+7) (.local .equality) store (.local .arithmetic)
      (Function.update store (aux .equalityKey) (store (aux .record)++[true])) := by
  let record:=store (aux .record)
  let before:=SemiprimeD1StackOwnerEqualityKey.initial record
  let after:=SemiprimeD1StackOwnerEqualityKey.done record
  have hi:Rel.DataRel equalityStack store before.data store:=by
    constructor
    · intro k;fin_cases k <;> simp [equalityStack,before,SemiprimeD1StackOwnerEqualityKey.initial,
        SemiprimeD1StackCopy.payload,record,ho,hs]
    · intro k _;rfl
  apply SemiprimeD1StackProcedureInclusion.included_call program equalityStack Label.equality
    equality_injective Q.program (.inl 0) (fun _=>rfl) (.local .equality) (.local .arithmetic)
    rfl _ before after _ _ rfl rfl rfl rfl (SemiprimeD1StackOwnerEqualityKey.source_run record) hi
  have he:Function.update before.data (1:Fin 3) (record++[true])=after.data:=by
    funext k;fin_cases k <;> rfl
  simpa only [he,equalityStack,show ¬(1:Fin 3)=0 by decide,ite_false,ite_true] using
    update_rel equalityStack equality_injective store before.data store hi 1 (record++[true])
/-- The endpoint compiler leaves every physically parsed input word intact. -/
theorem recipe_done_input (p:SemiprimeD1StackPortOwnerRecipeSpec.Counters)
    (tag:SemiprimeD1StackPortOwnerRecipe.Tag) (i:R.Input) :
    (SemiprimeD1StackPortOwnerRecipeExecution.done p tag).data (.inl i)=
      SemiprimeD1StackPortOwnerRecipeSpec.words p i := by
  cases i <;> rfl
/-- Whole real arithmetic-call inclusion, retaining actual source metadata and owner-ID cache. -/
theorem recipe_call (s:S.Stack→List Bool) (f:Fin 7→List Bool) (a:Aux→List Bool)
    (p:SemiprimeD1StackPortOwnerRecipeSpec.Counters) (tag:SemiprimeD1StackPortOwnerRecipe.Tag)
    (ht:p.tag=(SemiprimeD1StackPortOwnerRecipeDecision.tagCode tag).val) (hd:0<p.digits)
    (hi:∀i:R.Input,data s (fun _=>[]) f a (recipeStack (.inl i))=
      SemiprimeD1StackPortOwnerRecipeSpec.words p i) :
    ∃time≤SemiprimeD1StackPortOwnerRecipeExecution.budget p tag+1,
      Runs program time (.local .arithmetic) (data s (fun _=>[]) f a) (.local (.emitTag false))
        (data s (fun k=>(SemiprimeD1StackPortOwnerRecipeExecution.done p tag).data (.inr k)) f a) := by
  obtain ⟨time,htime,hr⟩:=SemiprimeD1StackPortOwnerRecipeExecution.source_run p tag ht hd
  refine ⟨time+1,Nat.add_le_add_right htime 1,?_⟩
  apply SemiprimeD1StackProcedureInclusion.included_call program recipeStack Label.recipe
    recipe_injective R.program (.local .start) (fun _=>rfl) (.local .arithmetic)
    (.local (.emitTag false)) rfl time
    (SemiprimeD1StackPortOwnerRecipe.initial (SemiprimeD1StackPortOwnerRecipeSpec.words p))
    (SemiprimeD1StackPortOwnerRecipeExecution.done p tag) _ _ rfl rfl rfl rfl hr
  · constructor
    · intro k;rcases k with i|k
      · exact hi i
      · rfl
    · intro k _;rfl
  · constructor
    · intro k;rcases k with i|k
      · rw [recipe_done_input]
        have he:data s (fun k=>(SemiprimeD1StackPortOwnerRecipeExecution.done p tag).data (.inr k)) f a
            (recipeStack (.inl i))=data s (fun _=>[]) f a (recipeStack (.inl i)):=by
          cases i <;> rfl
        rw [he]
        exact hi i
      · rfl
    · intro k hk
      rcases k with k|k
      · rfl
      · rcases k with k|k
        · exact False.elim (hk (.inr k) rfl)
        · rfl
end RiemannGaussian.SemiprimeD1StackOwnerCatalogueCalls
