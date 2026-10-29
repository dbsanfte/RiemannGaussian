/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackOwnerCatalogueSource
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 2000000
set_option maxRecDepth 32000
set_option synthInstance.maxSize 131072
namespace RiemannGaussian.SemiprimeD1StackOwnerCatalogueFields
open SemiprimeD1StackOwnerCatalogue SemiprimeD1StackOwnerCatalogueSource
open SemiprimeD1StackProcedureTrace (Runs included_call)
open SemiprimeD1StackPortOwnerRecipeCalls (update_rel)
open SemiprimeSourceHistogramKeyBits (frame)
namespace Rel
export SemiprimeD1StackMultiplierLink (DataRel)
end Rel
/-- Actual physical reader selected by a static edge/ID field position. -/
def fieldReader (part:Fin 7) : Stack := if part=6 then aux .readerIds else aux .readerEdges
/-- Every actual field-parser inclusion has four distinct Boolean roles. -/
theorem field_injective (part:Fin 7) : Function.Injective (fieldStack part) := by
  fin_cases part <;> decide
/-- Reading a field physically changes only its reader, its fresh cache and its validity cell. -/
theorem field_call (part:Fin 7) (store:Stack→List Bool) (word tail:List Bool)
    (hi:store (fieldReader part)=frame word tail) (ho:store (cache part)=[])
    (hs:store (aux .fieldScratch)=[]) (hv:store (aux .valid)=[]) :
    Runs program (8*word.length+7) (.local (.field part)) store (.local (.valid part))
      (Function.update (Function.update (Function.update store (fieldReader part) tail)
        (cache part) word) (aux .valid) [true]) := by
  simp only [fieldReader] at hi
  let before:=SemiprimeD1TensorTapeFieldBytecode.initial (frame word tail) []
  let after:SemiprimeD1StackBytecode.State F.Stack F.Label:=
    ⟨none,none,Sum.elim (SemiprimeD1TensorTapeFieldMachine.contents tail [] word) (fun _=>[true])⟩
  have hin:Rel.DataRel (fieldStack part) store before.store store:=by
    constructor
    · intro k
      rcases k with k|k
      · cases k <;> simp [fieldStack,before,SemiprimeD1TensorTapeFieldBytecode.initial,
          SemiprimeD1TensorTapeFieldMachine.contents,hi,ho,hs]
      · cases k
        exact hv
    · intro k _;rfl
  apply included_call program (fieldStack part) (Label.field part) (field_injective part)
    F.code (F.active .tagPop (none,false)) (fun _=>rfl) (.local (.field part)) (.local (.valid part))
    rfl (8*word.length+6) before after
  · rfl
  · rfl
  · exact SemiprimeD1TensorTapeFieldBytecode.framed_run word tail []
  · exact hin
  · have h0:=update_rel (fieldStack part) (field_injective part) store before.store store hin (.inl .input) tail
    have h1:=update_rel (fieldStack part) (field_injective part) store _ _ h0 (.inl .output) word
    have h2:=update_rel (fieldStack part) (field_injective part) store _ _ h1 (.inr ()) [true]
    have he:Function.update (Function.update (Function.update before.store (.inl .input) tail)
        (.inl .output) word) (.inr ()) [true]=after.store:=by
      funext k;rcases k with k|k <;> cases k <;> rfl
    simpa only [he,fieldStack,fieldReader] using h2
/-- The actual parsed field cache inclusion is injective. -/
theorem cache_injective : Function.Injective cache :=
  Sum.inr_injective.comp (Sum.inr_injective.comp Sum.inl_injective)
/-- The actual private auxiliary inclusion is injective. -/
theorem aux_injective : Function.Injective aux :=
  Sum.inr_injective.comp (Sum.inr_injective.comp Sum.inr_injective)
/-- The actual recipe work inclusion is injective. -/
theorem work_injective : Function.Injective work := Sum.inr_injective.comp Sum.inl_injective
/-- Literal parsed-field projection in the physical store view. -/
theorem data_cache (s:S.Stack→List Bool) (w:RecipeWork→List Bool) (f:Fin 7→List Bool)
    (a:Aux→List Bool) (part:Fin 7) : data s w f a (cache part)=f part := rfl
/-- Literal auxiliary projection in the physical store view. -/
theorem data_aux (s:S.Stack→List Bool) (w:RecipeWork→List Bool) (f:Fin 7→List Bool)
    (a:Aux→List Bool) (role:Aux) : data s w f a (aux role)=a role := rfl
/-- Literal recipe-register projection in the physical store view. -/
theorem data_work (s:S.Stack→List Bool) (w:RecipeWork→List Bool) (f:Fin 7→List Bool)
    (a:Aux→List Bool) (role:RecipeWork) : data s w f a (work role)=w role := rfl
/-- Exact actual output-cache update, preserving every acquired source/recipe/outer role. -/
theorem update_cache (s:S.Stack→List Bool) (w:RecipeWork→List Bool) (f:Fin 7→List Bool)
    (a:Aux→List Bool) (part:Fin 7) (word:List Bool) :
    Function.update (data s w f a) (cache part) word=data s w (Function.update f part word) a := by
  funext k
  rcases k with k|k
  · exact Function.update_of_ne (by intro h;cases h) _ _
  · rcases k with k|k
    · exact Function.update_of_ne (by intro h;cases h) _ _
    · rcases k with k|k
      · change Function.update (data s w f a) (cache part) word (cache k)=(Function.update f part word) k
        simp only [Function.update_apply,data_cache,cache_injective.eq_iff]
      · exact Function.update_of_ne (by intro h;cases h) _ _
/-- Exact actual private-work update, preserving all original source and parsed fields. -/
theorem update_aux (s:S.Stack→List Bool) (w:RecipeWork→List Bool) (f:Fin 7→List Bool)
    (a:Aux→List Bool) (role:Aux) (word:List Bool) :
    Function.update (data s w f a) (aux role) word=data s w f (Function.update a role word) := by
  funext k
  rcases k with k|k
  · exact Function.update_of_ne (by intro h;cases h) _ _
  · rcases k with k|k
    · exact Function.update_of_ne (by intro h;cases h) _ _
    · rcases k with k|k
      · exact Function.update_of_ne (by intro h;cases h) _ _
      · change Function.update (data s w f a) (aux role) word (aux k)=(Function.update a role word) k
        simp only [Function.update_apply,data_aux,aux_injective.eq_iff]
/-- Exact actual recipe-register update; no source metadata or parsed ID is overwritten. -/
theorem update_work (s:S.Stack→List Bool) (w:RecipeWork→List Bool) (f:Fin 7→List Bool)
    (a:Aux→List Bool) (role:RecipeWork) (word:List Bool) :
    Function.update (data s w f a) (work role) word=data s (Function.update w role word) f a := by
  funext k
  rcases k with k|k
  · exact Function.update_of_ne (by intro h;cases h) _ _
  · rcases k with k|k
    · change Function.update (data s w f a) (work role) word (work k)=(Function.update w role word) k
      simp only [Function.update_apply,data_work,work_injective.eq_iff]
    · exact Function.update_of_ne (by intro h;cases h) _ _
end RiemannGaussian.SemiprimeD1StackOwnerCatalogueFields
