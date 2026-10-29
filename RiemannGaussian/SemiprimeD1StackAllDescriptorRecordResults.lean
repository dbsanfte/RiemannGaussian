/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackAllDescriptorRecordCalls
/-! # Exact retained original common fields and chronological component history -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 3000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 1000000
namespace RiemannGaussian.SemiprimeD1StackAllDescriptorRecordResults
open SemiprimeD1StackAllDescriptorRecord SemiprimeD1StackAllDescriptorRecordWiring
open SemiprimeD1StackAllDescriptorRecordComponents
open SemiprimeD1TensorTapeCodec (vectorBits)
private theorem routed_common {A:Type} (targets:A→Option Common) (embed:A→Private)
    (hinj:Function.Injective (fun a=>(targets a).elim (privateStack (embed a)) Sum.inl))
    (result:A→List Bool) (raw:Fin 6→List Bool) (bank hist out newHist:List Bool)
    (hh:∃a,targets a=some .history)
    (used:∀a c,targets a=some c→ result a=commonData raw bank newHist out c) :
    ∀c,after (fun a=>(targets a).elim (privateStack (embed a)) Sum.inl) result
      (cleanData raw bank hist out) (Sum.inl c)=commonData raw bank newHist out c :=by
  apply after_common _ hinj result (cleanData raw bank hist out) (commonData raw bank newHist out)
  · intro a c h
    cases ht:targets a with
    | none=>simp only [ht,Option.elim_none,privateStack] at h;cases h
    | some b=>
      simp only [ht,Option.elim_some] at h
      have he:b=c:=Sum.inl.inj h
      subst b
      exact used a c ht
  · intro c hk
    cases c with
    | history=>
      obtain ⟨a,ha⟩:=hh
      exact (hk a (by simp only [ha,Option.elim_some])).elim
    | source i|bank|output|tagReader|copyScratch=>rfl
private theorem metadata_result {K L:Type} [DecidableEq K]
    (s:SemiprimeD1StackStaticTable.Static K L) (sourceMap:K→Option (Fin 6))
    (raw:Fin 6→List Bool) (words:List (List Bool)) (answer:List Bool→Bool) (hist out:List Bool)
    (k:SemiprimeD1StackDescriptorRecord.Stack K) (c:Common) (h:metadataAlias k=some c) :
    (SemiprimeD1StackDescriptorRecord.done s sourceMap raw words answer hist out).data k=
      commonData raw (vectorBits words)
        ((SemiprimeD1StackDescriptorRecord.done s sourceMap raw words answer hist out).data
          SemiprimeD1StackDescriptorRecord.history) out c :=by
  have hv:=metadata_key k c h
  cases c with
  | source i|bank|history|output=>
    have he:=Option.some.inj hv
    subst k
    rfl
  | tagReader|copyScratch=>cases hv
private theorem selected_result {K L:Type} [DecidableEq K]
    (s:SemiprimeD1StackStaticTable.Static K L) (sourceMap:K→Option (Fin 6))
    (raw:Fin 6→List Bool) (second inverse:Bool) (words:List (List Bool)) (answer:List Bool→Bool) (hist out:List Bool)
    (k:SemiprimeD1StackSelectedDescriptorRecord.Stack K) (c:Common) (h:selectedAlias k=some c) :
    (SemiprimeD1StackSelectedDescriptorRecord.done s sourceMap raw second inverse words answer hist out).data k=
      commonData raw (vectorBits words)
        ((SemiprimeD1StackSelectedDescriptorRecord.done s sourceMap raw second inverse words answer hist out).data
          SemiprimeD1StackSelectedDescriptorRecord.history) out c :=by
  have hv:=selected_key k c h
  cases c with
  | source i=>
    fin_cases i <;> (have he:=Option.some.inj hv;subst k;rfl)
  | bank|history|output=>
    have he:=Option.some.inj hv
    subst k
    rfl
  | tagReader|copyScratch=>cases hv
/-- Input call retains all original acquired fields/scope/output and changes only common history. -/
theorem input_common (raw:Fin 6→List Bool) (words:List (List Bool)) (hist out:List Bool) :
    ∀c,after inputStack (SemiprimeD1StackInputDescriptorRecordExecution.done raw words hist out).data
      (cleanData raw (vectorBits words) hist out) (.inl c)=commonData raw (vectorBits words)
        ((SemiprimeD1StackInputDescriptorRecordExecution.done raw words hist out).data SemiprimeD1StackDescriptorRecord.history) out c :=by
  apply routed_common metadataAlias Sum.inl inputStack_injective _ raw (vectorBits words) hist out _
  · exact ⟨SemiprimeD1StackDescriptorRecord.history,rfl⟩
  · exact metadata_result _ _ raw words _ hist out
/-- Carry call retains every source/caller byte outside the actual appended row history. -/
theorem carry_common (raw:Fin 6→List Bool) (words:List (List Bool)) (hist out:List Bool) :
    ∀c,after carryStack (SemiprimeD1StackCarryDescriptorRecordExecution.done raw words hist out).data
      (cleanData raw (vectorBits words) hist out) (.inl c)=commonData raw (vectorBits words)
        ((SemiprimeD1StackCarryDescriptorRecordExecution.done raw words hist out).data SemiprimeD1StackDescriptorRecord.history) out c :=by
  apply routed_common metadataAlias (fun k=>.inr (.inl k)) carryStack_injective _ raw (vectorBits words) hist out _
  · exact ⟨SemiprimeD1StackDescriptorRecord.history,rfl⟩
  · exact metadata_result _ _ raw words _ hist out
/-- Scale's original raw codes remain shared; its computed selector remains private. -/
theorem scale_common (raw:Fin 6→List Bool) (inverse:Bool) (words:List (List Bool)) (hist out:List Bool) :
    ∀c,after scaleStack (SemiprimeD1StackScaleDescriptorRecord.done raw inverse words hist out).data
      (cleanData raw (vectorBits words) hist out) (.inl c)=commonData raw (vectorBits words)
        ((SemiprimeD1StackScaleDescriptorRecord.done raw inverse words hist out).data SemiprimeD1StackSelectedDescriptorRecord.history) out c :=by
  apply routed_common selectedAlias (fun k=>.inr (.inr (.inl k))) scaleStack_injective _ raw (vectorBits words) hist out _
  · exact ⟨SemiprimeD1StackSelectedDescriptorRecord.history,rfl⟩
  · exact selected_result _ _ raw false inverse words _ hist out
/-- Both transform flags remain private while every original raw field is retained. -/
theorem transform_common (raw:Fin 6→List Bool) (second inverse:Bool) (words:List (List Bool)) (hist out:List Bool) :
    ∀c,after transformStack (SemiprimeD1StackTransformDescriptorRecord.done raw second inverse words hist out).data
      (cleanData raw (vectorBits words) hist out) (.inl c)=commonData raw (vectorBits words)
        ((SemiprimeD1StackTransformDescriptorRecord.done raw second inverse words hist out).data SemiprimeD1StackSelectedDescriptorRecord.history) out c :=by
  apply routed_common selectedAlias (fun k=>.inr (.inr (.inr (.inl k)))) transformStack_injective _ raw (vectorBits words) hist out _
  · exact ⟨SemiprimeD1StackSelectedDescriptorRecord.history,rfl⟩
  · exact selected_result _ _ raw second inverse words _ hist out
/-- Product compilation retains original N/scope/caller fields and updates only common history. -/
theorem product_common (raw:Fin 6→List Bool) (words:List (List Bool)) (hist out:List Bool) :
    ∀c,after productStack (SemiprimeD1StackProductRecord.done (raw 0) words hist out).data
      (cleanData raw (vectorBits words) hist out) (.inl c)=commonData raw (vectorBits words)
        ((SemiprimeD1StackProductRecord.done (raw 0) words hist out).data SemiprimeD1StackProductRecord.history) out c :=by
  apply routed_common productAlias (fun k=>.inr (.inr (.inr (.inr (.inl k))))) productStack_injective _ raw (vectorBits words) hist out _
  · exact ⟨SemiprimeD1StackProductRecord.history,rfl⟩
  · intro k c h
    have hv:=product_key k c h
    cases c with
    | source i=>
      fin_cases i
      · have he:=Option.some.inj hv;subst k;rfl
      all_goals cases hv
    | bank|history|output=>have he:=Option.some.inj hv;subst k;rfl
    | tagReader|copyScratch=>cases hv
/-- Both physical boundary branches retain all common source/caller fields. -/
theorem boundary_common (raw:Fin 6→List Bool) (words:List (List Bool)) (hist out:List Bool) :
    ∀c,after boundaryStack (SemiprimeD1StackBoundaryRecord.done (raw 0) words hist out).data
      (cleanData raw (vectorBits words) hist out) (.inl c)=commonData raw (vectorBits words)
        ((SemiprimeD1StackBoundaryRecord.done (raw 0) words hist out).data SemiprimeD1StackBoundaryRecord.history) out c :=by
  apply routed_common boundaryAlias (fun k=>.inr (.inr (.inr (.inr (.inr (.inl k)))))) boundaryStack_injective _ raw (vectorBits words) hist out _
  · exact ⟨SemiprimeD1StackBoundaryRecord.history,rfl⟩
  · intro k c h
    have hv:=boundary_key k c h
    cases c with
    | source i=>
      fin_cases i
      · have he:=Option.some.inj hv;subst k;rfl
      all_goals cases hv
    | bank|history|output=>have he:=Option.some.inj hv;subst k;rfl
    | tagReader|copyScratch=>cases hv
/-- The three literal Boolean table modes preserve original N and all descriptor coordinates too. -/
theorem boolean_common (mode:SemiprimeD1StackBooleanEntry.Mode)
    (raw:Fin 6→List Bool) (words:List (List Bool)) (hist out:List Bool) :
    ∀c,after booleanStack (SemiprimeD1StackBooleanRecord.done mode words hist out).data
      (cleanData raw (vectorBits words) hist out) (.inl c)=commonData raw (vectorBits words)
        ((SemiprimeD1StackBooleanRecord.done mode words hist out).data SemiprimeD1StackBooleanRecord.history) out c :=by
  apply routed_common booleanAlias (fun k=>.inr (.inr (.inr (.inr (.inr (.inr k)))))) booleanStack_injective _ raw (vectorBits words) hist out _
  · exact ⟨SemiprimeD1StackBooleanRecord.history,rfl⟩
  · intro k c h
    have hv:=boolean_key k c h
    cases c with
    | source i|tagReader|copyScratch=>cases hv
    | bank|history|output=>have he:=Option.some.inj hv;subst k;rfl
end RiemannGaussian.SemiprimeD1StackAllDescriptorRecordResults
