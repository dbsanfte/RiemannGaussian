/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackAllDescriptorRecordPrimitives
/-! # Actual included family calls on the directly acquired common operands -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 3000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 1000000
namespace RiemannGaussian.SemiprimeD1StackAllDescriptorRecordComponents
open SemiprimeD1StackAllDescriptorRecord SemiprimeD1StackAllDescriptorRecordWiring
open SemiprimeD1StackProcedureTrace
/-- Proof-side exact physical component result, retaining every word outside its actual operands. -/
noncomputable def after {A : Type} (stack : A→Stack) (result : A→List Bool) (d : Stack→List Bool) :
    Stack→List Bool :=Function.extend stack result d
/-- The mathematical extended store is exactly the physical included-call data relation. -/
theorem after_rel {A : Type} (stack : A→Stack) (hinj:Function.Injective stack)
    (result : A→List Bool) (d : Stack→List Bool) :
    SemiprimeD1StackMultiplierLink.DataRel stack d result (after stack result d) :=by
  constructor
  · intro k;exact hinj.extend_apply result d k
  · intro k hk
    exact Function.extend_apply' result d k (by rintro ⟨a,ha⟩;exact hk a ha)
/-- Each real family call executes its complete original compiled component,
including its genuine nested return stack; the surrounding caller is arbitrary. -/
theorem component_call {A L : Type} [DecidableEq A] (stack : A→Stack) (label : L→Label)
    (hinj:Function.Injective stack) (component : L→C.Instruction A L)
    (entry : L) (family : Family)
    (hcode:∀pc,program (label pc)=SemiprimeD1StackValidationLink.instruction stack label (component pc))
    (hcall:program (.inl (.record family))=.call (label entry) (.inl (.clear 0)))
    (time : Nat) (before result : C.State A L) (d : Stack→List Bool)
    (hp:before.pc=some entry) (hf:before.frames=[]) (hq:result.pc=none) (hg:result.frames=[])
    (hd:∀k,d (stack k)=before.data k)
    (hr:C.run component time before=some result) :
    Runs program (time+1) (.inl (.record family)) d (.inl (.clear 0)) (after stack result.data d) :=by
  apply SemiprimeD1StackProcedureCallsTrace.included_call program stack label hinj component entry hcode
    (.inl (.record family)) (.inl (.clear 0)) hcall time before result d (after stack result.data d)
    hp hf hq hg hr
  · exact ⟨hd,fun _ _=>rfl⟩
  · exact after_rel stack hinj result.data d
private theorem metadata_initial {K L : Type}
    (s:SemiprimeD1StackStaticTable.Static K L) (embed:SemiprimeD1StackDescriptorRecord.Stack K→Private)
    (raw:Fin 6→List Bool) (bank hist out:List Bool) (k:SemiprimeD1StackDescriptorRecord.Stack K) :
    cleanData raw bank hist out ((metadataAlias k).elim (privateStack (embed k)) Sum.inl)=
      (SemiprimeD1StackDescriptorRecord.initial s (fun _=>[]) raw bank hist out).data k :=by
  rcases k with k|k
  · rcases k with k|k
    · rcases k with k|k
      · rfl
      · rcases k with k|k
        · rfl
        · rcases k with k|k
          · cases k <;> rfl
          · cases k <;> rfl
    · rcases k with k|k
      · cases k <;> rfl
      · cases k <;> rfl
  · rcases k with k|k <;> rfl
/-- Actual139-role input client starts with only the shared acquired fields and scope. -/
theorem input_initial (raw:Fin 6→List Bool) (bank hist out:List Bool) (k:I.Stack) :
    cleanData raw bank hist out (inputStack k)=
      (SemiprimeD1StackInputDescriptorRecord.initial (fun _=>[]) raw bank hist out).data k :=
  metadata_initial SemiprimeD1StackPublicInputTable.static Sum.inl raw bank hist out k
/-- Actual137-role carry client starts without a template/count/table supplier. -/
theorem carry_initial (raw:Fin 6→List Bool) (bank hist out:List Bool) (k:A.Stack) :
    cleanData raw bank hist out (carryStack k)=
      (SemiprimeD1StackCarryDescriptorRecord.initial (fun _=>[]) raw bank hist out).data k :=
  metadata_initial SemiprimeD1StackPublicCarryTable.static (fun k=>.inr (.inl k)) raw bank hist out k
private theorem selected_initial {K L : Type}
    (s:SemiprimeD1StackStaticTable.Static K L) (embed:SemiprimeD1StackSelectedDescriptorRecord.Stack K→Private)
    (raw:Fin 6→List Bool) (bank hist out:List Bool) (k:SemiprimeD1StackSelectedDescriptorRecord.Stack K) :
    cleanData raw bank hist out ((selectedAlias k).elim (privateStack (embed k)) Sum.inl)=
      (SemiprimeD1StackSelectedDescriptorRecord.initial s (fun _=>[]) raw [] [] bank hist out).data k :=by
  rcases k with k|k
  · rcases k with k|k
    · rcases k with k|k
      · rcases k with k|k
        · rfl
        · rcases k with k|k
          · rfl
          · rcases k with k|k
            · cases k <;> rfl
            · cases k <;> rfl
      · rcases k with k|k
        · cases k <;> rfl
        · cases k <;> rfl
    · rcases k with k|k
      · fin_cases k <;> rfl
      · rfl
  · cases k <;> rfl
/-- Both original scale codewords are shared; computed selectors start physically empty. -/
theorem scale_initial (raw:Fin 6→List Bool) (bank hist out:List Bool) (k:S.Stack) :
    cleanData raw bank hist out (scaleStack k)=
      (SemiprimeD1StackScaleDescriptorRecord.initial (fun _=>[]) raw [] [] bank hist out).data k :=
  selected_initial SemiprimeD1StackPublicScaleTable.static (fun k=>.inr (.inr (.inl k))) raw bank hist out k
/-- Both original transform codewords are shared; no supplied singleton flag enters. -/
theorem transform_initial (raw:Fin 6→List Bool) (bank hist out:List Bool) (k:T.Stack) :
    cleanData raw bank hist out (transformStack k)=
      (SemiprimeD1StackTransformDescriptorRecord.initial (fun _=>[]) raw [] [] bank hist out).data k :=
  selected_initial SemiprimeD1StackPublicTransformTable.static (fun k=>.inr (.inr (.inr (.inl k)))) raw bank hist out k
/-- Product source receives only the original shared binary N and acquired scope. -/
theorem product_initial (raw:Fin 6→List Bool) (bank hist out:List Bool) (k:P.Stack) :
    cleanData raw bank hist out (productStack k)=
      (SemiprimeD1StackProductRecord.initial (raw 0) bank hist out).data k :=by
  rcases k with k|k
  · rcases k with k|k
    · rfl
    · cases k <;> rfl
  · rcases k with k|k <;> cases k <;> rfl
/-- Literal Boolean source receives the same actual scope and caller accumulators. -/
theorem boolean_initial (mode:SemiprimeD1StackBooleanEntry.Mode)
    (raw:Fin 6→List Bool) (bank hist out:List Bool) (k:B.Stack) :
    cleanData raw bank hist out (booleanStack k)=
      (SemiprimeD1StackBooleanRecord.initial mode bank hist out).data k :=by
  rcases k with k|k
  · rfl
  · rcases k with k|k <;> cases k <;> rfl
/-- Boundary source starts with only the shared original binary N, actual scope and caller bytes. -/
theorem boundary_initial (raw:Fin 6→List Bool) (bank hist out:List Bool) (k:Z.Stack) :
    cleanData raw bank hist out (boundaryStack k)=
      (SemiprimeD1StackBoundaryRecord.initial (raw 0) bank hist out).data k :=by
  rcases k with k|k
  · rcases k with k|k
    · rcases k with k|k
      · rcases k with k|k
        · cases k <;> rfl
        · rcases k with k|k
          · rcases k with k|k
            · cases k <;> rfl
            · fin_cases k <;> rfl
          · cases k;rfl
      · rcases k with k|k
        · cases k <;> rfl
        · fin_cases k <;> rfl
    · cases k <;> rfl
  · rcases k with k|k <;> cases k <;> rfl
/-- Common/caller bytes after an actual included family trace are determined
by its physically aliased operands; untouched common words retain their bytes. -/
theorem after_common {A : Type} (stack:A→Stack) (hinj:Function.Injective stack)
    (result:A→List Bool) (d:Stack→List Bool) (expected:Common→List Bool)
    (used:∀a c,stack a=Sum.inl c→ result a=expected c)
    (unused:∀c,(∀a,stack a≠Sum.inl c)→d (Sum.inl c)=expected c) :
    ∀c,after stack result d (Sum.inl c)=expected c :=by
  intro c
  by_cases h:∃a,stack a=Sum.inl c
  · obtain ⟨a,ha⟩:=h
    rw [←ha]
    exact (hinj.extend_apply result d a).trans (used a c ha)
  · exact (Function.extend_apply' result d (Sum.inl c) h).trans
      (unused c (by intro a ha;exact h ⟨a,ha⟩))
end RiemannGaussian.SemiprimeD1StackAllDescriptorRecordComponents
