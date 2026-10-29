/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackCachePhaseBankPrimitives
/-! # Real matching reference/child Field acquisitions
Both current operands are read from actual framed outer-vector payloads.
Their validity flags are real parsed singleton bits and physically consumed.
-/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackCachePhaseBankFields
open SemiprimeD1StackCachePhaseBank SemiprimeD1StackCachePhaseBankPrimitives
open SemiprimeD1StackProcedureTrace
open SemiprimeSourceHistogramKeyBits (frame)
/-- Actual fixed parser call site. -/
def fieldPC (children:Bool):Control:=if children then .childField else .referenceField
/-- Actual physical valid-pop site. -/
def validPC (children:Bool):Control:=if children then .childValid else .referenceValid
/-- Only a real successful parse reaches the following source instruction. -/
def fieldNext (children:Bool):Label:=.local (if children then .phase else .childHeader)
local notation "ctl"=>Label.local
/-- Each real Field call preserves every other246-role word and pays its own physical call/return. -/
theorem field_call (children:Bool) (before:Stack→List Bool) (word tail:List Bool)
    (hi:before (fieldStack children (.inl .input))=frame word tail)
    (ho:before (fieldStack children (.inl .output))=[]) (hs:before scratch=[]) (hv:before (aux .valid)=[]):
    Runs program (8*word.length+7) (ctl (fieldPC children)) before (ctl (validPC children))
      (Function.update (Function.update (Function.update before (fieldStack children (.inl .input)) tail)
        (fieldStack children (.inl .output)) word) (aux .valid) [true]):=by
  let start:=SemiprimeD1TensorTapeFieldBytecode.initial (frame word tail) []
  let stop:SemiprimeD1StackBytecode.State Field.Stack Field.Label:=
    ⟨none,none,Sum.elim (SemiprimeD1TensorTapeFieldMachine.contents tail [] word) (fun _=>[true])⟩
  have hin:Link.DataRel (fieldStack children) before start.store before:=by
    constructor
    · intro k;rcases k with k|k
      · cases k with
        | input=>exact hi
        | scratch=>exact hs
        | output=>exact ho
      · cases k;exact hv
    · intro k _;rfl
  have h0:=Link.data_update (fieldStack children) (field_injective children) before start.store before hin (.inl .input) tail
  have h1:=Link.data_update (fieldStack children) (field_injective children) before _ _ h0 (.inl .output) word
  have h2:=Link.data_update (fieldStack children) (field_injective children) before _ _ h1 (.inr ()) [true]
  have he:Function.update (Function.update (Function.update start.store (.inl .input) tail) (.inl .output) word) (.inr ()) [true]=stop.store:=by
    funext k;rcases k with k|k <;> cases k <;> rfl
  rw [he] at h2
  exact included_call program (fieldStack children) (Label.field children) (field_injective children) Field.code
    (Field.active .tagPop (none,false)) (fun _=>rfl) (ctl (fieldPC children)) (ctl (validPC children))
    (by cases children <;> rfl) (8*word.length+6) start stop _ _ rfl rfl
    (SemiprimeD1TensorTapeFieldBytecode.framed_run word tail []) hin h2
/-- Real validity pop restores the empty flag; no externally supplied validity enters runtime. -/
theorem field_read (children:Bool) (before:Stack→List Bool) (word tail:List Bool)
    (hi:before (fieldStack children (.inl .input))=frame word tail)
    (ho:before (fieldStack children (.inl .output))=[]) (hs:before scratch=[]) (hv:before (aux .valid)=[]):
    Runs program (8*word.length+8) (ctl (fieldPC children)) before (fieldNext children)
      (Function.update (Function.update before (fieldStack children (.inl .input)) tail)
        (fieldStack children (.inl .output)) word):=by
  have h0:=field_call children before word tail hi ho hs hv
  let v:=Function.update (Function.update (Function.update before (fieldStack children (.inl .input)) tail)
    (fieldStack children (.inl .output)) word) (aux .valid) [true]
  have h1:=pop_run (validPC children) (ctl .abort) (ctl .abort) (fieldNext children) (aux .valid) v [true]
    (by cases children <;> rfl) (Function.update_self _ _ _)
  simp only [List.head?_cons,List.tail_cons,SemiprimeD1StackBytecode.choose] at h1
  have he:Function.update v (aux .valid) []=
      Function.update (Function.update before (fieldStack children (.inl .input)) tail) (fieldStack children (.inl .output)) word:=by
    dsimp [v]
    rw [Function.update_idem,Function.update_comm (by cases children <;> decide:fieldStack children (.inl .output)≠aux .valid),
      Function.update_comm (by cases children <;> decide:fieldStack children (.inl .input)≠aux .valid)]
    have hz:Function.update before (aux .valid) []=before:=by rw [←hv];exact Function.update_eq_self _ _
    rw [hz]
  rw [he] at h1
  have h:=join h0 h1
  exact h
end RiemannGaussian.SemiprimeD1StackCachePhaseBankFields
