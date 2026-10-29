/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackRecoveryCoordinatePrimitives
/-! # Both real nested-vector fields are physically parsed and retained
Each actual phase payload supplies a block vector; each actual block supplies
the retained byte cache of the real binary coordinate lookup.
-/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 65536
namespace RiemannGaussian.SemiprimeD1StackRecoveryCoordinateFields
open SemiprimeD1StackRecoveryCoordinate SemiprimeD1StackRecoveryCoordinateState
open SemiprimeD1StackRecoveryCoordinatePrimitives SemiprimeD1StackProcedureTrace
open SemiprimeSourceHistogramKeyBits (frame)
namespace Link
export SemiprimeD1StackMultiplierLink (DataRel data_update)
end Link
/-- Actual input role of each physical parser site. -/
def fieldInput (inner:Bool):Role:=if inner then .blocks else .reader
/-- Actual output role of each physical parser site. -/
def fieldOutput (inner:Bool):Role:=if inner then .cache else .blocks
/-- Fixed real parser call label. -/
def fieldPC (inner:Bool):Label:=.local (if inner then .blockField else .phaseField)
/-- Fixed actual validity-pop label. -/
def validPC (inner:Bool):Label:=.local (if inner then .blockValid else .phaseValid)
/-- The source progresses to real lookup or physical row-sentinel seeding. -/
def fieldNext (inner:Bool):Label:=.local (if inner then .lookup else .rowSeed)
/-- Physical parser input is exactly its named bank field. -/
theorem field_input (inner:Bool):fieldStack inner (.inl .input)=address (fieldInput inner):=by cases inner <;> rfl
/-- Physical parser output is exactly its named bank field. -/
theorem field_output (inner:Bool):fieldStack inner (.inl .output)=address (fieldOutput inner):=by cases inner <;> rfl
/-- One actual source Field call, with its own physical validity bit and real return. -/
theorem field_call (inner:Bool) (key:List Bool) (w:Role → List Bool) (word tail:List Bool)
    (hi:w (fieldInput inner)=frame word tail) (ho:w (fieldOutput inner)=[]) (hv:w .valid=[]):
    Runs program (8*word.length+7) (fieldPC inner) (data key w) (validPC inner)
      (data key (Function.update (Function.update (Function.update w (fieldInput inner) tail) (fieldOutput inner) word) .valid [true])):=by
  let before:=SemiprimeD1TensorTapeFieldBytecode.initial (frame word tail) []
  let after:SemiprimeD1StackBytecode.State F.Stack F.Label:=
    ⟨none,none,Sum.elim (SemiprimeD1TensorTapeFieldMachine.contents tail [] word) (fun _=>[true])⟩
  have hin:Link.DataRel (fieldStack inner) (data key w) before.store (data key w):=by
    constructor
    · intro k;rcases k with k|k
      · cases k with
        | input=>rw [field_input,data_get];exact hi
        | scratch=>exact data_scratch key w
        | output=>change data key w (fieldStack inner (.inl .output))=[];rw [field_output,data_get,ho]
      · cases k;change w .valid=[];exact hv
    · intro k _;rfl
  simp only [data_update]
  apply included_call program (fieldStack inner) (Label.field inner) (field_injective inner) F.code
    (F.active .tagPop (none,false)) (fun _=>rfl) (fieldPC inner) (validPC inner) (by cases inner <;> rfl)
    (8*word.length+6) before after _ _ rfl rfl (SemiprimeD1TensorTapeFieldBytecode.framed_run word tail []) hin
  have h0:=Link.data_update (fieldStack inner) (field_injective inner) (data key w) before.store (data key w) hin (.inl .input) tail
  have h1:=Link.data_update (fieldStack inner) (field_injective inner) (data key w) _ _ h0 (.inl .output) word
  have h2:=Link.data_update (fieldStack inner) (field_injective inner) (data key w) _ _ h1 (.inr ()) [true]
  have he:Function.update (Function.update (Function.update before.store (.inl .input) tail) (.inl .output) word) (.inr ()) [true]=after.store:=by
    funext k;rcases k with k|k <;> cases k <;> rfl
  rw [he] at h2
  cases inner <;> exact h2
/-- The actual true validity pop clears its physical field and leaves exactly parsed payloads. -/
theorem field_read (inner:Bool) (key:List Bool) (w:Role → List Bool) (word tail:List Bool)
    (hi:w (fieldInput inner)=frame word tail) (ho:w (fieldOutput inner)=[]) (hv:w .valid=[]):
    Runs program (8*word.length+8) (fieldPC inner) (data key w) (fieldNext inner)
      (data key (Function.update (Function.update w (fieldInput inner) tail) (fieldOutput inner) word)):=by
  have h0:=field_call inner key w word tail hi ho hv
  let v:=Function.update (Function.update (Function.update w (fieldInput inner) tail) (fieldOutput inner) word) .valid [true]
  have h1:=pop_run (validPC inner) (.local .abort) (.local .abort) (fieldNext inner) .valid key v [true] (by cases inner <;> rfl) (Function.update_self _ _ _)
  simp only [List.head?_cons,List.tail_cons,SemiprimeD1StackBytecode.choose] at h1
  have he:Function.update v .valid []=Function.update (Function.update w (fieldInput inner) tail) (fieldOutput inner) word:=by
    dsimp [v]
    rw [Function.update_idem,Function.update_comm (by cases inner <;> decide:fieldOutput inner≠.valid),
      Function.update_comm (by cases inner <;> decide:fieldInput inner≠.valid)]
    have hz:Function.update w .valid []=w:=by rw [←hv];exact Function.update_eq_self _ _
    rw [hz]
  rw [he] at h1
  have h:=join h0 h1
  exact h
end RiemannGaussian.SemiprimeD1StackRecoveryCoordinateFields
