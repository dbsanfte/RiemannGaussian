/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackBooleanDescriptorRecordEncoding
/-! # Exact physical parser, unary tag and retained-record store updates -/
set_option autoImplicit false
set_option Elab.async false
namespace RiemannGaussian.SemiprimeD1StackBooleanDescriptorRecordView
open SemiprimeD1StackBooleanDescriptorRecord
/-- A cached field write touches exactly one finite original descriptor slot. -/
theorem update_cache (base : R.Stack→List Bool) (words : Fin 5→List Bool)
    (reader valid tagReader value : List Bool) (part : Fin 5) :
    Function.update (data base words reader valid tagReader) (cache part) value=
      data base (Function.update words part value) reader valid tagReader := by
  funext k
  by_cases hk:k=cache part
  · subst k
    rw [Function.update_self]
    change value=(Function.update words part value) part
    rw [Function.update_self]
  · rw [Function.update_of_ne hk]
    cases k with
    | inl k=>rfl
    | inr k=>cases k with
      | inl j=>
        have hj:j≠part:=by intro h;subst j;exact hk rfl
        change words j=(Function.update words part value) j
        rw [Function.update_of_ne hj]
      | inr j=>cases j <;> rfl
/-- Reader consumption preserves every cached coordinate and record accumulator. -/
theorem update_reader (base : R.Stack→List Bool) (words : Fin 5→List Bool)
    (reader valid tagReader next : List Bool) :
    Function.update (data base words reader valid tagReader) (aux .reader) next=
      data base words next valid tagReader := by
  funext k;rcases k with k|k|k <;> first | rfl | cases k <;> rfl
/-- Parser validity is a physically allocated and consumed Boolean cell. -/
theorem update_valid (base : R.Stack→List Bool) (words : Fin 5→List Bool)
    (reader valid tagReader next : List Bool) :
    Function.update (data base words reader valid tagReader) (aux .valid) next=
      data base words reader next tagReader := by
  funext k;rcases k with k|k|k <;> first | rfl | cases k <;> rfl
/-- Unary dispatch pops the copied tag rather than decoding a native mode. -/
theorem update_tagReader (base : R.Stack→List Bool) (words : Fin 5→List Bool)
    (reader valid tagReader next : List Bool) :
    Function.update (data base words reader valid tagReader) (aux .tagReader) next=
      data base words reader valid next := by
  funext k;rcases k with k|k|k <;> first | rfl | cases k <;> rfl
/-- The frozen record initialization is independent of its finite entry label. -/
theorem recordInput_mode (mode : SemiprimeD1StackBooleanEntry.Mode) (bank hist out : List Bool) :
    recordInput bank hist out=(R.initial mode bank hist out).data := rfl
end RiemannGaussian.SemiprimeD1StackBooleanDescriptorRecordView
