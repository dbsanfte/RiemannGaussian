/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackDigitCount

/-! # Actual cache copying and field-parser procedure calls -/
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 16000
set_option Elab.async false
namespace RiemannGaussian.SemiprimeD1StackDigitCountComponents
open SemiprimeD1StackDigitCount
open SemiprimeD1StackProcedureFragments (Runs included_call)
open SemiprimeSourceHistogramKeyBits (frame)

/-- Real Copy source projection, not a cache-reader callback. -/
theorem copy_input (bank:List Bool) : Link.DataRel copyStack (data bank [] [] [] [] [] [])
    (SemiprimeD1StackCopy.payload bank [] []) (data bank [] [] [] [] [] []) := by
  constructor
  · intro k;fin_cases k <;> rfl
  · intro k _;rfl

/-- The real copied bank determines the actual reader, preserving the original. -/
theorem copy_output (bank:List Bool) : Link.DataRel copyStack (data bank [] [] [] [] [] [])
    (SemiprimeD1StackCopy.payload bank bank []) (data bank bank [] [] [] [] []) := by
  constructor
  · intro k;fin_cases k <;> rfl
  · intro k hk
    cases k with
    | bank => exact False.elim (hk 0 rfl)
    | reader => exact False.elim (hk 1 rfl)
    | copyScratch => exact False.elim (hk 2 rfl)
    | count => rfl
    | word => rfl
    | fieldScratch => rfl
    | valid => rfl

/-- Actual whole-vector copy with a real included call and return. -/
theorem copy_call (bank:List Bool) :
    Runs program (5*bank.length+4) (.inl .main) (data bank [] [] [] [] [] []) (.inl .popVector)
      (data bank bank [] [] [] [] []) := by
  apply included_call program copyStack copyLabel copyStack_injective SemiprimeD1StackCopy.code 0
    (fun _=>rfl) (.inl .main) (.inl .popVector) rfl (5*bank.length+3)
    (SemiprimeD1StackCopy.state 0 none bank [] []) (SemiprimeD1StackCopy.done bank bank)
  · rfl
  · rfl
  · simpa only [List.append_nil] using SemiprimeD1StackCopy.copy_words bank [] none
  · exact copy_input bank
  · exact copy_output bank

/-- The actual vector-field reader starts at the actual remaining field bytes. -/
theorem field_input (bank word tail count:List Bool) :
    Link.DataRel fieldStack (data bank (frame word tail) count [] [] [] [])
      (Field.initial (frame word tail) []).store (data bank (frame word tail) count [] [] [] []) := by
  constructor
  · intro k
    cases k with
    | inl k => cases k <;> rfl
    | inr k => cases k;rfl
  · intro k _;rfl

/-- Real parser output records its actual copied field and actual true-valid bit. -/
theorem field_output (bank word tail count:List Bool) :
    Link.DataRel fieldStack (data bank (frame word tail) count [] [] [] [])
      (Sum.elim (SemiprimeD1TensorTapeFieldMachine.contents tail [] word) (fun _=>[true]))
      (data bank tail count word [] [true] []) := by
  constructor
  · intro k
    cases k with
    | inl k => cases k <;> rfl
    | inr k => cases k;rfl
  · intro k hk
    cases k with
    | bank => rfl
    | count => rfl
    | copyScratch => rfl
    | reader => exact False.elim (hk (.inl .input) rfl)
    | word => exact False.elim (hk (.inl .output) rfl)
    | fieldScratch => exact False.elim (hk (.inl .scratch) rfl)
    | valid => exact False.elim (hk (.inr ()) rfl)

/-- Every actual digit field is physically read/copied, including an empty zero field. -/
theorem field_call (bank word tail count:List Bool) :
    Runs program (8*word.length+7) (.inl .fieldCall) (data bank (frame word tail) count [] [] [] [])
      (.inl .clearWord) (data bank tail count word [] [true] []) := by
  apply included_call program fieldStack fieldLabel fieldStack_injective Field.code
    (Field.active .tagPop (none,false)) (fun _=>rfl) (.inl .fieldCall) (.inl .clearWord) rfl
    (8*word.length+6) (Field.initial (frame word tail) [])
    (⟨none,none,Sum.elim (SemiprimeD1TensorTapeFieldMachine.contents tail [] word) (fun _=>[true])⟩:B.State Field.Stack Field.Label)
    (data bank (frame word tail) count [] [] [] []) (data bank tail count word [] [true] [])
  · rfl
  · rfl
  · exact SemiprimeD1TensorTapeFieldBytecode.framed_run word tail []
  · exact field_input bank word tail count
  · exact field_output bank word tail count
end RiemannGaussian.SemiprimeD1StackDigitCountComponents
