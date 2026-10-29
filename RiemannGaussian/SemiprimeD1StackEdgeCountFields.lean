/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackEdgeCount
/-! # Actual six physical field reads, validity pops and payload drains -/
set_option autoImplicit false
set_option maxHeartbeats 1500000
set_option maxRecDepth 32768
namespace RiemannGaussian.SemiprimeD1StackEdgeCountFields
open SemiprimeD1StackEdgeCount
open SemiprimeD1StackProcedureFragments (Runs one_base included_call)
open SemiprimeSourceHistogramKeyBits (frame)

/-- Actual preserving whole-edge-tape Copy, not a read-only byte-size formula. -/
theorem copy_call (bank : List Bool) :
    Runs program (5*bank.length+4) (.inl .start) (data bank [] [] [] [] [] []) (.inl .peekRecord)
      (data bank bank [] [] [] [] []) := by
  apply included_call program copyStack copyLabel SemiprimeD1StackDigitCount.copyStack_injective
    SemiprimeD1StackCopy.code 0 (fun _=>rfl) (.inl .start) (.inl .peekRecord) rfl (5*bank.length+3)
    (SemiprimeD1StackCopy.state 0 none bank [] []) (SemiprimeD1StackCopy.done bank bank)
  · rfl
  · rfl
  · simpa only [List.append_nil] using SemiprimeD1StackCopy.copy_words bank [] none
  · exact SemiprimeD1StackDigitCountComponents.copy_input bank
  · exact SemiprimeD1StackDigitCountComponents.copy_output bank

/-- Every field, including the empty side field, is actually parsed and copied. -/
theorem field_call (part : Fin 6) (bank word tail count wire : List Bool) :
    Runs program (8*word.length+7) (.inl (.read part)) (data bank (frame word tail) count [] [] [] wire)
      (.inl (.valid part)) (data bank tail count word [] [true] wire) := by
  apply included_call program fieldStack fieldLabel SemiprimeD1StackDigitCount.fieldStack_injective
    Field.code (Field.active .tagPop (none,false)) (fun _=>rfl) (.inl (.read part)) (.inl (.valid part)) rfl
    (8*word.length+6) (SemiprimeD1TensorTapeFieldBytecode.initial (frame word tail) [])
    (⟨none,none,Sum.elim (SemiprimeD1TensorTapeFieldMachine.contents tail [] word) (fun _=>[true])⟩:
      B.State Field.Stack Field.Label)
  · rfl
  · rfl
  · exact SemiprimeD1TensorTapeFieldBytecode.framed_run word tail []
  · constructor
    · intro k
      cases k with
      | inl k => cases k <;> rfl
      | inr k => cases k; rfl
    · intro k hk; rfl
  · constructor
    · intro k
      cases k with
      | inl k => cases k <;> rfl
      | inr k => cases k; rfl
    · intro k hk
      cases k with
      | bank => rfl
      | count => rfl
      | copyScratch => rfl
      | reader => exact False.elim (hk (.inl .input) rfl)
      | word => exact False.elim (hk (.inl .output) rfl)
      | fieldScratch => exact False.elim (hk (.inl .scratch) rfl)
      | valid => exact False.elim (hk (.inr ()) rfl)

/-- Acquired field-validity is physically consumed before any next-field control. -/
theorem pop_valid (part : Fin 6) (bank reader count word wire : List Bool) :
    Runs program 1 (.inl (.valid part)) (data bank reader count word [] [true] wire)
      (.inl (.clear part)) (data bank reader count word [] [] wire) := by
  apply one_base program _ _ (.pop .valid (.inl .abort) (.inl .abort) (.inl (.clear part))) _ _ rfl
  · rfl
  · funext k; cases k <;> simp [B.execute,SemiprimeD1StackDigitCount.data,Function.update]

/-- Every parsed payload is physically cleared before the next of SIX fields. -/
theorem clear_word (part : Fin 6) (word bank reader count wire : List Bool) :
    Runs program (word.length+1) (.inl (.clear part)) (data bank reader count word [] [] wire)
      (afterClear part) (data bank reader count [] [] [] wire) := by
  induction word with
  | nil =>
    apply one_base program _ _ (.pop .word (afterClear part) (.inl (.clear part)) (.inl (.clear part))) _ _ rfl
    · rfl
    · funext k; cases k <;> simp [B.execute,SemiprimeD1StackDigitCount.data,Function.update]
  | cons bit word ih =>
    have h : Runs program 1 (.inl (.clear part)) (data bank reader count (bit::word) [] [] wire)
        (.inl (.clear part)) (data bank reader count word [] [] wire) := by
      apply one_base program _ _ (.pop .word (afterClear part) (.inl (.clear part)) (.inl (.clear part))) _ _ rfl
      · cases bit <;> rfl
      · cases bit <;> funext k <;> cases k <;> simp [B.execute,SemiprimeD1StackDigitCount.data,Function.update]
    simpa only [List.length_cons,show 1+(word.length+1)=word.length+1+1 by omega] using h.trans ih

/-- Closed actual one-field round: parser, real validity pop and complete drain. -/
theorem field_run (part : Fin 6) (bank word tail count wire : List Bool) :
    Runs program (9*word.length+9) (.inl (.read part)) (data bank (frame word tail) count [] [] [] wire)
      (afterClear part) (data bank tail count [] [] [] wire) := by
  have h:=(field_call part bank word tail count wire).trans
    ((pop_valid part bank tail count word wire).trans (clear_word part word bank tail count wire))
  simpa only [show (8*word.length+7)+(1+(word.length+1))=9*word.length+9 by omega] using h

/-- Exact sum of the SIX physical field-round transition counts. -/
def fieldsTime (words : Record) : ℕ :=
  (9*(words 0).length+9)+(9*(words 1).length+9)+(9*(words 2).length+9)+
    (9*(words 3).length+9)+(9*(words 4).length+9)+(9*(words 5).length+9)

/-- All six original fields execute before the count marker can be pushed. -/
theorem fields_run (words : Record) (bank tail count wire : List Bool) :
    Runs program (fieldsTime words) (.inl (.read 0)) (data bank (record words tail) count [] [] [] wire)
      (.inl .pushCount) (data bank tail count [] [] [] wire) := by
  have h0:=field_run 0 bank (words 0)
    (frame (words 1) (frame (words 2) (frame (words 3) (frame (words 4) (frame (words 5) tail))))) count wire
  have h1:=field_run 1 bank (words 1) (frame (words 2) (frame (words 3) (frame (words 4) (frame (words 5) tail)))) count wire
  have h2:=field_run 2 bank (words 2) (frame (words 3) (frame (words 4) (frame (words 5) tail))) count wire
  have h3:=field_run 3 bank (words 3) (frame (words 4) (frame (words 5) tail)) count wire
  have h4:=field_run 4 bank (words 4) (frame (words 5) tail) count wire
  have h5:=field_run 5 bank (words 5) tail count wire
  simp only [afterClear] at h0 h1 h2 h3 h4 h5
  norm_num at h0 h1 h2 h3 h4 h5
  exact (((((h0.trans h1).trans h2).trans h3).trans h4).trans h5)

end RiemannGaussian.SemiprimeD1StackEdgeCountFields
