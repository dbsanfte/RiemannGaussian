/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackDigitCountComponents
import RiemannGaussian.SemiprimeD1TensorTapeCodec

/-! # Actual cached-vector scan and count, including zero digit fields -/
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 16000
set_option Elab.async false
namespace RiemannGaussian.SemiprimeD1StackDigitCountLoop
open SemiprimeD1StackDigitCount SemiprimeD1StackDigitCountComponents
open SemiprimeD1StackProcedureFragments (Runs one_base)
open SemiprimeSourceHistogramKeyBits (frame)
open SemiprimeD1TensorTapeCodec (vectorBits)

/-- Every actual parsed field bit is consumed physically before the next record. -/
theorem clear_word (word bank reader count:List Bool) :
    Runs program (word.length+1) (.inl .clearWord) (data bank reader count word [] [true] [])
      (.inl .popValid) (data bank reader count [] [] [true] []) := by
  induction word with
  | nil =>
    apply one_base program _ _ (.pop .word (.inl .popValid) (.inl .clearWord) (.inl .clearWord)) _ _ rfl
    · rfl
    · funext k;cases k <;> simp [B.execute,data,Function.update]
  | cons bit word ih =>
    have h:Runs program 1 (.inl .clearWord) (data bank reader count (bit::word) [] [true] [])
        (.inl .clearWord) (data bank reader count word [] [true] []):=by
      apply one_base program _ _ (.pop .word (.inl .popValid) (.inl .clearWord) (.inl .clearWord)) _ _ rfl
      · cases bit <;> rfl
      · cases bit <;> funext k <;> cases k <;> simp [B.execute,data,Function.update]
    simpa only [List.length_cons,show 1+(word.length+1)=word.length+1+1 by omega] using h.trans ih

/-- Exact actual loop transitions, not a runtime record-count answer. -/
def loopTime : List (List Bool)→ℕ
  | [] => 1
  | word::words => 9*word.length+11+loopTime words

/-- Whole actual vector scan counts EVERY constructor, including an empty field. -/
theorem loop_run (words:List (List Bool)) (bank count:List Bool) :
    Runs program (loopTime words) (.inl .popVector) (data bank (vectorBits words) count [] [] [] [])
      (.inl .halt) (data bank [] (List.replicate words.length true++count) [] [] [] []) := by
  induction words generalizing count with
  | nil =>
    change Runs program 1 (.inl .popVector) (data bank [false] count [] [] [] [])
      (.inl .halt) (data bank [] count [] [] [] [])
    apply one_base program _ _ (.pop .reader (.inl .halt) (.inl .halt) (.inl .fieldCall)) _ _ rfl
    · rfl
    · funext k;cases k <;> simp [B.execute,data,Function.update]
  | cons word words ih =>
    have h0:Runs program 1 (.inl .popVector) (data bank (true::frame word (vectorBits words)) count [] [] [] [])
        (.inl .fieldCall) (data bank (frame word (vectorBits words)) count [] [] [] []):=by
      apply one_base program _ _ (.pop .reader (.inl .halt) (.inl .halt) (.inl .fieldCall)) _ _ rfl
      · rfl
      · funext k;cases k <;> simp [B.execute,data,Function.update]
    have h1:=field_call bank word (vectorBits words) count
    have h2:=clear_word word bank (vectorBits words) count
    have h3:Runs program 1 (.inl .popValid) (data bank (vectorBits words) count [] [] [true] [])
        (.inl .pushCount) (data bank (vectorBits words) count [] [] [] []):=by
      apply one_base program _ _ (.pop .valid (.inl .pushCount) (.inl .pushCount) (.inl .pushCount)) _ _ rfl
      · rfl
      · funext k;cases k <;> simp [B.execute,data,Function.update]
    have h4:Runs program 1 (.inl .pushCount) (data bank (vectorBits words) count [] [] [] [])
        (.inl .popVector) (data bank (vectorBits words) (true::count) [] [] [] []):=by
      apply one_base program _ _ (.push .count true (.inl .popVector)) _ _ rfl
      · rfl
      · funext k;cases k <;> simp [B.execute,data,Function.update]
    have h:=h0.trans (h1.trans (h2.trans (h3.trans (h4.trans (ih (true::count))))))
    have hc:List.replicate words.length true++true::count=List.replicate (word::words).length true++count:=by
      rw [List.length_cons,List.replicate_succ',List.append_assoc,List.singleton_append]
    rw [hc] at h
    simpa only [loopTime,vectorBits,show 1+((8*word.length+7)+((word.length+1)+(1+(1+loopTime words))))=
      9*word.length+11+loopTime words by omega] using h

/-- Physical cache byte length directly pays every parsing/counting transition. -/
theorem loopTime_le (words:List (List Bool)) : loopTime words≤6*(vectorBits words).length := by
  induction words with
  | nil => decide
  | cons word words ih =>
    simp only [loopTime,vectorBits,List.length_cons,SemiprimeSourceHistogramKeyBits.frame_length]
    omega
end RiemannGaussian.SemiprimeD1StackDigitCountLoop
