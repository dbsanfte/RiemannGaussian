/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackPublicInputComponents
/-! # Executed Boolean branches and all physical cleanup of PublicInput52 -/
set_option autoImplicit false
set_option synthInstance.maxSize 8192
set_option maxHeartbeats 1800000
set_option maxRecDepth 32768
namespace RiemannGaussian.SemiprimeD1StackPublicInputControl
open SemiprimeD1StackPublicInput SemiprimeD1StackPublicInputState
open SemiprimeD1StackProcedureFragments (Runs one_base)
/-- Every residual word bit is actually popped before final bound cleanup. -/
theorem clear_word (bits indexWord bd raw reader word out : List Bool) :
    Runs program (word.length+1) .clearWord (store (header bits indexWord bd) raw reader word [] [] out)
      .clearBound (store (header bits indexWord bd) raw reader [] [] [] out) := by
  induction word with
  | nil =>
    apply one_base program _ _ (.pop (blockStack 4) .clearBound .clearWord .clearWord) _ _ rfl
    · rfl
    · exact update_word _ _ _ _ _ _ _ _
  | cons bit word ih =>
    have h : Runs program 1 .clearWord (store (header bits indexWord bd) raw reader (bit::word) [] [] out)
        .clearWord (store (header bits indexWord bd) raw reader word [] [] out) := by
      apply one_base program _ _ (.pop (blockStack 4) .clearBound .clearWord .clearWord) _ _ rfl
      · cases bit <;> rfl
      · exact update_word _ _ _ _ _ _ _ _
    simpa only [List.length_cons,Nat.add_comm,Nat.add_left_comm,Nat.add_assoc] using h.trans ih
/-- Every residual bound bit is actually popped, preserving all other metadata. -/
theorem clear_bound (bits indexWord bd raw reader out : List Bool) :
    Runs program (bd.length+1) .clearBound (store (header bits indexWord bd) raw reader [] [] [] out)
      .done (store (header bits indexWord []) raw reader [] [] [] out) := by
  induction bd with
  | nil =>
    apply one_base program _ _ (.pop bound .done .clearBound .clearBound) _ _ rfl
    · rfl
    · exact update_bound _ _ _ _ _ _ _ _ _ _
  | cons bit bd ih =>
    have h : Runs program 1 .clearBound (store (header bits indexWord (bit::bd)) raw reader [] [] [] out)
        .clearBound (store (header bits indexWord bd) raw reader [] [] [] out) := by
      apply one_base program _ _ (.pop bound .done .clearBound .clearBound) _ _ rfl
      · cases bit <;> rfl
      · exact update_bound _ _ _ _ _ _ _ _ _ _
    simpa only [List.length_cons,Nat.add_comm,Nat.add_left_comm,Nat.add_assoc] using h.trans ih
/-- One actual verdict push plus complete word/bound draining. -/
theorem write_finish (bits indexWord bd raw reader word : List Bool) (verdict : Bool) :
    Runs program (word.length+bd.length+3) (.write verdict)
      (store (header bits indexWord bd) raw reader word [] [] []) .done
      (store (header bits indexWord []) raw reader [] [] [] [verdict]) := by
  have h : Runs program 1 (.write verdict) (store (header bits indexWord bd) raw reader word [] [] [])
      .clearWord (store (header bits indexWord bd) raw reader word [] [] [verdict]) := by
    apply one_base program _ _ (.push output verdict .clearWord) _ _ rfl
    · rfl
    · exact update_output _ _ _ _ _ _ _ _
  have hh:=h.trans ((clear_word bits indexWord bd raw reader word [verdict]).trans
    (clear_bound bits indexWord bd raw reader [verdict]))
  simpa only [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using hh
/-- The source's computed comparison singleton is ACTUALLY consumed by a pop. -/
theorem read_comparison (pc empty : Label) (next : Bool→Label)
    (hcode : program pc=.base (.pop comparison empty (next false) (next true)))
    (h : H.Stack→List Bool) (raw reader word : List Bool) (bit : Bool) :
    Runs program 1 pc (store h raw reader word [] [bit] []) (next bit) (store h raw reader word [] [] []) := by
  apply one_base program _ _ (.pop comparison empty (next false) (next true)) _ _ hcode
  · cases bit <;> rfl
  · exact update_comparison _ _ _ _ _ _ _ _
/-- Actual flag peek includes EOF→false and preserves the complete raw suffix. -/
theorem flag_peek (test : Bool) (h : H.Stack→List Bool) (raw reader word : List Bool) :
    Runs program 1 (.flag test) (store h raw reader word [] [] [])
      (.write ((!test)==reader.head?.getD false)) (store h raw reader word [] [] []) := by
  apply one_base program _ _ (.peek (blockStack 0) (.write ((!test)==false))
    (.write ((!test)==false)) (.write ((!test)==true))) _ _ rfl
  · cases reader with
    | nil => rfl
    | cons bit reader => cases bit <;> rfl
  · rfl
/-- Physical index emptiness is tested by ONE real cell peek, not a native length test. -/
theorem index_peek (bits indexWord raw reader word : List Bool) :
    Runs program 1 .indexCase (store (header bits indexWord []) raw reader word [] [] [])
      (if indexWord.isEmpty then .firstCopy else .nonzero)
      (store (header bits indexWord []) raw reader word [] [] []) := by
  apply one_base program _ _ (.peek index .firstCopy .nonzero .nonzero) _ _ rfl
  · cases indexWord with
    | nil => rfl
    | cons bit indexWord => cases bit <;> rfl
  · rfl
/-- The ACTUALLY acquired bound's low cell licenses the active/inactive branch. -/
theorem activity_peek (bits indexWord raw reader word : List Bool) :
    Runs program 1 .activity (store (header bits indexWord (M.actualBound bits indexWord)) raw reader word [] [] [])
      (if 0<SemiprimeD1StackInputWidthExecution.width (SemiprimeD1StackPublicInputWidthExecution.cache bits indexWord)
        then .guardCopy else .zero)
      (store (header bits indexWord (M.actualBound bits indexWord)) raw reader word [] [] []) := by
  apply one_base program _ _ (.peek bound .zero .guardCopy .zero) _ _ rfl
  · have hh:=SemiprimeD1StackInputWidthBounds.bound_head
      (SemiprimeD1StackPublicInputWidthExecution.cache bits indexWord)
    change (M.actualBound bits indexWord).head?=_ at hh
    change some (SemiprimeD1StackBytecode.choose (L:=Label) .zero .guardCopy .zero
      ((M.actualBound bits indexWord).head?))=_
    rw [hh]
    by_cases hw:SemiprimeD1StackInputWidthExecution.width
        (SemiprimeD1StackPublicInputWidthExecution.cache bits indexWord)=0
    · simp [hw,SemiprimeD1StackBytecode.choose]
    · have hp : 0<SemiprimeD1StackInputWidthExecution.width
          (SemiprimeD1StackPublicInputWidthExecution.cache bits indexWord) := by omega
      simp [hw,hp,SemiprimeD1StackBytecode.choose]
  · rfl
/-- Both literal bits of the first-index constant TWO are physically pushed. -/
theorem push_two (bits indexWord raw reader word : List Bool) :
    Runs program 2 .twoHigh (store (header bits indexWord []) raw reader word word [] [])
      .firstCheck (store (header bits indexWord [false,true]) raw reader word word [] []) := by
  have h0 : Runs program 1 .twoHigh (store (header bits indexWord []) raw reader word word [] [])
      .twoLow (store (header bits indexWord [true]) raw reader word word [] []) := by
    apply one_base program _ _ (.push bound true .twoLow) _ _ rfl
    · rfl
    · exact update_bound _ _ _ _ _ _ _ _ _ _
  have h1 : Runs program 1 .twoLow (store (header bits indexWord [true]) raw reader word word [] [])
      .firstCheck (store (header bits indexWord [false,true]) raw reader word word [] []) := by
    apply one_base program _ _ (.push bound false .firstCheck) _ _ rfl
    · rfl
    · exact update_bound _ _ _ _ _ _ _ _ _ _
  exact h0.trans h1
end RiemannGaussian.SemiprimeD1StackPublicInputControl
