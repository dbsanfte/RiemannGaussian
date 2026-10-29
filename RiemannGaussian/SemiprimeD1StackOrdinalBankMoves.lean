/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackOrdinalBankCalls
/-! # Physical width allocation, wrapped-word restoration and final materialization -/
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 32768
namespace RiemannGaussian.SemiprimeD1StackOrdinalBankMoves
open SemiprimeD1StackOrdinalBank SemiprimeD1StackOrdinalBankCalls
open SemiprimeD1StackProcedureFragments (Runs one_base)
namespace B
export SemiprimeD1StackBytecode (execute choose)
end B

/-- Physically consume the copied tally to allocate each zero counter bit. -/
theorem zero_run (todo word tally : List Bool) :
    Runs program (2*todo.length+1) (.inl .makeZero) (data word [] [] [] [] tally [] todo [])
      (.inl .copyRemaining) (data (List.replicate todo.length false++word) [] [] [] [] tally [] [] []) := by
  induction todo generalizing word with
  | nil =>
    apply one_base program _ _ (.pop zeroRemaining (.inl .copyRemaining) (.inl .pushZero) (.inl .pushZero)) _ _ rfl
    · rfl
    · funext k; rcases k with k|k <;> cases k <;> simp [B.execute,data,SemiprimeD1StackAssignmentLoop.data,zeroRemaining]
  | cons bit todo ih =>
    have h0 : Runs program 1 (.inl .makeZero) (data word [] [] [] [] tally [] (bit::todo) [])
        (.inl .pushZero) (data word [] [] [] [] tally [] todo []) := by
      apply one_base program _ _ (.pop zeroRemaining (.inl .copyRemaining) (.inl .pushZero) (.inl .pushZero)) _ _ rfl
      · cases bit <;> rfl
      · cases bit <;> funext k <;> rcases k with k|k <;> cases k <;> rfl
    have h1 : Runs program 1 (.inl .pushZero) (data word [] [] [] [] tally [] todo [])
        (.inl .makeZero) (data (false::word) [] [] [] [] tally [] todo []) := by
      apply one_base program _ _ (.push counter false (.inl .makeZero)) _ _ rfl
      · rfl
      · funext k; rcases k with k|k <;> cases k <;> simp [B.execute,data,SemiprimeD1StackAssignmentLoop.data,counter]
    have h:=h0.trans (h1.trans (ih (false::word)))
    simpa only [List.length_cons,List.replicate_succ',List.append_assoc,List.singleton_append,
      show 1+(1+(2*todo.length+1))=2*(todo.length+1)+1 by omega] using h

/-- Physical first pass reverses the actual wrapped output into scratch. -/
theorem move_drain (xs scratch history output tally todo : List Bool) :
    Runs program (2*xs.length+1) (.inl .moveDrain) (data [] scratch xs history output tally todo [] [])
      (.inl .restore) (data [] (xs.reverse++scratch) [] history output tally todo [] []) := by
  induction xs generalizing scratch with
  | nil =>
    apply one_base program _ _ (.pop (.inl .next) (.inl .restore) (.inl (.movePush false)) (.inl (.movePush true))) _ _ rfl
    · rfl
    · funext k; rcases k with k|k <;> cases k <;> simp [B.execute,data,SemiprimeD1StackAssignmentLoop.data]
  | cons bit xs ih =>
    have h0 : Runs program 1 (.inl .moveDrain) (data [] scratch (bit::xs) history output tally todo [] [])
        (.inl (.movePush bit)) (data [] scratch xs history output tally todo [] []) := by
      apply one_base program _ _ (.pop (.inl .next) (.inl .restore) (.inl (.movePush false)) (.inl (.movePush true))) _ _ rfl
      · cases bit <;> rfl
      · cases bit <;> funext k <;> rcases k with k|k <;> cases k <;>
          simp [B.execute,data,SemiprimeD1StackAssignmentLoop.data]
    have h1 : Runs program 1 (.inl (.movePush bit)) (data [] scratch xs history output tally todo [] [])
        (.inl .moveDrain) (data [] (bit::scratch) xs history output tally todo [] []) := by
      apply one_base program _ _ (.push (.inl .scratch) bit (.inl .moveDrain)) _ _ rfl
      · rfl
      · funext k; rcases k with k|k <;> cases k <;> simp [B.execute,data,SemiprimeD1StackAssignmentLoop.data]
    have h:=h0.trans (h1.trans (ih (bit::scratch)))
    simpa only [List.length_cons,List.reverse_cons,List.append_assoc,List.singleton_append,
      show 1+(1+(2*xs.length+1))=2*(xs.length+1)+1 by omega] using h

/-- Physical second pass restores little-endian order, without a word getter. -/
theorem restore_run (xs word history output tally todo : List Bool) :
    Runs program (2*xs.length+1) (.inl .restore) (data word xs [] history output tally todo [] [])
      (.inl .loop) (data (xs.reverse++word) [] [] history output tally todo [] []) := by
  induction xs generalizing word with
  | nil =>
    apply one_base program _ _ (.pop (.inl .scratch) (.inl .loop) (.inl (.restorePush false)) (.inl (.restorePush true))) _ _ rfl
    · rfl
    · funext k; rcases k with k|k <;> cases k <;> simp [B.execute,data,SemiprimeD1StackAssignmentLoop.data]
  | cons bit xs ih =>
    have h0 : Runs program 1 (.inl .restore) (data word (bit::xs) [] history output tally todo [] [])
        (.inl (.restorePush bit)) (data word xs [] history output tally todo [] []) := by
      apply one_base program _ _ (.pop (.inl .scratch) (.inl .loop) (.inl (.restorePush false)) (.inl (.restorePush true))) _ _ rfl
      · cases bit <;> rfl
      · cases bit <;> funext k <;> rcases k with k|k <;> cases k <;>
          simp [B.execute,data,SemiprimeD1StackAssignmentLoop.data]
    have h1 : Runs program 1 (.inl (.restorePush bit)) (data word xs [] history output tally todo [] [])
        (.inl .restore) (data (bit::word) xs [] history output tally todo [] []) := by
      apply one_base program _ _ (.push counter bit (.inl .restore)) _ _ rfl
      · rfl
      · funext k; rcases k with k|k <;> cases k <;> simp [B.execute,data,SemiprimeD1StackAssignmentLoop.data,counter]
    have h:=h0.trans (h1.trans (ih (bit::word)))
    simpa only [List.length_cons,List.reverse_cons,List.append_assoc,List.singleton_append,
      show 1+(1+(2*xs.length+1))=2*(xs.length+1)+1 by omega] using h

/-- The actual physical overflow bit is consumed; the marker loop, not overflow,
determines round count. Actual ordinal words are proved nonoverflowing separately. -/
theorem continue_run (bit : Bool) (xs history output tally todo : List Bool) :
    Runs program (4*xs.length+3) (.inl .popOverflow) (data [] [] (bit::xs) history output tally todo [] [])
      (.inl .loop) (data xs [] [] history output tally todo [] []) := by
  have h0 : Runs program 1 (.inl .popOverflow) (data [] [] (bit::xs) history output tally todo [] [])
      (.inl .moveDrain) (data [] [] xs history output tally todo [] []) := by
    apply one_base program _ _ (.pop (.inl .next) (.inl .abort) (.inl .moveDrain) (.inl .moveDrain)) _ _ rfl
    · cases bit <;> rfl
    · cases bit <;> funext k <;> rcases k with k|k <;> cases k <;>
        simp [B.execute,data,SemiprimeD1StackAssignmentLoop.data]
  have h1:=move_drain xs [] history output tally todo
  simp only [List.append_nil] at h1
  have h2:=restore_run xs.reverse [] history output tally todo
  have h:=h0.trans (h1.trans h2)
  simpa only [List.append_nil,List.length_reverse,List.reverse_reverse,
    show 1+((2*xs.length+1)+(2*xs.length+1))=4*xs.length+3 by omega] using h

/-- Final counter bytes are really cleared; no leftover answer/work is projected away. -/
theorem clear_counter (word history output tally : List Bool) :
    Runs program (word.length+1) (.inl .clearCounter) (data word [] [] history output tally [] [] [])
      (.inl .seedOutput) (data [] [] [] history output tally [] [] []) := by
  induction word with
  | nil =>
    apply one_base program _ _ (.pop counter (.inl .seedOutput) (.inl .clearCounter) (.inl .clearCounter)) _ _ rfl
    · rfl
    · funext k; rcases k with k|k <;> cases k <;> simp [B.execute,data,SemiprimeD1StackAssignmentLoop.data,counter]
  | cons bit word ih =>
    have h0 : Runs program 1 (.inl .clearCounter) (data (bit::word) [] [] history output tally [] [] [])
        (.inl .clearCounter) (data word [] [] history output tally [] [] []) := by
      apply one_base program _ _ (.pop counter (.inl .seedOutput) (.inl .clearCounter) (.inl .clearCounter)) _ _ rfl
      · cases bit <;> rfl
      · cases bit <;> funext k <;> rcases k with k|k <;> cases k <;>
          simp [B.execute,data,SemiprimeD1StackAssignmentLoop.data,counter]
    simpa only [List.length_cons,show 1+(word.length+1)=word.length+1+1 by omega] using h0.trans ih

/-- Real nil seeding and one final reversal materialize the original ID order. -/
theorem finish_run (word history output tally : List Bool) :
    Runs program (word.length+2*history.length+5) (.inl .clearCounter)
      (data word [] [] history output tally [] [] []) (.inl .done)
      (data [] [] [] [] (history.reverse++false::output) tally [] [] []) := by
  have h0:=clear_counter word history output tally
  have h1 : Runs program 1 (.inl .seedOutput) (data [] [] [] history output tally [] [] [])
      (.inl .reverse) (data [] [] [] history (false::output) tally [] [] []) := by
    apply one_base program _ _ (.push ids false (.inl .reverse)) _ _ rfl
    · rfl
    · funext k; rcases k with k|k <;> cases k <;> simp [B.execute,data,SemiprimeD1StackAssignmentLoop.data,ids]
  have h2:=reverse_call history (false::output) tally
  have h:=h0.trans (h1.trans h2)
  simpa only [show (word.length+1)+(1+(2*history.length+3))=word.length+2*history.length+5 by omega] using h

end RiemannGaussian.SemiprimeD1StackOrdinalBankMoves
