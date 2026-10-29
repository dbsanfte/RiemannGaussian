/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackWordEqual
import RiemannGaussian.SemiprimeD1StackCopy
import RiemannGaussian.SemiprimeMacroEntryBitPrimitives

/-! # Closed binary-value equality with padding and physical mismatch cleanup
The code reads actual digits and produces its answer through finite Boolean
branches. Decoded values below occur only in the proved output specification.
-/
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option Elab.async false
namespace RiemannGaussian.SemiprimeD1StackWordEqualExecution
open SemiprimeD1StackWordEqual SemiprimeD1StackBytecode SemiprimeBitArithmetic
open SemiprimeD1StackAdder (Stack store store_left store_right store_output)

/-- Literal left operand projection. -/
@[simp] theorem store_get_left (a b c d : List Bool) : store a b c d Stack.left=a := rfl
/-- Literal right operand projection. -/
@[simp] theorem store_get_right (a b c d : List Bool) : store a b c d Stack.right=b := rfl
/-- Literal comparison output projection. -/
@[simp] theorem store_get_output (a b c d : List Bool) : store a b c d Stack.output=d := rfl

/-- Two literal bytecode transitions, preserving actual intermediate payload. -/
theorem two_steps {a b c : State Stack Label}
    (h0 : step code a=some b) (h1 : step code b=some c) : run code 2 a=some c := by
  change (step code a).bind (step code)=some c
  rw [h0,Option.bind_some,h1]
/-- Chronological composition of this SAME fixed program. -/
theorem run_append (m n : ℕ) (a b c : State Stack Label)
    (h0 : run code m a=some b) (h1 : run code n b=some c) : run code (m+n) a=some c := by
  rw [SemiprimeD1StackCopy.run_add,h0,Option.bind_some,h1]

/-- Empty right mismatch tail enters done and physically halts. -/
theorem clear_right_run (right : List Bool) (flag : Option Bool) :
    run code (right.length+2) (state (some .clearRight) flag [] right [false])=
      some (state none none [] [] [false]) := by
  induction right generalizing flag with
  | nil =>
    apply two_steps (b:=state (some .done) none [] [] [false])
    · simp [step,execute,state,code,choose,store_right]
    · rfl
  | cons bit right ih =>
    have h0 : run code 1 (state (some .clearRight) flag [] (bit::right) [false])=
        some (state (some .clearRight) (some bit) [] right [false]) := by
      cases bit <;> simp [run,step,execute,state,code,choose,store_right]
    have h:=run_append 1 (right.length+2) _ _ _ h0 (ih (some bit))
    simpa only [List.length_cons,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using h

/-- Both remaining mismatch tails are physically erased before halt. -/
theorem clear_left_run (left right : List Bool) (flag : Option Bool) :
    run code (left.length+right.length+3) (state (some .clearLeft) flag left right [false])=
      some (state none none [] [] [false]) := by
  induction left generalizing flag with
  | nil =>
    have h0 : run code 1 (state (some .clearLeft) flag [] right [false])=
        some (state (some .clearRight) none [] right [false]) := by
      simp [run,step,execute,state,code,choose,store_left]
    have h:=run_append 1 (right.length+2) _ _ _ h0 (clear_right_run right none)
    simpa only [List.length_nil,Nat.zero_add,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using h
  | cons bit left ih =>
    have h0 : run code 1 (state (some .clearLeft) flag (bit::left) right [false])=
        some (state (some .clearLeft) (some bit) left right [false]) := by
      cases bit <;> simp [run,step,execute,state,code,choose,store_left]
    have h:=run_append 1 (left.length+right.length+3) _ _ _ h0 (ih (some bit))
    simpa only [List.length_cons,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using h

/-- A mismatch physically pushes false and cleans BOTH operand suffixes. -/
theorem reject_run (left right : List Bool) (flag : Option Bool) :
    run code (left.length+right.length+4) (state (some .reject) flag left right [])=
      some (state none none [] [] [false]) := by
  have h0 : run code 1 (state (some .reject) flag left right [])=
      some (state (some .clearLeft) flag left right [false]) := by
    simp [run,step,execute,state,code,store_output]
  have h:=run_append 1 (left.length+right.length+3) _ _ _ h0 (clear_left_run left right flag)
  simpa only [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using h

/-- An accepted comparison physically writes true and then really halts. -/
theorem accept_run (flag : Option Bool) :
    run code 2 (state (some .accept) flag [] [] [])=some (state none none [] [] [true]) := by
  apply two_steps (b:=state (some .done) flag [] [] [true])
  · simp [step,execute,state,code,store_output]
  · rfl

/-- Proof-side exact elapsed length of the physically scanned high-zero tail. -/
def emptyTime : List Bool→ℕ
  | [] => 3
  | false::ys => 1+emptyTime ys
  | true::ys => ys.length+5

/-- EOF on the left compares all right padding against literal zero. -/
theorem right_empty_run (right : List Bool) (flag : Option Bool) :
    run code (emptyTime right) (state (some .rightEmpty) flag [] right [])=
      some (state none none [] [] [decide (0=bitValue right)]) := by
  induction right generalizing flag with
  | nil =>
    have h0 : run code 1 (state (some .rightEmpty) flag [] [] [])=
        some (state (some .accept) none [] [] []) := by
      simp [run,step,execute,state,code,choose,store_right]
    exact run_append 1 2 _ _ _ h0 (accept_run none)
  | cons bit right ih =>
    cases bit with
    | false =>
      have h0 : run code 1 (state (some .rightEmpty) flag [] (false::right) [])=
          some (state (some .rightEmpty) (some false) [] right []) := by
        simp [run,step,execute,state,code,choose,store_right]
      have h:=run_append 1 (emptyTime right) _ _ _ h0 (ih (some false))
      simpa [emptyTime,bitValue,bitNat,eq_comm] using h
    | true =>
      have h0 : run code 1 (state (some .rightEmpty) flag [] (true::right) [])=
          some (state (some .reject) (some true) [] right []) := by
        simp [run,step,execute,state,code,choose,store_right]
      have hr:=reject_run [] right (some true)
      simp only [List.length_nil,Nat.zero_add] at hr
      have h:=run_append 1 (right.length+4) _ _ _ h0 hr
      have hz : ¬(0=1+2*bitValue right) := by omega
      simpa [emptyTime,bitValue,bitNat,hz,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using h

/-- Every high-zero-tail visit is counted in physical word length. -/
theorem emptyTime_le (right : List Bool) : emptyTime right ≤ right.length+4 := by
  induction right with
  | nil => decide
  | cons bit right ih => cases bit <;> simp only [emptyTime,List.length_cons] <;> omega

/-- Two actual reads compare real low bits, retaining only a finite dispatch label. -/
theorem pair_run (left right : List Bool) (x y : Bool) (flag : Option Bool) :
    run code 2 (state (some .loop) flag (x::left) (y::right) [])=
      some (state (some (if x=y then .loop else .reject)) (some y) left right []) := by
  apply two_steps (b:=state (some (if x then .rightTrue else .rightFalse)) (some x) left (y::right) [])
  · cases x <;> simp [step,execute,state,code,choose,store_left]
  · cases x <;> cases y <;> simp [step,execute,state,code,choose,store_right]

/-- A right EOF is a literal zero digit while the left bit is still physically consumed. -/
theorem right_eof_run (left : List Bool) (x : Bool) (flag : Option Bool) :
    run code 2 (state (some .loop) flag (x::left) [] [])=
      some (state (some (if x then .reject else .loop)) none left [] []) := by
  apply two_steps (b:=state (some (if x then .rightTrue else .rightFalse)) (some x) left [] [])
  · cases x <;> simp [step,execute,state,code,choose,store_left]
  · cases x <;> simp [step,execute,state,code,choose,store_right]

/-- Numeric low-bit equality retains BOTH the digit and tail information. -/
theorem cons_value_iff (x y : Bool) (left right : List Bool) :
    bitValue (x::left)=bitValue (y::right) ↔ x=y ∧ bitValue left=bitValue right := by
  cases x <;> cases y <;> simp [bitValue,bitNat] <;> omega

/-- Exact actual instruction count; all decoded-value decisions remain solely
in the output theorem, while this count follows the literal digit branches. -/
def executionTime : List Bool→List Bool→ℕ
  | [],ys => 1+emptyTime ys
  | false::xs,[] => 2+executionTime xs []
  | true::xs,[] => 2+(xs.length+4)
  | x::xs,y::ys => if x=y then 2+executionTime xs ys else 2+(xs.length+ys.length+4)

/-- Complete actual comparison, including unequal zero padding and all cleanup. -/
theorem source_run (left right : List Bool) (flag : Option Bool) :
    run code (executionTime left right) (state (some .loop) flag left right [])=
      some (state none none [] [] [decide (bitValue left=bitValue right)]) := by
  induction left generalizing right flag with
  | nil =>
    have h0 : run code 1 (state (some .loop) flag [] right [])=
        some (state (some .rightEmpty) none [] right []) := by
      simp [run,step,execute,state,code,choose,store_left]
    exact run_append 1 (emptyTime right) _ _ _ h0 (right_empty_run right none)
  | cons x left ih =>
    cases right with
    | nil =>
      cases x with
      | false =>
        have h:=run_append 2 (executionTime left []) _ _ _ (right_eof_run left false flag) (ih [] none)
        have hv : decide (bitValue (false::left)=bitValue [])=decide (bitValue left=bitValue []) := by
          simp [bitValue,bitNat]
          rfl
        change run code (2+executionTime left []) (state (some .loop) flag (false::left) [] [])=
          some (state none none [] [] [decide (bitValue (false::left)=bitValue [])])
        rw [hv]
        exact h
      | true =>
        have h:=run_append 2 (left.length+4) _ _ _ (right_eof_run left true flag) (reject_run left [] none)
        simpa [executionTime,bitValue,bitNat] using h
    | cons y right =>
      by_cases hxy : x=y
      · have h0:=pair_run left right x y flag
        simp only [hxy,ite_true] at h0
        have h:=run_append 2 (executionTime left right) _ _ _ h0 (ih right (some y))
        simpa only [executionTime,hxy,ite_true,cons_value_iff,true_and] using h
      · have h0:=pair_run left right x y flag
        simp only [hxy,ite_false] at h0
        have h:=run_append 2 (left.length+right.length+4) _ _ _ h0 (reject_run left right (some y))
        simpa only [executionTime,hxy,ite_false,cons_value_iff,false_and,decide_false] using h

/-- Uniform linear time in actual operand lengths, without a supplied equality answer. -/
theorem executionTime_le (left right : List Bool) :
    executionTime left right ≤ 2*(left.length+right.length)+8 := by
  induction left generalizing right with
  | nil =>
    have h:=emptyTime_le right
    simp only [executionTime,List.length_nil,Nat.zero_add]
    omega
  | cons x left ih =>
    cases right with
    | nil =>
      cases x <;> simp only [executionTime,List.length_cons,List.length_nil,Nat.add_zero]
      · have h:=ih [];simp only [List.length_nil,Nat.add_zero] at h;omega
      · omega
    | cons y right =>
      have h:=ih right
      simp only [executionTime,List.length_cons]
      split <;> omega

end RiemannGaussian.SemiprimeD1StackWordEqualExecution
