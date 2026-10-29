/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackCopy
import RiemannGaussian.SemiprimeD1StackAdder
import RiemannGaussian.SemiprimeD1StackBytecodeBounds

/-! # Actual equality of bounded unary jet-index metadata
Both physical counter words are consumed. Their bit VALUES are irrelevant;
coefficient payloads do not pass through this metadata-only procedure.
-/
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace RiemannGaussian.SemiprimeD1StackJetIndexEq
open SemiprimeD1StackBytecode
open SemiprimeD1StackAdder (Stack store store_left store_right store_output)

/-- Fixed finite equality/clearing control, independent of both index values. -/
inductive Label where
  | loop | rightEmpty | rightFull | clearLeft | clearRight | accept | reject | done
  deriving DecidableEq,Repr

/-- Actual constant label enumeration. -/
instance : Fintype Label := Fintype.ofList [.loop,.rightEmpty,.rightFull,.clearLeft,.clearRight,.accept,.reject,.done]
  (by intro k; cases k <;> simp)

/-- Actual paired-pop comparison with full mismatch cleanup. -/
def code : Label → Instruction Stack Label
  | .loop => .pop .left .rightEmpty .rightFull .rightFull
  | .rightEmpty => .pop .right .accept .clearRight .clearRight
  | .rightFull => .pop .right .clearLeft .loop .loop
  | .clearLeft => .pop .left .reject .clearLeft .clearLeft
  | .clearRight => .pop .right .reject .clearRight .clearRight
  | .accept => .push .output true .done
  | .reject => .push .output false .done
  | .done => .halt

/-- Literal counter/work/result state; the output starts empty in the public entry. -/
def state (pc : Option Label) (flag : Option Bool) (left right output : List Bool) : State Stack Label :=
  ⟨pc,flag,store left right [] output⟩

@[simp] theorem store_get_left (a b c d : List Bool) : store a b c d Stack.left = a := rfl
@[simp] theorem store_get_right (a b c d : List Bool) : store a b c d Stack.right = b := rfl
@[simp] theorem store_get_output (a b c d : List Bool) : store a b c d Stack.output = d := rfl

/-- Actual compiled fixed machine for unary metadata comparison. -/
def machine : Turing.FinTM2 := SemiprimeD1StackBytecode.machine Stack.left Stack.output Label.loop code

/-- Two literal source transitions. -/
theorem two_steps (a b c : State Stack Label)
    (h₁ : step code a=some b) (h₂ : step code b=some c) : run code 2 a=some c := by
  change (step code a).bind (step code)=some c
  rw [h₁,Option.bind_some,h₂]

/-- Actual finite source-run composition. -/
theorem run_append (m n : ℕ) (a b c : State Stack Label)
    (hm : run code m a=some b) (hn : run code n b=some c) : run code (m+n) a=some c := by
  rw [SemiprimeD1StackCopy.run_add,hm,Option.bind_some,hn]

/-- The accepted/rejected flag is physically pushed, then the machine really halts. -/
theorem finish_run (accepted : Bool) (flag : Option Bool) :
    run code 2 (state (some (if accepted then .accept else .reject)) flag [] [] [])=
    some (state none none [] [] [accepted]) := by
  apply two_steps (b:=state (some .done) flag [] [] [accepted])
  · cases accepted <;> simp [step,execute,state,code,store_output]
  · rfl

/-- Full left-mismatch cleanup, including real reject-bit emission and halt. -/
theorem clear_left_run (left : List Bool) (flag : Option Bool) :
    run code (left.length+3) (state (some .clearLeft) flag left [] [])=
    some (state none none [] [] [false]) := by
  induction left generalizing flag with
  | nil =>
    have h1 : run code 1 (state (some .clearLeft) flag [] [] [])=some (state (some .reject) none [] [] []) := by
      simp [run,step,execute,state,code,choose,store_left]
    exact run_append 1 2 _ _ _ h1 (finish_run false none)
  | cons bit left ih =>
    have h1 : run code 1 (state (some .clearLeft) flag (bit::left) [] [])=
        some (state (some .clearLeft) (some bit) left [] []) := by
      cases bit <;> simp [run,step,execute,state,code,choose,store_left]
    have hh:=run_append 1 (left.length+3) _ _ _ h1 (ih (some bit))
    simpa only [List.length_cons,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using hh

/-- Full right-mismatch cleanup, including every remaining counter cell. -/
theorem clear_right_run (right : List Bool) (flag : Option Bool) :
    run code (right.length+3) (state (some .clearRight) flag [] right [])=
    some (state none none [] [] [false]) := by
  induction right generalizing flag with
  | nil =>
    have h1 : run code 1 (state (some .clearRight) flag [] [] [])=some (state (some .reject) none [] [] []) := by
      simp [run,step,execute,state,code,choose,store_right]
    exact run_append 1 2 _ _ _ h1 (finish_run false none)
  | cons bit right ih =>
    have h1 : run code 1 (state (some .clearRight) flag [] (bit::right) [])=
        some (state (some .clearRight) (some bit) [] right []) := by
      cases bit <;> simp [run,step,execute,state,code,choose,store_right]
    have hh:=run_append 1 (right.length+3) _ _ _ h1 (ih (some bit))
    simpa only [List.length_cons,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using hh

/-- Actual paired-read step consumes one metadata cell on each side. -/
theorem pair_run (left right : List Bool) (x y : Bool) (flag : Option Bool) :
    run code 2 (state (some .loop) flag (x::left) (y::right) [])=
    some (state (some .loop) (some y) left right []) := by
  apply two_steps (b:=state (some .rightFull) (some x) left (y::right) [])
  · cases x <;> simp [step,execute,state,code,choose,store_left]
  · cases y <;> simp [step,execute,state,code,choose,store_right]

/-- Exact fixed-program equality, ALL input counter cells consumed, no equality answer supplied. -/
theorem source_run (left right : List Bool) (flag : Option Bool) :
    run code (left.length+right.length+4) (state (some .loop) flag left right [])=
    some (state none none [] [] [decide (left.length=right.length)]) := by
  induction left generalizing right flag with
  | nil =>
    cases right with
    | nil =>
      have h1 : run code 2 (state (some .loop) flag [] [] [])=some (state (some .accept) none [] [] []) := by
        apply two_steps (b:=state (some .rightEmpty) none [] [] [])
        · simp [step,execute,state,code,choose,store_left]
        · simp [step,execute,state,code,choose,store_right]
      exact run_append 2 2 _ _ _ h1 (finish_run true none)
    | cons y right =>
      have h1 : run code 2 (state (some .loop) flag [] (y::right) [])=
          some (state (some .clearRight) (some y) [] right []) := by
        apply two_steps (b:=state (some .rightEmpty) none [] (y::right) [])
        · simp [step,execute,state,code,choose,store_left]
        · cases y <;> simp [step,execute,state,code,choose,store_right]
      have hh:=run_append 2 (right.length+3) _ _ _ h1 (clear_right_run right (some y))
      rw [show 2+(right.length+3)=([] : List Bool).length+(y::right).length+4 by simp; omega] at hh
      simpa using hh
  | cons x left ih =>
    cases right with
    | nil =>
      have h1 : run code 2 (state (some .loop) flag (x::left) [] [])=
          some (state (some .clearLeft) none left [] []) := by
        apply two_steps (b:=state (some .rightFull) (some x) left [] [])
        · cases x <;> simp [step,execute,state,code,choose,store_left]
        · simp [step,execute,state,code,choose,store_right]
      have hh:=run_append 2 (left.length+3) _ _ _ h1 (clear_left_run left none)
      rw [show 2+(left.length+3)=(x::left).length+([] : List Bool).length+4 by simp; omega] at hh
      simpa only [List.length_nil,List.length_cons,Nat.add_one_ne_zero,decide_false] using hh
    | cons y right =>
      have h1:=pair_run left right x y flag
      have h2:=ih right (some y)
      have hh:=run_append 2 (left.length+right.length+4) _ _ _ h1 h2
      rw [show 2+(left.length+right.length+4)=(x::left).length+(y::right).length+4 by simp; omega] at hh
      simpa only [List.length_cons,Nat.add_right_cancel_iff] using hh

/-- Genuine actual finite-machine equality certificate at an exact linear time. -/
def sourceEqual (left right : List Bool) :
    StateTransition.EvalsToInTime (step code) (state (some .loop) none left right [])
      (some (state none none [] [] [decide (left.length=right.length)])) (left.length+right.length+4) :=
  ⟨⟨_,source_run left right none⟩,le_refl _⟩

/-- Actual compiled finite-stack execution; these operands represent metadata, never coefficients. -/
def machineEqual (left right : List Bool) :
    StateTransition.EvalsToInTime machine.step
      (SemiprimeD1StackBytecode.configuration (state (some .loop) none left right []))
      (some (SemiprimeD1StackBytecode.configuration (state none none [] [] [decide (left.length=right.length)])))
      (left.length+right.length+4) :=
  SemiprimeD1StackBytecode.evalsCorrect Stack.left Stack.output Label.loop code _ _ _ (sourceEqual left right)

/-- Every successful executed prefix stays within a linear physical cell bound. -/
theorem prefix_cells (left right : List Bool) (fuel : ℕ) (out : State Stack Label)
    (h : run code fuel (state (some .loop) none left right [])=some out) :
    SemiprimeD1StackBytecodeBounds.cells out ≤ 5*(left.length+right.length)+16 := by
  have ht := SemiprimeD1StackBytecodeBounds.fuel_le_halt code
    (state (some .loop) none left right [])
    (state none none [] [] [decide (left.length=right.length)]) out
    (left.length+right.length+4) fuel (source_run left right none) rfl h
  have hc := SemiprimeD1StackBytecodeBounds.run_cells code fuel _ out h
  have hi : SemiprimeD1StackBytecodeBounds.cells (state (some .loop) none left right []) =
      left.length+right.length := by
    have hu : (Finset.univ : Finset Stack) = {.left,.right,.scratch,.output} := by decide
    simp [SemiprimeD1StackBytecodeBounds.cells,hu,state,store]
  have hk : Fintype.card Stack=4 := by decide
  rw [hi,hk] at hc
  omega

end RiemannGaussian.SemiprimeD1StackJetIndexEq
