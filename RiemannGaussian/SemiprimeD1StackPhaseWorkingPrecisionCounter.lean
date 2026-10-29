/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackPhaseWorkingPrecisionPrimitives
/-! # Paid repeated real binary increment from physically copied unary metadata -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 2000000
namespace RiemannGaussian.SemiprimeD1StackPhaseWorkingPrecisionCounter
open SemiprimeD1StackPhaseWorkingPrecision SemiprimeD1StackPhaseWorkingPrecisionArithmetic
open SemiprimeD1StackPhaseWorkingPrecisionPrimitives SemiprimeD1StackProcedureTrace
/-- One actual counter round consumes its own physical remaining marker. -/
theorem pop_todo (second : Bool) (old : M.Stack→List Bool) (l r out word power : List Bool) (n : Nat) :
    Runs program 1 (.loop second) (data old l r out word [] (List.replicate (n+1) true) [] [] power)
      (.increment second) (data old l r out word [] (List.replicate n true) [] [] power) :=by
  apply one_base program (.loop second) (.increment second)
    (.pop (aux .todo) (.finish second) (.increment second) (.increment second)) _ _ rfl
  · rfl
  · funext k;rcases k with k|k
    · rfl
    · cases k <;> rfl
/-- Actual overflow prefix is consumed physically; no overflow/length advice is supplied. -/
theorem pop_overflow (second bit : Bool) (old : M.Stack→List Bool) (l r out word todo power : List Bool) :
    Runs program 1 (.popOverflow second) (data old l r out [] (bit::word) todo [] [] power)
      (.restore second) (data old l r out [] word todo [] [] power) :=by
  apply one_base program (.popOverflow second) (.restore second)
    (.pop (aux .next) (.restore second) (.restore second) (.restore second)) _ _ rfl
  · cases bit <;> rfl
  · funext k;rcases k with k|k
    · rfl
    · cases k <;> rfl
/-- Literal wrapped-output copy restores the physical counter from the actual next word. -/
theorem restore_counter (second : Bool) (old : M.Stack→List Bool) (l r out word todo power : List Bool) :
    Runs program (5*word.length+4) (.restore second) (data old l r out [] word todo [] [] power)
      (.clearNext second) (data old l r out word word todo [] [] power) :=by
  have h:=copy_call 4 (.restore second) (.clearNext second) rfl (data old l r out [] word todo [] [] power) rfl rfl
  have he:Function.update (data old l r out [] word todo [] [] power) (copyTarget 4)
      (data old l r out [] word todo [] [] power (copySource 4))=data old l r out word word todo [] [] power:=by
    funext k;rcases k with k|k
    · rfl
    · cases k <;> rfl
  rw [he] at h
  exact h
/-- Every duplicate wrapped-output cell is physically erased before the next round. -/
theorem clear_next (second : Bool) (old : M.Stack→List Bool) (l r out word todo power : List Bool) :
    Runs program (word.length+1) (.clearNext second) (data old l r out word word todo [] [] power)
      (.loop second) (data old l r out word [] todo [] [] power) :=by
  have h:=SemiprimeD1StackPhysicalLoops.drain program (.clearNext second) (.loop second) (aux .next)
    rfl (data old l r out word word todo [] [] power) word
  have hi:Function.update (data old l r out word word todo [] [] power) (aux .next) word=
      data old l r out word word todo [] [] power:=Function.update_eq_self _ _
  have ho:Function.update (data old l r out word word todo [] [] power) (aux .next) []=
      data old l r out word [] todo [] [] power:=by
    funext k;rcases k with k|k
    · rfl
    · cases k <;> rfl
  rw [hi,ho] at h
  exact h
/-- Complete paid round calls the actual frozen increment bytecode and restores/clears its bank. -/
theorem round_run (second : Bool) (old : M.Stack→List Bool) (l r out word power : List Bool) (n : Nat) :
    ∃q≤20*(word.length+2),Runs program q (.loop second)
      (data old l r out word [] (List.replicate (n+1) true) [] [] power) (.loop second)
      (data old l r out (I.wrapped word) [] (List.replicate n true) [] [] power) :=by
  have h0:=pop_todo second old l r out word power n
  obtain ⟨b,hb,h1⟩:=increment_call second old l r out word (List.replicate n true) power
  have h2:=pop_overflow second (SemiprimeD1StackIncrement.overflow word) old l r out (I.wrapped word) (List.replicate n true) power
  have h3:=restore_counter second old l r out (I.wrapped word) (List.replicate n true) power
  have h4:=clear_next second old l r out (I.wrapped word) (List.replicate n true) power
  have hh:=join (join (join (join h0 h1) h2) h3) h4
  refine ⟨_,?_,hh⟩
  rw [I.wrapped_length]
  omega
/-- Exactly n actual physical remaining markers execute n real binary increment rounds. -/
theorem loop_run (second : Bool) (old : M.Stack→List Bool) (l r out word power : List Bool) (n : Nat) :
    ∃q≤30*(n+1)*(word.length+2),Runs program q (.loop second)
      (data old l r out word [] (List.replicate n true) [] [] power) (.finish second)
      (data old l r out ((I.wrapped^[n]) word) [] [] [] [] power) :=by
  induction n generalizing word with
  | zero=>
    refine ⟨1,by omega,?_⟩
    apply one_base program (.loop second) (.finish second)
      (.pop (aux .todo) (.finish second) (.increment second) (.increment second)) _ _ rfl
    · rfl
    · funext k;rcases k with k|k
      · rfl
      · cases k <;> rfl
  | succ n ih=>
    obtain ⟨b,hb,h0⟩:=round_run second old l r out word power n
    obtain ⟨c,hc,h1⟩:=ih (I.wrapped word)
    have hh:=join h0 h1
    refine ⟨b+c,?_,?_⟩
    · rw [I.wrapped_length] at hc
      nlinarith
    · simpa only [Function.iterate_succ_apply] using hh
end RiemannGaussian.SemiprimeD1StackPhaseWorkingPrecisionCounter
