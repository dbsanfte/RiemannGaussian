/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackBinarySquareRootPrimitives
/-! # Actual eighteen-word private-bank erasure after every square-root test -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackBinarySquareRootSweep
open SemiprimeD1StackBinarySquareRoot SemiprimeD1StackBinarySquareRootEncoding
open SemiprimeD1StackBinarySquareRootPrimitives SemiprimeD1StackProcedureTrace
/-- Proof-side prefix of the actual fixed eighteen-role physical sweep. -/
def swept (before : Stack→List Bool) : ℕ→Stack→List Bool
  | 0 => before
  | n+1 => if h:n<18 then Function.update (swept before n) (clearStack ⟨n,h⟩) [] else swept before n
/-- Exact paid pop clock, including every empty-word EOF read. -/
def sweepTime (before : Stack→List Bool) : ℕ→ℕ
  | 0 => 0
  | n+1 => sweepTime before n+if h:n<18 then (swept before n (clearStack ⟨n,h⟩)).length+1 else 0
/-- Actual finite program label at each fixed sweep boundary. -/
def sweepLabel (n : ℕ) : Label := if h:n<18 then ctl (.clear ⟨n,h⟩) else ctl .shift
/-- The finite next-label table agrees with the next sweep boundary. -/
theorem next_label (n : ℕ) (hn : n<18) : clearNext ⟨n,hn⟩=sweepLabel (n+1) := rfl
/-- This is the SAME literal finite source physically draining all visited roles. -/
theorem sweep_run (before : Stack→List Bool) (n : ℕ) (hn : n≤18) :
    Runs program (sweepTime before n) (ctl (.clear 0)) before (sweepLabel n) (swept before n) := by
  induction n with
  | zero => exact runs_refl program _ before
  | succ n ih =>
    have hlt : n<18 := by omega
    have hi:=ih (by omega)
    have hd:=SemiprimeD1StackPhysicalLoops.drain program (ctl (.clear ⟨n,hlt⟩))
      (clearNext ⟨n,hlt⟩) (clearStack ⟨n,hlt⟩) rfl (swept before n)
      (swept before n (clearStack ⟨n,hlt⟩))
    rw [Function.update_eq_self] at hd
    rw [next_label] at hd
    have he : sweepLabel n=ctl (.clear ⟨n,hlt⟩) := dite_eq_left hlt
    rw [he] at hi
    simpa only [sweepTime,swept,dite_eq_left hlt] using join hi hd
/-- Every actually swept role is empty at every later sweep boundary. -/
theorem swept_clear (before : Stack→List Bool) (n : ℕ) (i : Fin 18) (hi : i.val<n) :
    swept before n (clearStack i)=[] := by
  induction n with
  | zero => omega
  | succ n ih =>
    by_cases hn : n<18
    · rw [swept,dite_eq_left hn]
      by_cases he : i.val=n
      · have h : i=⟨n,hn⟩ := Fin.ext he
        rw [h,Function.update_self]
      · rw [Function.update_of_ne (fun h => he (congrArg Fin.val (clear_injective h)))]
        exact ih (by omega)
    · rw [swept,dite_eq_right hn]
      exact ih (by omega)
/-- All foreign metadata and final/root words survive the physical sweep exactly. -/
theorem swept_foreign (before : Stack→List Bool) (n : ℕ) (q : Stack)
    (hq : ∀i,clearStack i≠q) : swept before n q=before q := by
  induction n with
  | zero => rfl
  | succ n ih =>
    by_cases hn : n<18
    · rw [swept,dite_eq_left hn,Function.update_of_ne (Ne.symm (hq ⟨n,hn⟩)),ih]
    · rw [swept,dite_eq_right hn,ih]
/-- The full actual sweep erases exactly all18 private words, retaining all15 others. -/
theorem swept_bank (m : M.Stack→List Bool) (a : A.Stack→List Bool) (x : X.Stack→List Bool)
    (w : W.Stack→List Bool) (u : Aux→List Bool) :
    swept (bank m a x w u) 18=bank m (fun _ => []) (fun _ => []) (fun _ => []) u := by
  funext q
  rcases q with q|q|q|q|q
  · exact swept_foreign _ _ (metadata q) (by intro i;fin_cases i <;> simp [clearStack,metadata,adder,multiply,SemiprimeD1StackBinarySquareRoot.compare])
  · obtain ⟨i,hi⟩ : ∃i,clearStack i=adder q := by cases q <;> decide
    have h:=swept_clear (bank m a x w u) 18 i i.isLt
    rw [hi] at h
    exact h
  · have hs : ∀k : X.Stack,∃i,clearStack i=multiply k := by decide
    obtain ⟨i,hi⟩:=hs q
    have h:=swept_clear (bank m a x w u) 18 i i.isLt
    rw [hi] at h
    exact h
  · have hs : ∀k : W.Stack,∃i,clearStack i=compare k := by decide
    obtain ⟨i,hi⟩:=hs q
    have h:=swept_clear (bank m a x w u) 18 i i.isLt
    rw [hi] at h
    exact h
  · exact swept_foreign _ _ (aux q) (by intro i;fin_cases i <;> cases q <;> simp [clearStack,aux,adder,multiply,SemiprimeD1StackBinarySquareRoot.compare])
/-- Erasure never increases ANY allocated word's length. -/
theorem swept_length (before : Stack→List Bool) (n : ℕ) (q : Stack) :
    (swept before n q).length ≤ (before q).length := by
  induction n with
  | zero => exact Nat.le_refl _
  | succ n ih =>
    by_cases hn : n<18
    · rw [swept,dite_eq_left hn]
      by_cases he : q=clearStack ⟨n,hn⟩
      · rw [he,Function.update_self];exact Nat.zero_le _
      · rw [Function.update_of_ne he];exact ih
    · rw [swept,dite_eq_right hn];exact ih
/-- Clock is bounded by actual initially present word lengths and eighteen EOFs. -/
theorem sweepTime_le (before : Stack→List Bool) (cap n : ℕ)
    (hc : ∀i,(before (clearStack i)).length ≤ cap) : sweepTime before n ≤ n*(cap+1) := by
  induction n with
  | zero => exact Nat.zero_le _
  | succ n ih =>
    rw [sweepTime]
    by_cases hn : n<18
    · rw [dite_eq_left hn]
      have h:=(swept_length before n (clearStack ⟨n,hn⟩)).trans (hc _)
      nlinarith
    · rw [dite_eq_right hn]
      nlinarith
end RiemannGaussian.SemiprimeD1StackBinarySquareRootSweep
