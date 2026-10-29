/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackUnaryDivmod
import Mathlib.Tactic.Linarith

/-! # Actual block-by-block unary division execution -/
set_option autoImplicit false
namespace RiemannGaussian.SemiprimeD1StackUnaryDivmodExecution
open Turing Turing.TM2 SemiprimeD1StackUnaryDivmod
open SemiprimeD1StackFiniteControlPaths (SourcePath)

/-- Two real steps consume one input/copy token while the divisor copy remains nonempty. -/
theorem read_more (flag : Option Bool) (input divisor copied quotient remainder : List Bool) :
    Executes 2 (cfg (some .start) flag (true::input) divisor (true::true::copied) [] quotient remainder)
      (cfg (some .start) (some true) input divisor (true::copied) [] quotient (true::remainder)) := by
  have hs : TM2.step program
      (cfg (some .start) flag (true::input) divisor (true::true::copied) [] quotient remainder)=
      some (cfg (some .count) (some true) input divisor (true::true::copied) [] quotient (true::remainder)) := by
    simp [program,cfg,contents,TM2.step,TM2.stepAux]
  have hc : TM2.step program
      (cfg (some .count) (some true) input divisor (true::true::copied) [] quotient (true::remainder))=
      some (cfg (some .start) (some true) input divisor (true::copied) [] quotient (true::remainder)) := by
    simp [program,cfg,contents,TM2.step,TM2.stepAux]
  exact SourcePath.next hs (SourcePath.next hc (.refl _))

/-- The last copied divisor token triggers the actual completed-block phase. -/
theorem read_last (flag : Option Bool) (input divisor quotient remainder : List Bool) :
    Executes 2 (cfg (some .start) flag (true::input) divisor [true] [] quotient remainder)
      (cfg (some .complete) none input divisor [] [] quotient (true::remainder)) := by
  have hs : TM2.step program (cfg (some .start) flag (true::input) divisor [true] [] quotient remainder)=
      some (cfg (some .count) (some true) input divisor [true] [] quotient (true::remainder)) := by
    simp [program,cfg,contents,TM2.step,TM2.stepAux]
  have hc : TM2.step program (cfg (some .count) (some true) input divisor [true] [] quotient (true::remainder))=
      some (cfg (some .complete) none input divisor [] [] quotient (true::remainder)) := by
    simp [program,cfg,contents,TM2.step,TM2.stepAux]
  exact SourcePath.next hs (SourcePath.next hc (.refl _))

/-- A final partial block scans all copied-counter leftovers, then halts. -/
theorem partial_exec (n c r : ℕ) (hc : n<c) (divisor quotient : List Bool) (flag : Option Bool) :
    Executes (n+c+2) (cfg (some .start) flag (unary n) divisor (unary c) [] quotient (unary r))
      (cfg none none [] divisor [] [] quotient (unary (r+n))) := by
  induction n generalizing c r flag with
  | zero =>
    have hs : TM2.step program (cfg (some .start) flag [] divisor (unary c) [] quotient (unary r))=
        some (cfg (some .clearCopy) none [] divisor (unary c) [] quotient (unary r)) := by
      simp [program,cfg,contents,TM2.step,TM2.stepAux]
    simpa [unary] using SourcePath.next hs (clear_copy none divisor (unary c) quotient (unary r))
  | succ n ih =>
    cases c with
    | zero => omega
    | succ c =>
      cases c with
      | zero => omega
      | succ c =>
        have hcn : n<c+1 := by omega
        have ht := ih (c+1) (r+1) hcn (some true)
        have he : r+1+n=r+(n+1) := by omega
        rw [he] at ht
        have hs := read_more flag (unary n) divisor (unary c) quotient (unary r)
        have h := exec_trans hs ht
        convert h using 1 <;> first | omega | simp only [unary_succ]

/-- Every full divisor-sized prefix reaches the actual completion instruction. -/
theorem full_exec (k r : ℕ) (input divisor quotient : List Bool) (flag : Option Bool) :
    Executes (2*(k+1))
      (cfg (some .start) flag (unary (k+1)++input) divisor (unary (k+1)) [] quotient (unary r))
      (cfg (some .complete) none input divisor [] [] quotient (unary (r+(k+1)))) := by
  induction k generalizing r flag with
  | zero => simpa [unary,List.replicate_succ] using read_last flag input divisor quotient (unary r)
  | succ k ih =>
    have ht := ih (r+1) (some true)
    have he : r+1+(k+1)=r+(k+1+1) := by omega
    rw [he] at ht
    have hs := read_more flag (unary (k+1)++input) divisor (unary k) quotient (unary r)
    have h := exec_trans hs ht
    convert h using 1 <;> first | omega | simp only [unary_succ,List.cons_append]

/-- Completed-block quotient increment, remainder clearing and divisor reload are all executed. -/
theorem complete_reload (d : ℕ) (input quotient : List Bool) (flag : Option Bool) :
    Executes (3*d+4)
      (cfg (some .complete) flag input (unary d) [] [] quotient (unary d))
      (cfg (some .start) none input (unary d) (unary d) [] (true::quotient) []) := by
  have hs : TM2.step program (cfg (some .complete) flag input (unary d) [] [] quotient (unary d))=
      some (cfg (some .clearRemainder) flag input (unary d) [] [] (true::quotient) (unary d)) := by
    simp [program,cfg,contents,TM2.step,TM2.stepAux]
  have hc := clear_remainder flag input (unary d) (true::quotient) (unary d)
  have hr := reload_exec none input (unary d) (true::quotient) []
  have h := SourcePath.next hs (exec_trans hc hr)
  simp only [unary,List.length_replicate] at h
  rw [show d+1+(2*d+2)+1=3*d+4 by omega] at h
  exact h


/-- Exact count of actual completed blocks and the final physically scanned partial block. -/
def cycleTime (n d : ℕ) : ℕ := (n/d)*(5*d+4)+(n%d)+d+2

/-- Every completed block physically increments quotient, clears remainder and reloads divisor. -/
theorem cycle_exec (n d : ℕ) (hd : 0<d) (quotient : List Bool) (flag : Option Bool) :
    Executes (cycleTime n d)
      (cfg (some .start) flag (unary n) (unary d) (unary d) [] quotient [])
      (cfg none none [] (unary d) [] [] (unary (n/d)++quotient) (unary (n%d))) := by
  cases d with
  | zero => omega
  | succ k =>
    induction n using Nat.strong_induction_on generalizing quotient flag with
    | h n ih =>
      by_cases hn : n<k+1
      · simpa [cycleTime,Nat.div_eq_of_lt hn,Nat.mod_eq_of_lt hn,unary] using
          partial_exec n (k+1) 0 hn (unary (k+1)) quotient flag
      · have hdn : k+1≤n := by omega
        have hsmall : n-(k+1)<n := by omega
        have hsplit : unary n=unary (k+1)++unary (n-(k+1)) := by
          rw [←unary_add]
          congr 1
          omega
        have hf := full_exec k 0 (unary (n-(k+1))) (unary (k+1)) quotient flag
        simp only [Nat.zero_add] at hf
        rw [←hsplit] at hf
        have hc := complete_reload (k+1) (unary (n-(k+1))) quotient none
        have ht := ih (n-(k+1)) hsmall (true::quotient) none
        have h := exec_trans hf (exec_trans hc ht)
        have hsum : n-(k+1)+(k+1)=n := Nat.sub_add_cancel hdn
        have hdiv : n/(k+1)=(n-(k+1))/(k+1)+1 := by
          rw [←hsum,Nat.add_div_right _ hd]
          simp
        have hmod : n%(k+1)=(n-(k+1))%(k+1) := by
          rw [←hsum,Nat.add_mod_right]
          simp
        have htime : 2*(k+1)+(3*(k+1)+4+cycleTime (n-(k+1)) (k+1))=cycleTime n (k+1) := by
          unfold cycleTime
          rw [hdiv,hmod]
          nlinarith
        rw [htime] at h
        simpa only [hdiv,hmod,unary_succ,unary_bump,show unary 0=[] from rfl,List.cons_append] using h

/-- The zero-divisor guard executes an actual input-to-remainder copy. -/
theorem zero_exec (input remainder quotient : List Bool) (flag : Option Bool) :
    Executes (input.length+1) (cfg (some .zeroCopy) flag input [] [] [] quotient remainder)
      (cfg none none [] [] [] [] quotient (unary input.length++remainder)) := by
  induction input generalizing flag remainder with
  | nil =>
    apply SourcePath.next ?_ (.refl _)
    simp [program,cfg,contents,unary,TM2.step,TM2.stepAux]
  | cons b bs ih =>
    have hs : TM2.step program (cfg (some .zeroCopy) flag (b::bs) [] [] [] quotient remainder)=
        some (cfg (some .zeroCopy) (some b) bs [] [] [] quotient (true::remainder)) := by
      simp [program,cfg,contents,TM2.step,TM2.stepAux]
    simpa [unary_bump] using SourcePath.next hs (ih (true::remainder) (some b))

/-- Exact transition count for the physically guarded divider. -/
def totalTime (n d : ℕ) : ℕ := if d=0 then n+2 else 2*d+3+cycleTime n d

/-- Closed actual division from original unary input/divisor, retaining divisor only. -/
theorem divide_exec (n d : ℕ) :
    Executes (totalTime n d) (cfg (some .entry) none (unary n) (unary d) [] [] [] [])
      (cfg none none [] (unary d) [] [] (unary (n/d)) (unary (n%d))) := by
  cases d with
  | zero =>
    have hs : TM2.step program (cfg (some .entry) none (unary n) [] [] [] [] [])=
        some (cfg (some .zeroCopy) none (unary n) [] [] [] [] []) := by
      simp [program,cfg,contents,TM2.step,TM2.stepAux]
    have ht := zero_exec (unary n) [] [] none
    simpa [totalTime,unary] using SourcePath.next hs ht
  | succ k =>
    have hs : TM2.step program (cfg (some .entry) none (unary n) (unary (k+1)) [] [] [] [])=
        some (cfg (some .reload) (some true) (unary n) (unary (k+1)) [] [] [] []) := by
      simp [program,cfg,contents,unary_succ,TM2.step,TM2.stepAux]
    have hc := reload_exec (some true) (unary n) (unary (k+1)) [] []
    have ht := cycle_exec n (k+1) (by omega) [] none
    simp only [unary,List.length_replicate] at hc ht
    have h := SourcePath.next hs (exec_trans hc ht)
    have he : 2*(k+1)+2+cycleTime n (k+1)+1=totalTime n (k+1) := by
      simp only [totalTime,Nat.succ_ne_zero,ite_false]
      omega
    rw [he] at h
    simpa only [List.append_nil,unary] using h

/-- The exact physical time is linear in acquired unary operand lengths. -/
theorem totalTime_le (n d : ℕ) : totalTime n d≤20*(n+d+1) := by
  by_cases hd : d=0
  · simp [totalTime,hd]; omega
  · have hmul := Nat.div_mul_le_self n d
    have hdiv := Nat.div_le_self n d
    have hmod := Nat.mod_le n d
    simp only [totalTime,hd,ite_false,cycleTime]
    nlinarith

end RiemannGaussian.SemiprimeD1StackUnaryDivmodExecution
