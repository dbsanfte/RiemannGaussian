/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeSourceWordIdCountsCore

/-! # Physical-ID count circuit resources
Reachable-state caps are internal proof interfaces; the original-bank endpoint
uses the concrete copied-key push and concrete bank predicate.
-/
set_option autoImplicit false
namespace RiemannGaussian.SemiprimeSourceWordIdCountsBudget
open SemiprimeMaterializedWords (Run activeRun)
open SemiprimeSourceOffsetInputsCore SemiprimeBitArithmetic
open SemiprimeSourceScoreCountBitsCore (sumBits_clock)
open SemiprimeSourceWordIdCountsCore
open SemiprimeMaterializedScoreEnvironment

/-- Exact reachable-state obligations for both paid physical pushes and leaves. -/
def Cap {σ : Type*} (ids : List (List Bool))
    (push : σ→ List Bool→ List Bool→ Run σ) (terminal : σ→ Run Bool) (P T : ℕ) :
    List (List Bool)→σ→ Prop
  | [],env => (terminal env).work≤ T
  | key::keys,env => ∀ id∈ids,(push env key id).work≤ P ∧
      Cap ids push terminal P T keys (push env key id).value

/-- Original-depth branch adder and copied-push report envelope. -/
def budget (L P T : ℕ) : ℕ→ℕ
  | 0 => T+2
  | m+1 => L*(P+budget L P T m+3+11*(1+m*L+L)+7)+1+L+3

/-- Every actual push, child and adder stays in the retained count report. -/
theorem count_clock {σ : Type*} (ids : List (List Bool))
    (push : σ→ List Bool→ List Bool→ Run σ) (terminal : σ→ Run Bool)
    (P T : ℕ) (keys : List (List Bool)) (env : σ)
    (h : Cap ids push terminal P T keys env) :
    (count ids push terminal keys env).clock≤ budget ids.length P T keys.length := by
  induction keys generalizing env with
  | nil => exact Nat.add_le_add_right h 2
  | cons key keys ih =>
    have hh:=sumBits_clock (fun id =>
      let next:=push env key id
      let child:=count ids push terminal keys next.value
      (⟨child.bits,next.work+child.clock+3⟩:NatRun)) ids
      (1+keys.length*ids.length) (P+budget ids.length P T keys.length+3)
      (fun id _ => count_length ids push terminal keys (push env key id).value)
      (fun id hi => Nat.add_le_add_right (Nat.add_le_add (h id hi).1 (ih _ (h id hi).2)) 3)
    simpa only [count,budget,List.length_cons,Nat.add_assoc] using
      Nat.add_le_add_right (Nat.add_le_add_right hh ids.length) 3

/-- At most four original active keys give at most four completion levels. -/
theorem budget_mono_depth (L P T m : ℕ) (hL : 0< L) :
    budget L P T m≤ budget L P T (m+1) := by
  have h : budget L P T m≤ L*budget L P T m := by
    simpa only [Nat.one_mul] using Nat.mul_le_mul_right (budget L P T m) hL
  have h' := Nat.mul_le_mul_left L
    (show budget L P T m≤ P+budget L P T m+3+11*(1+m*L+L)+7 from by omega)
  change budget L P T m≤ L*(P+budget L P T m+3+11*(1+m*L+L)+7)+1+L+3
  omega

/-- The original support-four bound specializes the actual recursive cap. -/
theorem budget_le_four (L P T m : ℕ) (hL : 0< L) (hm : m≤4) :
    budget L P T m≤ budget L P T 4 :=
  monotone_nat_of_le_succ (fun k => budget_mono_depth L P T k hL) hm

/-- Direct structural padding width, without a numerical count-answer premise. -/
theorem padded_length {σ : Type*} {Q : ℕ} (ids : List (List Bool))
    (push : σ→ List Bool→ List Bool→ Run σ) (terminal : σ→ Run Bool)
    (p : ScoreProgram Q) (remaining : List ℕ) (env : σ)
    (hL : 0< ids.length) (hr : remaining.Nodup) :
    (padded ids push terminal p remaining env).bits.length≤3+8*ids.length+ids.length^4 := by
  have ha:=SemiprimeSourceScoreCountsPadding.active_length p remaining hr
  have hc:=count_length ids push terminal (acquireKeys (activeRun (support p) remaining).value).value env
  rw [acquireKeys_length] at hc
  have he:=natBits_length (unaryPower ids.length (4-(activeRun (support p) remaining).value.length)).cells.length
  have hm:=mulBits_length
    (count ids push terminal (acquireKeys (activeRun (support p) remaining).value).value env).bits
    (natBits (unaryPower ids.length (4-(activeRun (support p) remaining).value.length)).cells.length).bits
  simp only [unaryPower_length] at he hm
  have hp:ids.length^(4-(activeRun (support p) remaining).value.length)≤ ids.length^4 :=
    Nat.pow_le_pow_right hL (by omega)
  have hca: (count ids push terminal (acquireKeys (activeRun (support p) remaining).value).value env).bits.length≤
      1+4*ids.length := hc.trans (by gcongr)
  simp only [padded,unaryPower_length]
  omega

/-- Every actual lane suffix has a structural physical-word bound. -/
theorem evaluate_length {σ : Type*} {Q : ℕ} (ids : List (List Bool))
    (push : σ→ List Bool→ List Bool→ Run σ) (terminal : ScoreProgram Q→σ→ Run Bool)
    (programs : List (ScoreProgram Q)) (remaining : List ℕ) (env : σ)
    (hL : 0< ids.length) (hr : remaining.Nodup) :
    (evaluate ids push terminal programs remaining env).incidence.length≤
      3+8*ids.length+ids.length^4+programs.length ∧
    (evaluate ids push terminal programs remaining env).head.length≤
      3+8*ids.length+ids.length^4+programs.length := by
  induction programs with
  | nil => simp [evaluate]
  | cons p programs ih =>
    have ht:=padded_length ids push (terminal p) p remaining env hL hr
    have hi:=(addBits_counts (padded ids push (terminal p) p remaining env).bits
      (evaluate ids push terminal programs remaining env).incidence false).2.2.2.2
    have hh:=(addBits_counts (padded ids push (terminal p) p remaining env).bits
      (evaluate ids push terminal programs remaining env).head false).2.2.2.2
    cases p <;> simp only [evaluate,List.length_cons] <;> constructor <;> omega

end RiemannGaussian.SemiprimeSourceWordIdCountsBudget
