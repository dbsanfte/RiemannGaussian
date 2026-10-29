/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeSourceScoreCounts

/-! # Normalized four-coordinate counts of actual local source completions -/
set_option autoImplicit false
set_option maxHeartbeats 1800000
namespace RiemannGaussian.SemiprimeSourceScoreCountsPadding
open OAI.Algorithms.SubexponentialSAT
open LocalExpectation MulticolorTypes
open SemiprimeMaterializedWords SemiprimeMaterializedScoreEnvironment SemiprimeSourceScoreCounts

/-- Execute the at-most-four padding multiplications, rather than accept a power answer. -/
def power (L : ℕ) : ℕ→Run ℕ
  | 0 => ⟨1,1⟩
  | k+1 => let previous:=power L k
           ⟨previous.value*L,previous.work+3⟩

/-- Actual padding value and retained scalar multiplication stages. -/
theorem power_spec (L k : ℕ) : (power L k).value=L^k ∧ (power L k).work=3*k+1 := by
  induction k with
  | zero => simp [power]
  | succ k ih =>
    constructor
    · simpa only [power,pow_succ] using congrArg (fun n => n*L) ih.1
    · simp only [power,ih.2];omega

/-- Actual active-support scan, ordered truth count, and padding to common L^4. -/
def paddedLocal {r Q : ℕ} (alphabet : List (Word r Q)) (p : ScoreProgram Q)
    (remaining : List ℕ) (env : Environment r Q) : Run ℕ :=
  let active:=activeRun (support p) remaining
  let raw:=count alphabet p active.value env
  let pad:=power alphabet.length (4-active.value.length)
  ⟨raw.value*pad.value,active.work+raw.work+pad.work+5⟩

/-- Exact acquired active-list bound; repeated support codes are not deleted
from the original terminal, only the original active membership scan is used. -/
theorem active_length {Q : ℕ} (p : ScoreProgram Q) (remaining : List ℕ) (hr : remaining.Nodup) :
    (activeRun (support p) remaining).value.length≤4 := by
  rw [activeRun_value]
  exact (active_length_le (support p).toFinset remaining hr).trans
    ((List.toFinset_card_le _).trans (support_length p))

/-- Original count-to-common-denominator identity, not an assumed average. -/
theorem padding_division (L C m : ℕ) (hL : 0<L) (hm : m≤4) :
    (C:ℚ)/(L:ℚ)^m=((C*L^(4-m):ℕ):ℚ)/(L:ℚ)^4 := by
  have hln : (L:ℚ)≠0 := by exact_mod_cast Nat.ne_of_gt hL
  have hp : (L:ℚ)^4=(L:ℚ)^m*(L:ℚ)^(4-m) := by rw [← pow_add,Nat.add_sub_of_le hm]
  rw [hp,Nat.cast_mul,Nat.cast_pow]
  field_simp

/-- Every normalized local count is bounded by the SAME four-coordinate leaf count. -/
theorem paddedLocal_le {r Q : ℕ} (alphabet : List (Word r Q)) (p : ScoreProgram Q)
    (remaining : List ℕ) (env : Environment r Q) (hr : remaining.Nodup) :
    (paddedLocal alphabet p remaining env).value≤alphabet.length^4 := by
  let active:=activeRun (support p) remaining
  have hm:=active_length p remaining hr
  have hc:=count_le alphabet p active.value env
  simp only [paddedLocal,(power_spec _ _).1]
  calc
    _≤alphabet.length^active.value.length*alphabet.length^(4-active.value.length) :=
      Nat.mul_le_mul_right _ hc
    _=alphabet.length^4 := by rw [← pow_add,Nat.add_sub_of_le hm]

/-- Local score is the normalized actual integer collision count for all prefixes. -/
theorem localTerm_count {r Q : ℕ} (alphabet : List (Word r Q)) (x y : ℚ)
    (p : ScoreProgram Q) (remaining : List ℕ) (env : Environment r Q)
    (hL : 0<alphabet.length) (hr : remaining.Nodup) :
    (SemiprimeMaterializedScoreSearch.localTerm alphabet x y p remaining env).value=
      weight x y p*((paddedLocal alphabet p remaining env).value:ℚ)/(alphabet.length:ℚ)^4 := by
  have hp:=padding_division alphabet.length
    (count alphabet p (activeRun (support p) remaining).value env).value
    (activeRun (support p) remaining).value.length hL (active_length p remaining hr)
  simp only [SemiprimeMaterializedScoreSearch.localTerm,expectation_count,paddedLocal,(power_spec _ _).1]
  rw [show weight x y p*↑(count alphabet p (activeRun (support p) remaining).value env).value/
      (alphabet.length:ℚ)^(activeRun (support p) remaining).value.length=
      weight x y p*(↑(count alphabet p (activeRun (support p) remaining).value env).value/
      (alphabet.length:ℚ)^(activeRun (support p) remaining).value.length) by ring,hp]
  ring

end RiemannGaussian.SemiprimeSourceScoreCountsPadding
