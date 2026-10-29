/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeMaterializedScoreEnvironment

/-! # Executed conditional expectations over cached finite environments -/
set_option autoImplicit false
set_option maxHeartbeats 1600000
namespace RiemannGaussian.SemiprimeMaterializedScoreSearch
open OAI.Algorithms.SubexponentialSAT
open LocalExpectation MulticolorTypes
open SemiprimeMaterializedWords SemiprimeMaterializedScoreEnvironment

/-- Every local completion pushes a stored override, never a functional update. -/
def expectation {r Q : ℕ} (alphabet : List (Word r Q)) (x y : ℚ) (p : ScoreProgram Q) :
    List ℕ → Environment r Q → Run ℚ
  | [], env =>
    let result := terminal x y p env
    ⟨result.value,result.work+1⟩
  | i::remaining, env =>
    let result := sumRun (fun w =>
      let child := expectation alphabet x y p remaining (extend env i w)
      ⟨child.value,child.work+Q+2⟩) alphabet
    ⟨result.value/(alphabet.length : ℚ),result.work+alphabet.length+3⟩

/-- Exact finite averaging of the ORIGINAL score, without an assignment-function oracle. -/
theorem expectation_value {r Q : ℕ} (alphabet : List (Word r Q)) (x y : ℚ)
    (p : ScoreProgram Q) (remaining : List ℕ) (env : Environment r Q) :
    (expectation alphabet x y p remaining env).value =
      wordExpectation alphabet (programValue x y p) remaining (denote env) := by
  induction remaining generalizing env with
  | nil => exact terminal_value x y p env
  | cons i remaining ih =>
    simp only [expectation,wordExpectation,ConditionalExpectation.mean,sumRun_value]
    congr 2
    apply List.map_congr_left
    intro w _
    exact (ih (extend env i w)).trans (congrArg (wordExpectation alphabet (programValue x y p) remaining)
      (denote_extend env i w))

/-- Local traversal includes actual terminal production and coordinate caching. -/
theorem expectation_work {r Q : ℕ} (alphabet : List (Word r Q)) (x y : ℚ)
    (p : ScoreProgram Q) (remaining : List ℕ) (env : Environment r Q) (N s : ℕ)
    (hn : env.fixed.length≤N) (hs : env.overrides.length+remaining.length≤ s) :
    (expectation alphabet x y p remaining env).work ≤
      (alphabet.length+1)^(remaining.length+1)*(terminalBudget N s Q+Q+20) := by
  induction remaining generalizing env with
  | nil =>
    have ht := terminal_work x y p env N s hn (by simpa using hs)
    simp only [expectation,List.length_nil,Nat.zero_add,pow_one]
    nlinarith
  | cons i remaining ih =>
    let A := alphabet.length
    let B := terminalBudget N s Q
    let D := (A+1)^(remaining.length+1)*(B+Q+20)
    have hc (w : Word r Q) :
        (expectation alphabet x y p remaining (extend env i w)).work ≤ D := by
      apply ih
      · exact hn
      · simp only [extend,List.length_cons] at *
        omega
    have hb := sumRun_work (fun w =>
      let child := expectation alphabet x y p remaining (extend env i w)
      (⟨child.value,child.work+Q+2⟩ : Run ℚ)) alphabet (D+Q+2)
      (fun w _ => Nat.add_le_add_right (Nat.add_le_add_right (hc w) Q) 2)
    have hp : A+1≤(A+1)^(remaining.length+1) :=
      by simpa using Nat.pow_le_pow_right (by omega : 0<A+1) (by omega : 1≤remaining.length+1)
    have hd : A*(Q+6)+4≤D := by dsimp [D]; nlinarith
    change (sumRun _ alphabet).work+A+3≤_
    simp only [List.length_cons,pow_succ]
    change (sumRun _ alphabet).work+A+3≤(A+1)^(remaining.length+1)*(A+1)*(B+Q+20)
    dsimp [D] at hb hd
    dsimp [A] at *
    nlinarith

/-- One term first computes its active support list by the real membership scan. -/
def localTerm {r Q : ℕ} (alphabet : List (Word r Q)) (x y : ℚ) (p : ScoreProgram Q)
    (remaining : List ℕ) (env : Environment r Q) : Run ℚ :=
  let selected := activeRun (support p) remaining
  let result := expectation alphabet x y p selected.value env
  ⟨result.value,selected.work+result.work+5⟩

/-- Supports are the concrete code lists stored in the score instruction. -/
theorem localTerm_value {r Q : ℕ} (alphabet : List (Word r Q)) (x y : ℚ) (p : ScoreProgram Q)
    (remaining : List ℕ) (env : Environment r Q) :
    (localTerm alphabet x y p remaining env).value =
      wordExpectation alphabet (programValue x y p) (active (support p).toFinset remaining) (denote env) := by
  simp only [localTerm,expectation_value,activeRun_value]

/-- At most four overrides per term; the prefix is cached and all scans are paid. -/
theorem localTerm_work {r Q : ℕ} (alphabet : List (Word r Q)) (x y : ℚ) (p : ScoreProgram Q)
    (remaining : List ℕ) (env : Environment r Q) (N : ℕ)
    (hn : env.fixed.length≤N) (ho : env.overrides=[]) (hr : remaining.Nodup) :
    (localTerm alphabet x y p remaining env).work ≤
      remaining.length*12+(alphabet.length+1)^5*(terminalBudget N 4 Q+Q+20)+6 := by
  have ha := activeRun_work (support p) remaining
  have hl : (activeRun (support p) remaining).value.length≤4 := by
    rw [activeRun_value]
    exact (active_length_le (support p).toFinset remaining hr).trans
      ((List.toFinset_card_le _).trans (support_length p))
  have he := expectation_work alphabet x y p (activeRun (support p) remaining).value env N 4 hn
    (by simpa only [ho,List.length_nil,Nat.zero_add] using hl)
  have hp := Nat.pow_le_pow_right (by omega : 0<alphabet.length+1) (Nat.add_le_add_right hl 1)
  have hmul := Nat.mul_le_mul_right (terminalBudget N 4 Q+Q+20) hp
  norm_num only at hmul
  have hsupport := support_length p
  have hm := Nat.mul_le_mul_left remaining.length (show 2*(support p).length+4≤12 by omega)
  change (activeRun _ remaining).work+(expectation _ _ _ _ _ _).work+5≤_
  omega

/-- Sum every actual source score instruction and subtract the actual offset. -/
def evaluate {r Q : ℕ} (alphabet : List (Word r Q)) (programs : List (ScoreProgram Q))
    (x y offset : ℚ) (remaining : List ℕ) (env : Environment r Q) : Run ℚ :=
  let result := sumRun (fun p => localTerm alphabet x y p remaining env) programs
  ⟨result.value-offset,result.work+2⟩

/-- The computed objective is exactly the published local evaluator. -/
theorem evaluate_value {r Q : ℕ} (alphabet : List (Word r Q)) (programs : List (ScoreProgram Q))
    (x y offset : ℚ) (remaining : List ℕ) (env : Environment r Q) :
    (evaluate alphabet programs x y offset remaining env).value=
      localEvaluator alphabet programs (fun p => (support p).toFinset)
        (programValue x y) offset remaining (denote env) := by
  simp only [evaluate,localEvaluator,sumRun_value,localTerm_value]

/-- Execute prefix caching and range acquisition before any local objective calls. -/
def sequential {r Q : ℕ} (a : Word r Q) (tail : List (Word r Q))
    (programs : List (ScoreProgram Q)) (x y offset : ℚ) (n : ℕ) (fixed : List (Word r Q)) : Run ℚ :=
  let env := baseEnvironment a fixed
  let result := evaluate (a::tail) programs x y offset (List.range' fixed.length n) env
  ⟨result.value,result.work+2*(Q+1)*(fixed.length+1)+fixed.length+n+2⟩

/-- The reverse-prefix convention and all overridden values match the source. -/
theorem sequential_value {r Q : ℕ} (a : Word r Q) (tail : List (Word r Q))
    (programs : List (ScoreProgram Q)) (x y offset : ℚ) (n : ℕ) (fixed : List (Word r Q)) :
    (sequential a tail programs x y offset n fixed).value=
      sequentialEvaluator (a::tail) programs (fun p => (support p).toFinset)
        (programValue x y) offset a n fixed := by
  simp only [sequential,sequentialEvaluator,evaluate_value,denote_baseEnvironment]

/-- Fixed polynomial objective envelope, including actual decoder/override reads. -/
def evaluatorBudget (A T N Q : ℕ) : ℕ :=
  T*(N*12+(A+1)^5*(terminalBudget N 4 Q+Q+20)+9)+3+
    2*(Q+1)*(N+1)+N+2

/-- No arbitrary terminal budget is assumed in this original-score evaluator. -/
theorem sequential_work {r Q : ℕ} (a : Word r Q) (tail : List (Word r Q))
    (programs : List (ScoreProgram Q)) (x y offset : ℚ) (n N : ℕ) (fixed : List (Word r Q))
    (hlen : n+fixed.length≤N) :
    (sequential a tail programs x y offset n fixed).work ≤
      evaluatorBudget (a::tail).length programs.length N Q := by
  have hs := sumRun_work
    (fun p => localTerm (a::tail) x y p (List.range' fixed.length n) (baseEnvironment a fixed)) programs
    (N*12+((a::tail).length+1)^5*(terminalBudget N 4 Q+Q+20)+6) (by
      intro p _
      have h := localTerm_work (a::tail) x y p (List.range' fixed.length n)
        (baseEnvironment a fixed) N (by simpa only [baseEnvironment,List.length_map] using (show fixed.length≤N by omega))
        rfl (List.nodup_range')
      simp only [List.length_range'] at h
      exact h.trans (by gcongr; omega))
  have he : N*12+((a::tail).length+1)^5*(terminalBudget N 4 Q+Q+20)+6+3 =
      N*12+((a::tail).length+1)^5*(terminalBudget N 4 Q+Q+20)+9 := by omega
  rw [he] at hs
  have hfix : fixed.length≤N := by omega
  have hc := Nat.mul_le_mul_left (2*(Q+1)) (Nat.add_le_add_right hfix 1)
  change (sumRun _ programs).work+2+2*(Q+1)*(fixed.length+1)+fixed.length+n+2≤_
  unfold evaluatorBudget
  omega

/-- Complete deterministic original-score search; no chosen label is supplied. -/
def search {r Q : ℕ} (a : Word r Q) (tail : List (Word r Q))
    (programs : List (ScoreProgram Q)) (x y offset : ℚ) (N : ℕ) : Run (List (Word r Q)) :=
  assign a tail (sequential a tail programs x y offset) N []

/-- Exact deterministic output, not merely an equally good objective value. -/
theorem search_value {r Q : ℕ} (a : Word r Q) (tail : List (Word r Q))
    (programs : List (ScoreProgram Q)) (x y offset : ℚ) (N : ℕ) :
    (search a tail programs x y offset N).value =
      localAssign a tail programs (fun p => (support p).toFinset)
        (programValue x y) offset a N := by
  simp only [search,assign_value,localAssign]
  congr 1
  funext n fixed
  exact sequential_value a tail programs x y offset n fixed

/-- Full fixed-polynomial scalar/control envelope in the actual finite dimensions. -/
theorem search_work {r Q : ℕ} (a : Word r Q) (tail : List (Word r Q))
    (programs : List (ScoreProgram Q)) (x y offset : ℚ) (N : ℕ) :
    (search a tail programs x y offset N).work ≤
      N*(tail.length*(2*evaluatorBudget (a::tail).length programs.length N Q+3)+4)+1 :=
  assign_work a tail (sequential a tail programs x y offset)
    (evaluatorBudget (a::tail).length programs.length N Q) N
    (fun n fixed hn => sequential_work a tail programs x y offset n N fixed hn)
    N [] (by simp)

end RiemannGaussian.SemiprimeMaterializedScoreSearch
