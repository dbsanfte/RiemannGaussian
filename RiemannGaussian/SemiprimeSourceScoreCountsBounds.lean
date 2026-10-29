/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeSourceScoreCountsObjective

/-! # Actual native count-prefix and producer-work bounds
No terminal/count/work answer is supplied by the original caller. These are
integer/scalar/list ledgers, not a claim of a complete primitive-bit compiler.
-/
set_option autoImplicit false
set_option maxHeartbeats 1800000
namespace RiemannGaussian.SemiprimeSourceScoreCountsBounds
open OAI.Algorithms.SubexponentialSAT.MulticolorTypes
open SemiprimeMaterializedWords SemiprimeMaterializedScoreEnvironment
open SemiprimeSourceScoreCounts SemiprimeSourceScoreCountsPadding SemiprimeSourceScoreCountsObjective

/-- Every actual branch-sum prefix or suffix has at most the full leaf count.
Only its literal list length matters; duplicates and override collisions remain. -/
theorem branch_partial_le {r Q : ℕ} (alphabet xs : List (Word r Q)) (p : ScoreProgram Q)
    (remaining : List ℕ) (env : Environment r Q) (i : ℕ) (hlen : xs.length≤alphabet.length) :
    (sumCount (fun w => count alphabet p remaining (extend env i w)) xs).value≤
      alphabet.length^(remaining.length+1) := by
  have h:=sumCount_le (fun w => count alphabet p remaining (extend env i w)) xs
    (alphabet.length^remaining.length) (fun w _ => count_le alphabet p remaining (extend env i w))
  apply h.trans
  rw [pow_succ]
  exact (Nat.mul_le_mul_right _ hlen).trans_eq (Nat.mul_comm _ _)

/-- Every ACTUAL padding multiplication prefix stays within L^4. -/
theorem padding_prefix_le {r Q : ℕ} (alphabet : List (Word r Q)) (p : ScoreProgram Q)
    (remaining : List ℕ) (env : Environment r Q) (hr : remaining.Nodup)
    (hL : 0<alphabet.length) (k : ℕ)
    (hk : k≤4-(activeRun (support p) remaining).value.length) :
    (count alphabet p (activeRun (support p) remaining).value env).value*(power alphabet.length k).value≤
      alphabet.length^4 := by
  have hm:=active_length p remaining hr
  have hc:=count_le alphabet p (activeRun (support p) remaining).value env
  rw [(power_spec _ _).1]
  calc
    _≤alphabet.length^(activeRun (support p) remaining).value.length*alphabet.length^k :=
      Nat.mul_le_mul_right _ hc
    _=alphabet.length^((activeRun (support p) remaining).value.length+k) := (pow_add _ _ _).symm
    _≤alphabet.length^4 := Nat.pow_le_pow_right hL (by omega)

/-- Every suffix actually returned by the original recursive program sum. -/
theorem evaluateCounts_suffix_le {r Q : ℕ} (alphabet : List (Word r Q))
    (programs : List (ScoreProgram Q)) (remaining : List ℕ) (env : Environment r Q)
    (hr : remaining.Nodup) (k : ℕ) :
    (evaluateCounts alphabet (programs.drop k) remaining env).value.incidence≤
      (programs.length-k)*alphabet.length^4 ∧
    (evaluateCounts alphabet (programs.drop k) remaining env).value.head≤
      (programs.length-k)*alphabet.length^4 := by
  simpa only [List.length_drop] using evaluateCounts_le alphabet (programs.drop k) remaining env hr

/-- The new normalization executes at most thirteen extra native power stages. -/
theorem paddedLocal_work_le_old {r Q : ℕ} (alphabet : List (Word r Q)) (p : ScoreProgram Q)
    (remaining : List ℕ) (env : Environment r Q) :
    (paddedLocal alphabet p remaining env).work≤
      (SemiprimeMaterializedScoreSearch.localTerm alphabet 0 0 p remaining env).work+13 := by
  have hw:=count_work_eq alphabet 0 0 p (activeRun (support p) remaining).value env
  have hp:=(power_spec alphabet.length (4-(activeRun (support p) remaining).value.length)).2
  simp only [paddedLocal,SemiprimeMaterializedScoreSearch.localTerm]
  rw [hw,hp]
  omega

/-- Closed native per-instruction work from original dimensions. -/
def termBudget (A N Q : ℕ) : ℕ := N*12+(A+1)^5*(terminalBudget N 4 Q+Q+20)+19

/-- Both active scans and every TRUE-leaf predicate are actually executed and paid. -/
theorem paddedLocal_work {r Q : ℕ} (alphabet : List (Word r Q)) (p : ScoreProgram Q)
    (remaining : List ℕ) (env : Environment r Q) (N : ℕ)
    (hn : env.fixed.length≤N) (ho : env.overrides=[]) (hr : remaining.Nodup)
    (hlen : remaining.length≤N) :
    (paddedLocal alphabet p remaining env).work≤termBudget alphabet.length N Q := by
  have h:=paddedLocal_work_le_old alphabet p remaining env
  have hold:=SemiprimeMaterializedScoreSearch.localTerm_work alphabet 0 0 p remaining env N hn ho hr
  unfold termBudget
  have hh : remaining.length*12≤N*12 := Nat.mul_le_mul_right _ hlen
  omega

/-- Every original term is acquired once, with no supplied producer budget. -/
theorem evaluateCounts_work {r Q : ℕ} (alphabet : List (Word r Q)) (programs : List (ScoreProgram Q))
    (remaining : List ℕ) (env : Environment r Q) (N : ℕ)
    (hn : env.fixed.length≤N) (ho : env.overrides=[]) (hr : remaining.Nodup)
    (hlen : remaining.length≤N) :
    (evaluateCounts alphabet programs remaining env).work≤
      programs.length*(termBudget alphabet.length N Q+5)+1 := by
  induction programs with
  | nil => simp [evaluateCounts]
  | cons p programs ih =>
    have hp:=paddedLocal_work alphabet p remaining env N hn ho hr hlen
    simp only [evaluateCounts,List.length_cons,Nat.add_mul,Nat.one_mul]
    omega

/-- Complete original-prefix count producer envelope. -/
def sequentialBudget (A T N Q : ℕ) : ℕ :=
  T*(termBudget A N Q+5)+1+2*(Q+1)*(N+1)+N+2

/-- Complete count production has a fixed polynomial native scalar/list ledger. -/
theorem sequentialCounts_work {r Q : ℕ} (a : Word r Q) (tail : List (Word r Q))
    (programs : List (ScoreProgram Q)) (n N : ℕ) (fixed : List (Word r Q))
    (hlen : n+fixed.length≤N) :
    (sequentialCounts a tail programs n fixed).work≤
      sequentialBudget (a::tail).length programs.length N Q := by
  have h:=evaluateCounts_work (a::tail) programs (List.range' fixed.length n)
    (baseEnvironment a fixed) N
    (by simpa only [baseEnvironment,List.length_map] using (show fixed.length≤N by omega))
    rfl (List.nodup_range') (by simpa only [List.length_range'] using (show n≤N by omega))
  have hf : fixed.length≤N := by omega
  have hm := Nat.mul_le_mul_left (2*(Q+1)) (Nat.add_le_add_right hf 1)
  simp only [sequentialCounts,sequentialBudget]
  omega

end RiemannGaussian.SemiprimeSourceScoreCountsBounds
