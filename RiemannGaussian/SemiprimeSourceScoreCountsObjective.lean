/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeSourceScoreCountsPadding

/-! # Actual two-lane original collision counts and their source-score identity -/
set_option autoImplicit false
set_option maxHeartbeats 1800000
namespace RiemannGaussian.SemiprimeSourceScoreCountsObjective
open OAI.Algorithms.SubexponentialSAT.MulticolorTypes
open SemiprimeMaterializedWords SemiprimeMaterializedScoreEnvironment
open SemiprimeSourceScoreCounts SemiprimeSourceScoreCountsPadding

/-- Actual incidence and head-collision multiplicities with a common L^4 normalization. -/
structure Counts where
  /-- Sum of normalized TRUE incidence terminals. -/
  incidence : ℕ
  /-- Sum of normalized TRUE head terminals. -/
  head : ℕ

/-- Every source instruction is evaluated once, in its actual list order.
Repeated programs retain their original multiplicities. -/
def evaluateCounts {r Q : ℕ} (alphabet : List (Word r Q)) :
    List (ScoreProgram Q)→List ℕ→Environment r Q→Run Counts
  | [],_,_ => ⟨⟨0,0⟩,1⟩
  | p::programs,remaining,env =>
    let this:=paddedLocal alphabet p remaining env
    let rest:=evaluateCounts alphabet programs remaining env
    let values:=match p with
      | .incidence _ _ _ _ => ⟨this.value+rest.value.incidence,rest.value.head⟩
      | .head _ _ _ => ⟨rest.value.incidence,this.value+rest.value.head⟩
    ⟨values,this.work+rest.work+5⟩

/-- Both actual count lanes are bounded for every source-program prefix. -/
theorem evaluateCounts_le {r Q : ℕ} (alphabet : List (Word r Q)) (programs : List (ScoreProgram Q))
    (remaining : List ℕ) (env : Environment r Q) (hr : remaining.Nodup) :
    (evaluateCounts alphabet programs remaining env).value.incidence≤programs.length*alphabet.length^4 ∧
    (evaluateCounts alphabet programs remaining env).value.head≤programs.length*alphabet.length^4 := by
  induction programs with
  | nil => simp [evaluateCounts]
  | cons p programs ih =>
    have hc:=paddedLocal_le alphabet p remaining env hr
    cases p <;> simp only [evaluateCounts,List.length_cons,Nat.add_mul,Nat.one_mul]
    all_goals constructor <;> omega

/-- A literal take-prefix corollary, including repeated original score instructions. -/
theorem evaluateCounts_prefix_le {r Q : ℕ} (alphabet : List (Word r Q))
    (programs : List (ScoreProgram Q)) (remaining : List ℕ) (env : Environment r Q)
    (hr : remaining.Nodup) (k : ℕ) :
    (evaluateCounts alphabet (programs.take k) remaining env).value.incidence≤
      min k programs.length*alphabet.length^4 ∧
    (evaluateCounts alphabet (programs.take k) remaining env).value.head≤
      min k programs.length*alphabet.length^4 := by
  simpa only [List.length_take] using evaluateCounts_le alphabet (programs.take k) remaining env hr

/-- Exact finite aggregation of original local terms; no supplied count premise. -/
theorem scoreSum_counts {r Q : ℕ} (alphabet : List (Word r Q)) (programs : List (ScoreProgram Q))
    (x y : ℚ) (remaining : List ℕ) (env : Environment r Q)
    (hL : 0<alphabet.length) (hr : remaining.Nodup) :
    (sumRun (fun p => SemiprimeMaterializedScoreSearch.localTerm alphabet x y p remaining env) programs).value=
      (y*y*((evaluateCounts alphabet programs remaining env).value.incidence:ℚ)+
       x*x*((evaluateCounts alphabet programs remaining env).value.head:ℚ))/(alphabet.length:ℚ)^4 := by
  induction programs with
  | nil => simp [sumRun,evaluateCounts]
  | cons p programs ih =>
    have hl:=localTerm_count alphabet x y p remaining env hL hr
    cases p <;> simp only [sumRun,evaluateCounts] <;> rw [hl,ih] <;>
      simp only [weight,Nat.cast_add] <;> ring

/-- The ACTUAL original scalar evaluator is exactly the normalized integer pair. -/
theorem evaluate_counts {r Q : ℕ} (alphabet : List (Word r Q)) (programs : List (ScoreProgram Q))
    (x y offset : ℚ) (remaining : List ℕ) (env : Environment r Q)
    (hL : 0<alphabet.length) (hr : remaining.Nodup) :
    (SemiprimeMaterializedScoreSearch.evaluate alphabet programs x y offset remaining env).value=
      (y^2*((evaluateCounts alphabet programs remaining env).value.incidence:ℚ)+
       x^2*((evaluateCounts alphabet programs remaining env).value.head:ℚ))/(alphabet.length:ℚ)^4-offset := by
  simp only [SemiprimeMaterializedScoreSearch.evaluate,scoreSum_counts alphabet programs x y remaining env hL hr,pow_two]

/-- Acquire the SAME cached reverse-prefix environment and unforced range. -/
def sequentialCounts {r Q : ℕ} (a : Word r Q) (tail : List (Word r Q))
    (programs : List (ScoreProgram Q)) (n : ℕ) (fixed : List (Word r Q)) : Run Counts :=
  let env:=baseEnvironment a fixed
  let result:=evaluateCounts (a::tail) programs (List.range' fixed.length n) env
  ⟨result.value,result.work+2*(Q+1)*(fixed.length+1)+fixed.length+n+2⟩

/-- Exact source-score formula for EVERY actual search prefix, independent of
its reachability or chosen candidate; no score/count callback is assumed. -/
theorem sequential_counts {r Q : ℕ} (a : Word r Q) (tail : List (Word r Q))
    (programs : List (ScoreProgram Q)) (x y offset : ℚ) (n : ℕ) (fixed : List (Word r Q)) :
    (SemiprimeMaterializedScoreSearch.sequential a tail programs x y offset n fixed).value=
      (y^2*((sequentialCounts a tail programs n fixed).value.incidence:ℚ)+
       x^2*((sequentialCounts a tail programs n fixed).value.head:ℚ))/((a::tail).length:ℚ)^4-offset := by
  exact evaluate_counts (a::tail) programs x y offset (List.range' fixed.length n)
    (baseEnvironment a fixed) (by simp) (List.nodup_range')

/-- All prefixes have both counts at most T L^4. -/
theorem sequentialCounts_le {r Q : ℕ} (a : Word r Q) (tail : List (Word r Q))
    (programs : List (ScoreProgram Q)) (n : ℕ) (fixed : List (Word r Q)) :
    (sequentialCounts a tail programs n fixed).value.incidence≤programs.length*(a::tail).length^4 ∧
    (sequentialCounts a tail programs n fixed).value.head≤programs.length*(a::tail).length^4 :=
  evaluateCounts_le (a::tail) programs (List.range' fixed.length n)
    (baseEnvironment a fixed) (List.nodup_range')

end RiemannGaussian.SemiprimeSourceScoreCountsObjective
