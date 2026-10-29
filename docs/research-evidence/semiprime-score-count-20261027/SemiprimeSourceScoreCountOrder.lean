/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeSourceScoreCountsObjective
import RiemannGaussian.SemiprimeSourceScoreCancellation

/-! # Original acquired count lanes preserve scheduled source-score order
The original score is identified with its actually executed finite count
recurrence. Shared factors and offsets then cancel, at every original search
prefix, without an assumed count or scalar-score answer.
-/
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace RiemannGaussian.SemiprimeSourceScoreCountOrder
open SemiprimeSourceScoreCancellation SemiprimeSourceScoreCountsObjective
open OAI.Algorithms.SubexponentialSAT.MulticolorTypes
open SemiprimeMaterializedScoreEnvironment

/-- The integer objective of the actual original finite count producer. -/
def integerValue {r Q : ℕ} (M n lam U : ℕ) (a : Word r Q) (tail : List (Word r Q))
    (programs : List (ScoreProgram Q)) (s : ℕ) (fixed : List (Word r Q)) : ℕ :=
  let counts := sequentialCounts a tail programs s fixed
  weight M n lam U counts.value.incidence counts.value.head

/-- The actual original score, at its original schedule, has the count form used
by denominator cancellation. The only size identity is the actual alphabet/bank size. -/
theorem sequential_score {r Q : ℕ} (M n lam U : ℕ) (a : Word r Q) (tail : List (Word r Q))
    (programs : List (ScoreProgram Q)) (offset : ℚ) (s : ℕ) (fixed : List (Word r Q))
    (hcard : (a::tail).length^4=U^2) :
    (SemiprimeMaterializedScoreSearch.sequential a tail programs
      ((M:ℚ)/((r:ℚ)*(lam:ℚ)*(U:ℚ))) ((n:ℚ)/(2*(r:ℚ))) offset s fixed).value =
      score M n r lam U (sequentialCounts a tail programs s fixed).value.incidence
        (sequentialCounts a tail programs s fixed).value.head offset := by
  have hc : ((a::tail).length:ℚ)^4=(U:ℚ)^2 := by exact_mod_cast hcard
  rw [sequential_counts,hc]
  rfl

/-- Every pair of actually produced prefix scores has exactly the integer count order. -/
theorem integer_le_iff {r Q : ℕ} (M n lam U : ℕ) (a : Word r Q) (tail : List (Word r Q))
    (programs : List (ScoreProgram Q)) (offset : ℚ) (s t : ℕ) (fixed other : List (Word r Q))
    (hr : 0 < r) (hlam : 0 < lam) (hU : 0 < U) (hcard : (a::tail).length^4=U^2) :
    integerValue M n lam U a tail programs s fixed ≤ integerValue M n lam U a tail programs t other ↔
      (SemiprimeMaterializedScoreSearch.sequential a tail programs
        ((M:ℚ)/((r:ℚ)*(lam:ℚ)*(U:ℚ))) ((n:ℚ)/(2*(r:ℚ))) offset s fixed).value ≤
      (SemiprimeMaterializedScoreSearch.sequential a tail programs
        ((M:ℚ)/((r:ℚ)*(lam:ℚ)*(U:ℚ))) ((n:ℚ)/(2*(r:ℚ))) offset t other).value := by
  rw [sequential_score M n lam U a tail programs offset s fixed hcard,
    sequential_score M n lam U a tail programs offset t other hcard]
  exact weight_le_iff M n r lam U _ _ _ _ offset hr hlam hU

/-- ORIGINAL source enumeration cardinalities discharge the shared denominator identity. -/
theorem caller_cardinality {I E : Type} {n r Q : ℕ}
    (en : SemiprimeSourceLayout.Enumerations I (Fin n) E r Q) :
    (en.wordFirst::en.wordTail).length^4=(en.types.values.length)^2 := by
  rw [SemiprimeSourceOffsetHeight.caller_word_length,SemiprimeSourceOffsetHeight.caller_universal_length]
  exact (bank_square r Q).symm

/-- Original resource caps bound every produced integer objective, at all prefixes. -/
theorem integerValue_bound {r Q : ℕ} (M n lam U : ℕ) (a : Word r Q) (tail : List (Word r Q))
    (programs : List (ScoreProgram Q)) (s : ℕ) (fixed : List (Word r Q))
    (hcard : (a::tail).length^4=U^2) :
    integerValue M n lam U a tail programs s fixed ≤
      programs.length*U^2*(n^2*lam^2*U^2+4*M^2) := by
  have hc := sequentialCounts_le a tail programs s fixed
  rw [hcard] at hc
  exact weight_bound M n lam U _ _ programs.length hc.1 hc.2

end RiemannGaussian.SemiprimeSourceScoreCountOrder
