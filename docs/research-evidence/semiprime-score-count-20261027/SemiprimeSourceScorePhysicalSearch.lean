/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeSourceScoreCountBits
import RiemannGaussian.SemiprimeSourceScoreWeightAcquisition
import RiemannGaussian.SemiprimeSourceScoreCountOrder
import RiemannGaussian.SemiprimeSourceScoreChoice

/-! # Original source search driven by actual physical integer counts
Weights are acquired once. Each candidate is scored by actual Boolean terminal,
counter and weighted-arithmetic circuits; the physical comparator drives source
label selection. Host source labels, natural loop indices and original descriptor
construction remain explicit metadata interfaces, not a whole tape-machine proof.
-/
set_option autoImplicit false
set_option maxHeartbeats 1200000
namespace RiemannGaussian.SemiprimeSourceScorePhysicalSearch
open SemiprimeRationalBits SemiprimeMaterializedWords
open OAI.Algorithms.SubexponentialSAT.MulticolorTypes
open SemiprimeMaterializedScoreEnvironment

/-- Actual cached-input physical scores are the cancelled integer objective. -/
theorem score_value {r Q : ℕ} (M n lam : ℕ) (a : Word r Q) (tail : List (Word r Q))
    (programs : List (ScoreProgram Q)) (s : ℕ) (fixed : List (Word r Q)) :
    (SemiprimeSourceScoreCountBits.score (SemiprimeSourceScoreWeightAcquisition.acquire M n r Q lam)
      a tail programs s fixed).word.value =
      (SemiprimeSourceScoreCountOrder.integerValue M n lam (r^(2*Q)) a tail programs s fixed:ℚ) := by
  rw [SemiprimeSourceScoreCountBits.score_value,
    (SemiprimeSourceScoreWeightAcquisition.acquire_value M n r Q lam).1,
    (SemiprimeSourceScoreWeightAcquisition.acquire_value M n r Q lam).2]
  rfl

/-- The physical callback preserves all comparisons of the ORIGINAL objective. -/
theorem score_order {r Q : ℕ} (M n lam : ℕ) (a : Word r Q) (tail : List (Word r Q))
    (programs : List (ScoreProgram Q)) (offset : ℚ) (s t : ℕ) (fixed other : List (Word r Q))
    (hr : 0 < r) (hlam : 0 < lam) (hcard : (a::tail).length^4=(r^(2*Q))^2) :
    (SemiprimeSourceScoreCountBits.score (SemiprimeSourceScoreWeightAcquisition.acquire M n r Q lam)
      a tail programs s fixed).word.value ≤
      (SemiprimeSourceScoreCountBits.score (SemiprimeSourceScoreWeightAcquisition.acquire M n r Q lam)
        a tail programs t other).word.value ↔
      (SemiprimeMaterializedScoreSearch.sequential a tail programs
        ((M:ℚ)/((r:ℚ)*(lam:ℚ)*(r^(2*Q):ℕ))) ((n:ℚ)/(2*(r:ℚ))) offset s fixed).value ≤
      (SemiprimeMaterializedScoreSearch.sequential a tail programs
        ((M:ℚ)/((r:ℚ)*(lam:ℚ)*(r^(2*Q):ℕ))) ((n:ℚ)/(2*(r:ℚ))) offset t other).value := by
  rw [score_value,score_value]
  have hc :
      (SemiprimeSourceScoreCountOrder.integerValue M n lam (r^(2*Q)) a tail programs s fixed:ℚ) ≤
        (SemiprimeSourceScoreCountOrder.integerValue M n lam (r^(2*Q)) a tail programs t other:ℚ) ↔
      SemiprimeSourceScoreCountOrder.integerValue M n lam (r^(2*Q)) a tail programs s fixed ≤
        SemiprimeSourceScoreCountOrder.integerValue M n lam (r^(2*Q)) a tail programs t other := by
    exact_mod_cast Iff.rfl
  exact hc.trans (SemiprimeSourceScoreCountOrder.integer_le_iff M n lam (r^(2*Q))
    a tail programs offset s t fixed other hr hlam (pow_pos hr _) hcard)

/-- Acquire original integer weights ONCE and execute the actual candidate callback. -/
def run {r Q : ℕ} (M n lam : ℕ) (a : Word r Q) (tail : List (Word r Q))
    (programs : List (ScoreProgram Q)) (N : ℕ) : Run (List (Word r Q)) :=
  let weights := SemiprimeSourceScoreWeightAcquisition.acquire M n r Q lam
  let out := SemiprimeSourceScoreChoice.assign a tail
    (SemiprimeSourceScoreCountBits.score weights a tail programs) N []
  ⟨out.value,weights.clock+out.work+2⟩

/-- The new execution returns the EXACT original deterministic source labels.
Offset and rational scale values are proof-side only and are absent from runtime inputs. -/
theorem run_refines {r Q : ℕ} (M n lam : ℕ) (a : Word r Q) (tail : List (Word r Q))
    (programs : List (ScoreProgram Q)) (N : ℕ) (offset : ℚ)
    (hr : 0 < r) (hlam : 0 < lam) (hcard : (a::tail).length^4=(r^(2*Q))^2) :
    (run M n lam a tail programs N).value =
      (SemiprimeMaterializedScoreSearch.search a tail programs
        ((M:ℚ)/((r:ℚ)*(lam:ℚ)*(r^(2*Q):ℕ))) ((n:ℚ)/(2*(r:ℚ))) offset N).value := by
  exact SemiprimeSourceScoreChoice.assign_refines a tail
    (SemiprimeSourceScoreCountBits.score (SemiprimeSourceScoreWeightAcquisition.acquire M n r Q lam)
      a tail programs)
    (SemiprimeMaterializedScoreSearch.sequential a tail programs
      ((M:ℚ)/((r:ℚ)*(lam:ℚ)*(r^(2*Q):ℕ))) ((n:ℚ)/(2*(r:ℚ))) offset)
    (fun s xs => SemiprimeSourceScoreCountBits.score_valid _ a tail programs s xs)
    (fun s xs v w => score_order M n lam a tail programs offset s s (v::xs) (w::xs) hr hlam hcard) N []

/-- Original source descriptor construction is executed before the physical search. -/
def computedList {I V E : Type} [DecidableEq V] [DecidableEq E] {r Q : ℕ}
    (owner : I → V) (factor : I → E) (M n lam : ℕ) (a : Word r Q) (tail : List (Word r Q))
    (terms : List (OAI.Algorithms.SubexponentialSAT.SqrtLog.Packing.ScoreTerm I V Q))
    (indices : List (V⊕E)) : Run (List (Word r Q)) :=
  let compiled := SemiprimeMaterializedSourceWords.compileAll owner factor indices terms
  let out := run M n lam a tail compiled.value indices.length
  ⟨out.value,compiled.work+out.work+1⟩

/-- No score-program oracle remains at this original descriptor-list entry point. -/
theorem computedList_refines {I V E : Type} [DecidableEq V] [DecidableEq E] {r Q : ℕ}
    (owner : I → V) (factor : I → E) (M n lam : ℕ) (a : Word r Q) (tail : List (Word r Q))
    (terms : List (OAI.Algorithms.SubexponentialSAT.SqrtLog.Packing.ScoreTerm I V Q))
    (indices : List (V⊕E)) (offset : ℚ) (hr : 0 < r) (hlam : 0 < lam)
    (hcard : (a::tail).length^4=(r^(2*Q))^2) :
    (computedList owner factor M n lam a tail terms indices).value=
      (SemiprimeMaterializedSourceWords.computedList owner factor a tail terms indices
        ((M:ℚ)/((r:ℚ)*(lam:ℚ)*(r^(2*Q):ℕ))) ((n:ℚ)/(2*(r:ℚ))) offset).value := by
  exact run_refines M n lam a tail _ indices.length offset hr hlam hcard

end RiemannGaussian.SemiprimeSourceScorePhysicalSearch
