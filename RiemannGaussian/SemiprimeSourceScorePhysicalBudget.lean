/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeSourceScorePhysicalCaller
import RiemannGaussian.SemiprimeSourceScoreCountBitsBounds
import RiemannGaussian.SemiprimeSourceSearchState

/-! # Original-resource budget of physical integer-count label selection
Every terminal/count/weight/comparison report is retained. Original descriptor
and label metadata still have native scalar interfaces; this is not a completed
primitive-machine cost theorem for the whole public factorizer.
-/
set_option autoImplicit false
set_option maxHeartbeats 1400000
namespace RiemannGaussian.SemiprimeSourceScorePhysicalBudget
open SemiprimeRationalBits SemiprimeSourceScoreCountBitsBounds
open OAI.Algorithms.SubexponentialSAT.MulticolorTypes
open SemiprimeMaterializedScoreEnvironment SemiprimeReportPolynomialGrowth

/-- Actual acquired original weight width, not a semantic magnitude oracle. -/
def weightCap (M n lam U : ℕ) : ℕ :=
  SemiprimeSourceScoreWeightBits.weightWidth (SemiprimeSourceScoreWeightAcquisition.inputWidth M n lam U)
/-- Uniform physical score-word cap derived from original list and cached-weight sizes. -/
def wordCap (L T M n lam U : ℕ) : ℕ := 3*scoreOperandWidth L T (weightCap M n lam U)+1
/-- Actual weight acquisition and every candidate score/comparison/control step. -/
def runBudget (M n r Q lam U L T N : ℕ) : ℕ :=
  SemiprimeSourceScoreWeightAcquisition.acquisitionBudget M n r Q lam U+
    (N*((L-1)*(2*scoreBudget r Q N L T (weightCap M n lam U)+
      200*(wordCap L T M n lam U+1)^2+3)+4)+1)+2

/-- Exact runtime-derived physical producer bound on all reachable source prefixes. -/
theorem run_work {r Q : ℕ} (M n lam : ℕ) (a : Word r Q) (tail : List (Word r Q))
    (programs : List (ScoreProgram Q)) (N : ℕ) (hr : 0 < r)
    (hp : ∀ p∈programs,∀ i∈support p,i ≤ N) :
    (SemiprimeSourceScorePhysicalSearch.run M n lam a tail programs N).work ≤
      runBudget M n r Q lam (r^(2*Q)) (a::tail).length programs.length N := by
  let weights := SemiprimeSourceScoreWeightAcquisition.acquire M n r Q lam
  have hw := SemiprimeSourceScoreWeightAcquisition.acquire_length M n r Q lam
  have hcallback (s : ℕ) (fixed : List (Word r Q)) (hlen : s+fixed.length ≤ N) :
      (SemiprimeSourceScoreCountBits.score weights a tail programs s fixed).clock ≤
          scoreBudget r Q N (a::tail).length programs.length (weightCap M n lam (r^(2*Q))) ∧
        Width (SemiprimeSourceScoreCountBits.score weights a tail programs s fixed).word
          (wordCap (a::tail).length programs.length M n lam (r^(2*Q))) := by
    exact ⟨score_clock weights a tail programs s fixed N _ (by omega) hp hw.1 hw.2,
      score_width weights a tail programs s fixed _ hw.1 hw.2⟩
  have hs := SemiprimeSourceScoreChoice.assign_work a tail
    (SemiprimeSourceScoreCountBits.score weights a tail programs)
    (scoreBudget r Q N (a::tail).length programs.length (weightCap M n lam (r^(2*Q))))
    (wordCap (a::tail).length programs.length M n lam (r^(2*Q))) N hcallback N [] (by simp)
  have ha := SemiprimeSourceScoreWeightAcquisition.acquire_clock M n r Q lam hr
  exact Nat.add_le_add_right (Nat.add_le_add ha hs) 2

/-- Actual descriptor generation plus the full acquired physical search. -/
def computedBudget (M n r Q lam U L T N : ℕ) : ℕ :=
  T*(8*N+15)+1+runBudget M n r Q lam U L T N+1

/-- The original finite enumeration supplies every descriptor ID bound internally. -/
theorem computed_work {I E : Type} [DecidableEq E] {n r Q : ℕ} [NeZero r]
    (owner : I → Fin n) (factor : I → E)
    (en : SemiprimeSourceLayout.Enumerations I (Fin n) E r Q) (lam : ℕ) :
    (SemiprimeSourceScorePhysicalCaller.computed owner factor en lam).work ≤
      computedBudget en.incidences.values.length n r Q lam en.types.values.length
        (en.wordFirst::en.wordTail).length en.terms.values.length en.indices.values.length := by
  have hp : ∀ p∈(SemiprimeMaterializedSourceWords.compileAll owner factor en.indices.values en.terms.values).value,
      ∀ i∈support p,i ≤ en.indices.values.length := by
    intro p hpm i hi
    exact (SemiprimeSourceSearchState.compileAll_support_lt owner factor en.indices en.terms.values p hpm i hi).le
  have hs := run_work en.incidences.values.length n lam en.wordFirst en.wordTail
    (SemiprimeMaterializedSourceWords.compileAll owner factor en.indices.values en.terms.values).value
    en.indices.values.length (NeZero.pos r) hp
  rw [SemiprimeSourceSearchState.compileAll_length] at hs
  have hc := SemiprimeMaterializedSourceWords.compileAll_work owner factor en.indices.values en.terms.values
  rw [SemiprimeSourceOffsetHeight.caller_universal_length]
  exact Nat.add_le_add_right (Nat.add_le_add hc hs) 1

end RiemannGaussian.SemiprimeSourceScorePhysicalBudget
