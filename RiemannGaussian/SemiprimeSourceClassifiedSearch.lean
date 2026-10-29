/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeSourceClassifiedCounts
import RiemannGaussian.SemiprimeSourceClassifiedWeights
import RiemannGaussian.SemiprimeSourceWordIdSearch

/-! # Original indexed source search without local completion enumeration
The bank, collision powers and weights are acquired once. Every score uses
actual physical classifiers and cached powers; no unary count padding or
universal-cardinality initializer is executed by this search.
-/
set_option autoImplicit false
set_option maxHeartbeats 1800000
namespace RiemannGaussian.SemiprimeSourceClassifiedSearch
open SemiprimeRationalBits SemiprimeMaterializedWords
open SemiprimeSourceWordBank SemiprimeSourceWordBankSemantics
open SemiprimeSourceWordIdControl
open SemiprimeMaterializedScoreEnvironment (ScoreProgram)
open SemiprimeSourceIncidenceNamespaces (Separated)

/-- Different physical weight padding preserves exactly the original scalar score. -/
theorem score_value (M n r Q lam : ℕ) [NeZero r] (programs : List (ScoreProgram Q))
    (s : ℕ) (fixed : List (List Bool)) (hf : InMenu (acquire r Q).ids fixed)
    (hp : ∀ p∈programs,Separated p) :
    (SemiprimeSourceClassifiedCounts.score (acquire r Q) (SemiprimeSourceCountPowers.acquire r Q)
      (SemiprimeSourceClassifiedWeights.acquire M n lam (SemiprimeSourceCountPowers.acquire r Q))
      defaultID programs s fixed).word.value=
      (SemiprimeSourceWordIdCounts.score (acquire r Q)
        (SemiprimeSourceScoreWeightAcquisition.acquire M n r Q lam) defaultID programs s fixed).word.value := by
  have hh := SemiprimeSourceClassifiedCounts.score_eq r Q
    (SemiprimeSourceClassifiedWeights.acquire M n lam (SemiprimeSourceCountPowers.acquire r Q))
    defaultID programs s fixed (SemiprimeSourceWordBankIndexed.default_mem r Q) hf hp
  apply hh.trans
  have hw := SemiprimeSourceClassifiedWeights.acquire_old_value M n r Q lam
  change (SemiprimeSourceScoreWeightBits.scoreWord _
    (SemiprimeSourceWordIdCounts.sequential (acquire r Q) defaultID programs s fixed).incidence
    (SemiprimeSourceWordIdCounts.sequential (acquire r Q) defaultID programs s fixed).head).value=
    (SemiprimeSourceScoreWeightBits.scoreWord _
    (SemiprimeSourceWordIdCounts.sequential (acquire r Q) defaultID programs s fixed).incidence
    (SemiprimeSourceWordIdCounts.sequential (acquire r Q) defaultID programs s fixed).head).value
  rw [SemiprimeSourceScoreWeightBits.scoreWord_value,SemiprimeSourceScoreWeightBits.scoreWord_value,hw.1,hw.2]

/-- The concrete classified callback inherits exact original ordering and all ties. -/
theorem score_order (M n F r Q lam : ℕ) [NeZero r] (arity : Fin F → ℕ)
    (programs : List (ScoreProgram Q)) (offset : ℚ) (s : ℕ)
    (fixed : List (List Bool)) (v w : List Bool)
    (hf : InMenu (acquire r Q).ids fixed) (hv : v∈(acquire r Q).ids) (hw : w∈(acquire r Q).ids)
    (hp : ∀ p∈programs,Separated p) (hlam : 0 < lam) :
    let en := (SemiprimePaidFiniteEnumerations.indexed n F r Q arity).value
    let powers := SemiprimeSourceCountPowers.acquire r Q
    let weights := SemiprimeSourceClassifiedWeights.acquire M n lam powers
    (SemiprimeSourceClassifiedCounts.score (acquire r Q) powers weights defaultID programs s (v::fixed)).word.value ≤
      (SemiprimeSourceClassifiedCounts.score (acquire r Q) powers weights defaultID programs s (w::fixed)).word.value ↔
      (SemiprimeMaterializedScoreSearch.sequential en.wordFirst en.wordTail programs
        ((M:ℚ)/((r:ℚ)*(lam:ℚ)*(r^(2*Q):ℕ))) ((n:ℚ)/(2*(r:ℚ))) offset s
        (decode r Q v::fixed.map (decode r Q))).value ≤
      (SemiprimeMaterializedScoreSearch.sequential en.wordFirst en.wordTail programs
        ((M:ℚ)/((r:ℚ)*(lam:ℚ)*(r^(2*Q):ℕ))) ((n:ℚ)/(2*(r:ℚ))) offset s
        (decode r Q w::fixed.map (decode r Q))).value := by
  dsimp only
  rw [score_value M n r Q lam programs s (v::fixed) (inMenu_cons _ fixed v hv hf) hp,
    score_value M n r Q lam programs s (w::fixed) (inMenu_cons _ fixed w hw hf) hp]
  exact SemiprimeSourceWordIdSearch.score_order M n F r Q lam arity programs offset s fixed v w hf hv hw hlam

/-- Acquire only bank/powers/original magnitudes, then execute the existing ID controller. -/
def run (M n r Q lam : ℕ) (programs : List (ScoreProgram Q)) (N : ℕ) : Run (List (List Bool)) :=
  let bank := acquire r Q
  let powers := SemiprimeSourceCountPowers.acquire r Q
  let weights := SemiprimeSourceClassifiedWeights.acquire M n lam powers
  let result := SemiprimeSourceChoiceBits.run defaultID (SemiprimeSourceWordIdMenu.tail bank)
    (fun tokens fixed => SemiprimeSourceClassifiedCounts.score bank powers weights
      defaultID programs tokens.length fixed) N []
  ⟨result.value,bank.clock+powers.clock+weights.clock+result.work+bank.ids.length+7⟩

/-- Every returned selected ID still belongs to the actually acquired menu. -/
theorem run_valid (M n r Q lam : ℕ) [NeZero r] (programs : List (ScoreProgram Q)) (N : ℕ) :
    InMenu (acquire r Q).ids (run M n r Q lam programs N).value := by
  have hc := SemiprimeSourceWordIdMenu.candidates_valid r Q
  rw [SemiprimeSourceWordIdMenu.first_eq_default] at hc
  exact assign_inMenu (acquire r Q).ids defaultID (SemiprimeSourceWordIdMenu.tail (acquire r Q))
    _ _ [] hc (by simp [InMenu])

/-- The actual optimized result is the exact original indexed scalar search. -/
theorem run_refines (M n F r Q lam : ℕ) [NeZero r] (arity : Fin F → ℕ)
    (programs : List (ScoreProgram Q)) (N : ℕ) (offset : ℚ)
    (hp : ∀ p∈programs,Separated p) (hlam : 0 < lam) :
    let en := (SemiprimePaidFiniteEnumerations.indexed n F r Q arity).value
    (run M n r Q lam programs N).value.map (decode r Q)=
      (SemiprimeMaterializedScoreSearch.search en.wordFirst en.wordTail programs
        ((M:ℚ)/((r:ℚ)*(lam:ℚ)*(r^(2*Q):ℕ))) ((n:ℚ)/(2*(r:ℚ))) offset N).value := by
  let en := (SemiprimePaidFiniteEnumerations.indexed n F r Q arity).value
  have hc := SemiprimeSourceWordIdMenu.candidates_valid r Q
  rw [SemiprimeSourceWordIdMenu.first_eq_default] at hc
  have hh := run_decode (acquire r Q).ids (decode r Q) defaultID
    (SemiprimeSourceWordIdMenu.tail (acquire r Q))
    (fun ts fixed => SemiprimeSourceClassifiedCounts.score (acquire r Q)
      (SemiprimeSourceCountPowers.acquire r Q)
      (SemiprimeSourceClassifiedWeights.acquire M n lam (SemiprimeSourceCountPowers.acquire r Q))
      defaultID programs ts.length fixed)
    (SemiprimeMaterializedScoreSearch.sequential en.wordFirst en.wordTail programs
      ((M:ℚ)/((r:ℚ)*(lam:ℚ)*(r^(2*Q):ℕ))) ((n:ℚ)/(2*(r:ℚ))) offset)
    (fun ts xs _ => SemiprimeSourceClassifiedCounts.score_valid _ _ _ _ programs ts.length xs)
    (fun ts xs hf v hv w hw => score_order M n F r Q lam arity programs offset ts.length xs v w hf hv hw hp hlam)
    N [] hc (by simp [InMenu])
  have hd : decode r Q defaultID=en.wordFirst := by
    exact (congrArg (decode r Q) (SemiprimeSourceWordIdMenu.first_eq_default r Q)).symm.trans
      (SemiprimeSourceWordIdMenu.first_decode n F r Q arity)
  rw [hd,SemiprimeSourceWordIdMenu.tail_decode n F r Q arity] at hh
  exact hh

end RiemannGaussian.SemiprimeSourceClassifiedSearch
