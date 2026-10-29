/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeSourceWordIdCounts
import RiemannGaussian.SemiprimeSourceWordIdMenu
import RiemannGaussian.SemiprimeSourceScorePhysicalSearch

/-! # Executed acquired-bank source search returning physical candidate IDs
All candidate/prefix payloads are Boolean IDs. The actual bank, ID environment,
terminal and counter pipeline supplies every score. Original Word functions and
decoders occur only in proofs relating the result to the indexed source order.
-/
set_option autoImplicit false
set_option maxHeartbeats 1800000
namespace RiemannGaussian.SemiprimeSourceWordIdSearch
open SemiprimeRationalBits SemiprimeMaterializedWords
open SemiprimeSourceWordBank SemiprimeSourceWordBankSemantics
open SemiprimeSourceWordIdControl
open OAI.Algorithms.SubexponentialSAT.MulticolorTypes
open SemiprimeMaterializedScoreEnvironment (ScoreProgram)

/-- The concrete physical-ID callback has the same value as the verified old
physical score, interpreted on the original decoded prefix in the theorem only. -/
theorem score_value (M n F r Q lam : ℕ) [NeZero r] (arity : Fin F → ℕ)
    (programs : List (ScoreProgram Q)) (s : ℕ) (fixed : List (List Bool))
    (hf : InMenu (acquire r Q).ids fixed) :
    let en := (SemiprimePaidFiniteEnumerations.indexed n F r Q arity).value
    let weights := SemiprimeSourceScoreWeightAcquisition.acquire M n r Q lam
    (SemiprimeSourceWordIdCounts.score (acquire r Q) weights defaultID programs s fixed).word.value=
      (SemiprimeSourceScoreCountBits.score weights en.wordFirst en.wordTail programs s
        (fixed.map (decode r Q))).word.value := by
  dsimp only
  simp only [SemiprimeSourceScoreCountBits.score_value]
  exact SemiprimeSourceWordIdCounts.score_indexed n F r Q arity _ programs s fixed hf

/-- Every actual valid-menu prefix inherits the exact original score ordering. -/
theorem score_order (M n F r Q lam : ℕ) [NeZero r] (arity : Fin F → ℕ)
    (programs : List (ScoreProgram Q)) (offset : ℚ) (s : ℕ)
    (fixed : List (List Bool)) (v w : List Bool)
    (hf : InMenu (acquire r Q).ids fixed) (hv : v∈(acquire r Q).ids) (hw : w∈(acquire r Q).ids)
    (hlam : 0 < lam) :
    let en := (SemiprimePaidFiniteEnumerations.indexed n F r Q arity).value
    let weights := SemiprimeSourceScoreWeightAcquisition.acquire M n r Q lam
    (SemiprimeSourceWordIdCounts.score (acquire r Q) weights defaultID programs s (v::fixed)).word.value ≤
      (SemiprimeSourceWordIdCounts.score (acquire r Q) weights defaultID programs s (w::fixed)).word.value ↔
      (SemiprimeMaterializedScoreSearch.sequential en.wordFirst en.wordTail programs
        ((M:ℚ)/((r:ℚ)*(lam:ℚ)*(r^(2*Q):ℕ))) ((n:ℚ)/(2*(r:ℚ))) offset s
        (decode r Q v::fixed.map (decode r Q))).value ≤
      (SemiprimeMaterializedScoreSearch.sequential en.wordFirst en.wordTail programs
        ((M:ℚ)/((r:ℚ)*(lam:ℚ)*(r^(2*Q):ℕ))) ((n:ℚ)/(2*(r:ℚ))) offset s
        (decode r Q w::fixed.map (decode r Q))).value := by
  dsimp only
  rw [score_value M n F r Q lam arity programs s (v::fixed) (inMenu_cons _ fixed v hv hf),
    score_value M n F r Q lam arity programs s (w::fixed) (inMenu_cons _ fixed w hw hf)]
  have hcard := SemiprimeSourceScoreCountOrder.caller_cardinality
    (SemiprimePaidFiniteEnumerations.indexed n F r Q arity).value
  rw [SemiprimeSourceOffsetHeight.caller_universal_length] at hcard
  exact SemiprimeSourceScorePhysicalSearch.score_order M n lam _ _ programs offset s s _ _
    (NeZero.pos r) hlam hcard

/-- Acquire original rows/IDs and integer weights, then execute the existing
Boolean-ID controller with the concrete physical score callback. -/
def run (M n r Q lam : ℕ) (programs : List (ScoreProgram Q)) (N : ℕ) : Run (List (List Bool)) :=
  let bank := acquire r Q
  let weights := SemiprimeSourceScoreWeightAcquisition.acquire M n r Q lam
  let result := SemiprimeSourceChoiceBits.run defaultID (SemiprimeSourceWordIdMenu.tail bank)
    (fun tokens fixed => SemiprimeSourceWordIdCounts.score bank weights defaultID programs tokens.length fixed) N []
  ⟨result.value,bank.clock+weights.clock+result.work+bank.ids.length+5⟩

/-- Every physically selected output ID is an actual acquired menu entry. -/
theorem run_valid (M n r Q lam : ℕ) [NeZero r] (programs : List (ScoreProgram Q)) (N : ℕ) :
    InMenu (acquire r Q).ids (run M n r Q lam programs N).value := by
  have hc := SemiprimeSourceWordIdMenu.candidates_valid r Q
  rw [SemiprimeSourceWordIdMenu.first_eq_default] at hc
  exact assign_inMenu (acquire r Q).ids defaultID (SemiprimeSourceWordIdMenu.tail (acquire r Q))
    _ _ [] hc (by simp [InMenu])

/-- The actual physical-ID result decodes to the EXACT old indexed source labels.
There is no supplied menu, score, count, truth or Word-function runtime argument. -/
theorem run_refines (M n F r Q lam : ℕ) [NeZero r] (arity : Fin F → ℕ)
    (programs : List (ScoreProgram Q)) (N : ℕ) (offset : ℚ) (hlam : 0 < lam) :
    let en := (SemiprimePaidFiniteEnumerations.indexed n F r Q arity).value
    (run M n r Q lam programs N).value.map (decode r Q)=
      (SemiprimeMaterializedScoreSearch.search en.wordFirst en.wordTail programs
        ((M:ℚ)/((r:ℚ)*(lam:ℚ)*(r^(2*Q):ℕ))) ((n:ℚ)/(2*(r:ℚ))) offset N).value := by
  let en := (SemiprimePaidFiniteEnumerations.indexed n F r Q arity).value
  have hc := SemiprimeSourceWordIdMenu.candidates_valid r Q
  rw [SemiprimeSourceWordIdMenu.first_eq_default] at hc
  have hh := run_decode (acquire r Q).ids (decode r Q) defaultID
    (SemiprimeSourceWordIdMenu.tail (acquire r Q))
    (fun ts fixed => SemiprimeSourceWordIdCounts.score (acquire r Q)
      (SemiprimeSourceScoreWeightAcquisition.acquire M n r Q lam) defaultID programs ts.length fixed)
    (SemiprimeMaterializedScoreSearch.sequential en.wordFirst en.wordTail programs
      ((M:ℚ)/((r:ℚ)*(lam:ℚ)*(r^(2*Q):ℕ))) ((n:ℚ)/(2*(r:ℚ))) offset)
    (fun ts xs _ => SemiprimeSourceWordIdCounts.score_valid _ _ _ programs ts.length xs)
    (fun ts xs hf v hv w hw => score_order M n F r Q lam arity programs offset ts.length xs v w hf hv hw hlam)
    N [] hc (by simp [InMenu])
  have hd : decode r Q defaultID=en.wordFirst := by
    exact (congrArg (decode r Q) (SemiprimeSourceWordIdMenu.first_eq_default r Q)).symm.trans
      (SemiprimeSourceWordIdMenu.first_decode n F r Q arity)
  rw [hd,SemiprimeSourceWordIdMenu.tail_decode n F r Q arity] at hh
  exact hh

end RiemannGaussian.SemiprimeSourceWordIdSearch
