/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeSourceWordIdCounts
import RiemannGaussian.SemiprimeSourceWordIdCountsBudget

/-! # Structural output bounds of the actual physical-ID score callback
These require only actual array sizes, never unknown count values or Fits.
-/
set_option autoImplicit false
namespace RiemannGaussian.SemiprimeSourceWordIdCountsBounds
open SemiprimeRationalBits SemiprimeSourceWordBank SemiprimeSourceScoreWeightBits
open SemiprimeMaterializedScoreEnvironment (ScoreProgram)

/-- One original-list-size bound covers both physical count lanes. -/
def laneWidth (L T : ℕ) : ℕ := 3+8*L+L^4+T

/-- Actual sequential counts have structurally bounded physical arrays. -/
theorem sequential_length {Q : ℕ} (bank : Bank) (defaultID : List Bool)
    (programs : List (ScoreProgram Q)) (n : ℕ) (fixedIDs : List (List Bool))
    (hL : 0< bank.ids.length) :
    (SemiprimeSourceWordIdCounts.sequential bank defaultID programs n fixedIDs).incidence.length≤
      laneWidth bank.ids.length programs.length ∧
    (SemiprimeSourceWordIdCounts.sequential bank defaultID programs n fixedIDs).head.length≤
      laneWidth bank.ids.length programs.length := by
  have h:=SemiprimeSourceWordIdCountsBudget.evaluate_length bank.ids SemiprimeSourceWordIdEnvironment.extend
    (fun p env => SemiprimeSourceWordIdPredicate.terminal bank env p) programs
    (List.range' fixedIDs.length n) (SemiprimeSourceWordIdEnvironment.initial defaultID fixedIDs).value
    hL List.nodup_range'
  exact h

/-- Actual weight and lane widths before the two final multipliers and adder. -/
def operandWidth (L T K : ℕ) : ℕ := K+laneWidth L T

/-- Physical output width derives from the acquired words and circuit structure. -/
theorem score_width {Q : ℕ} (bank : Bank) (weights : Weights) (defaultID : List Bool)
    (programs : List (ScoreProgram Q)) (n : ℕ) (fixedIDs : List (List Bool)) (K : ℕ)
    (hL : 0< bank.ids.length) (ha : weights.incidence.length≤ K) (hb : weights.head.length≤ K) :
    Width (SemiprimeSourceWordIdCounts.score bank weights defaultID programs n fixedIDs).word
      (3*operandWidth bank.ids.length programs.length K+1) := by
  have hl:=sequential_length bank defaultID programs n fixedIDs hL
  have h:=combine_length weights
    (SemiprimeSourceWordIdCounts.sequential bank defaultID programs n fixedIDs).incidence
    (SemiprimeSourceWordIdCounts.sequential bank defaultID programs n fixedIDs).head
    (operandWidth bank.ids.length programs.length K)
    (ha.trans (by unfold operandWidth;omega)) (hb.trans (by unfold operandWidth;omega))
    (hl.1.trans (by unfold operandWidth;omega)) (hl.2.trans (by unfold operandWidth;omega))
  exact ⟨h,by change 1≤3*operandWidth bank.ids.length programs.length K+1;omega⟩

/-- Every actual acquired positive-r bank supplies the needed nonempty-menu fact. -/
theorem acquired_ids_pos (r Q : ℕ) [NeZero r] : 0<(acquire r Q).ids.length := by
  have h:=SemiprimeSourceWordBankIndexed.ids_nonempty r Q
  exact List.length_pos_iff.mpr h

end RiemannGaussian.SemiprimeSourceWordIdCountsBounds
