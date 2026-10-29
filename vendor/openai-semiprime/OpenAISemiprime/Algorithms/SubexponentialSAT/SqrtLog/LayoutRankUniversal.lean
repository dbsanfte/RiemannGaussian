import OpenAISemiprime.Algorithms.SubexponentialSAT.LeanCompat
import OpenAISemiprime.Algorithms.SubexponentialSAT.SqrtLog.LayoutRankBlocks
import OpenAISemiprime.Algorithms.SubexponentialSAT.SqrtLog.LayoutUniversal

namespace OAI.Algorithms

/-! The actual universal spectral bound, summed once over all heads. -/

namespace SubexponentialSAT.SqrtLog.LayoutRank

open scoped BigOperators
open Module Matrix
open SubexponentialSAT.MulticolorTypes LayoutScaledMatrices

variable {r Q : ℕ}

theorem universal_constraints_rank_le (A R : ℕ) (t : Fin Q) (g : Fin r) :
    rowRank (LayoutUniversal.constraints A R t g) ≤
      finrank ℚ (LinearMap.range (LayoutNumerator.rationalDefect (0 : Fin 1) t g A R).mulVecLin) := by
  calc
    _ ≤ rowRank (clearedDefect (LayoutNumerator.denominator R)
        (LayoutNumerator.joint (0 : Fin 1) t g A R)) := rowRank_pullback_le _ _
    _ = _ := by
      change rowRank (fun i j =>
        (clearedDefect (LayoutNumerator.denominator R)
          (LayoutNumerator.joint (0 : Fin 1) t g A R)) i j) = _
      rw [rowRank_eq_matrix_rank]
      rfl

theorem universal_centered_rank_relative (R : ℕ) (t : Fin Q) (g : Fin r)
    (ε : ℚ) (hr : 2 ≤ r) (hQ : 2 ≤ Q) (hR : 4 ≤ R) (hsize : 4 * R ≤ Q)
    (hε : 0 < ε)
    (hwidth : 32 * ((Q - 1 : ℕ) : ℝ) * Real.log (2 / (ε : ℝ)) ≤ (R : ℝ) ^ 2) :
    (rowRank (LayoutUniversal.constraints
      (SubexponentialSAT.Subexp.TailInterval.intervalStart r Q R) R t g) : ℚ) ≤
        ε * Fintype.card (Joint t g (0 : Fin 1)) := by
  exact le_trans (by exact_mod_cast (universal_constraints_rank_le
    (SubexponentialSAT.Subexp.TailInterval.intervalStart r Q R) R t g))
      (LayoutNumerator.centered_rationalDefect_rank_relative t g 0 R ε
        hr hQ hR hsize hε hwidth)

variable {O : Type*} [CommRing O] {node : Fin Q → O}

theorem universal_data_rank_eq (A R : ℕ) (denom : Oˣ)
    (hdenom : (denom : O) = (LayoutNumerator.denominator R : O))
    (units : SubexponentialSAT.SubexpRowInterpolation.NodeUnits node) (t : Fin Q) (g : Fin r) :
    rowRank ((LayoutUniversal.data A R denom hdenom units).constraints t g) =
      rowRank (LayoutUniversal.constraints A R t g) := by
  change rowRank (fun j => LayoutUniversal.constraints A R t g
    ((Fintype.equivFin (Joint t g (0 : Fin 1))).symm j)) = _
  exact rowRank_reindex _ _ (Equiv.surjective _)

/-- The sum over heads costs one ambient universal block, not r blocks. -/
theorem universal_total_rank_le (R : ℕ) (denom : Oˣ)
    (hdenom : (denom : O) = (LayoutNumerator.denominator R : O))
    (units : SubexponentialSAT.SubexpRowInterpolation.NodeUnits node) (t : Fin Q)
    (ε : ℚ) (hr : 2 ≤ r) (hQ : 2 ≤ Q) (hR : 4 ≤ R) (hsize : 4 * R ≤ Q)
    (hε : 0 < ε)
    (hwidth : 32 * ((Q - 1 : ℕ) : ℝ) * Real.log (2 / (ε : ℝ)) ≤ (R : ℝ) ^ 2) :
    (∑ g : Fin r, (rowRank ((LayoutUniversal.data (r := r)
      (SubexponentialSAT.Subexp.TailInterval.intervalStart r Q R) R denom hdenom units).constraints t g) : ℚ)) ≤
        ε * Fintype.card (UniversalType r Q 1) := by
  simp_rw [universal_data_rank_eq]
  calc
    _ ≤ ∑ g : Fin r, ε * (Fintype.card (Joint t g (0 : Fin 1)) : ℚ) := by
      apply Finset.sum_le_sum
      intro g _
      exact universal_centered_rank_relative R t g ε hr hQ hR hsize hε hwidth
    _ = ε * ∑ g : Fin r, (Fintype.card (Joint t g (0 : Fin 1)) : ℚ) := by
      rw [Finset.mul_sum]
    _ ≤ _ := mul_le_mul_of_nonneg_left (by exact_mod_cast sum_card_joint_le t (0 : Fin 1)) hε.le

variable {I V F : Type*} [Fintype I] [DecidableEq I] [Fintype V] [DecidableEq V]
variable {b R : ℕ} {label : I → UniversalType r Q 1}

/-- The concrete universal blocks, uncovered-coordinate rows, and literal
head-preserving incidence pullback together have total rank at most 2εM. -/
theorem actual_pulled_blocks_total_rank_le
    (denom : Oˣ) (hdenom : (denom : O) = (LayoutNumerator.denominator R : O))
    (units : SubexponentialSAT.SubexpRowInterpolation.NodeUnits node)
    (P : SubexponentialSAT.BlockPacking.CompleteBlocks label b) (factor : I → F)
    (color : F → Fin Q → Fin r)
    (hcolor : ∀ i t, (label i).slot 0 t = color (factor i) t)
    (owner : I → V) (head : Fin Q → V → Fin r)
    (hhead : ∀ t i, (label i).head t = head t (owner i))
    (t : Fin Q) (ε : ℚ) (hr : 2 ≤ r) (hQ : 2 ≤ Q) (hR : 4 ≤ R) (hsize : 4 * R ≤ Q)
    (hε : 0 < ε)
    (hwidth : 32 * ((Q - 1 : ℕ) : ℝ) * Real.log (2 / (ε : ℝ)) ≤ (R : ℝ) ^ 2)
    (hcover : (1 - ε) * (Fintype.card I : ℚ) ≤ b * (Fintype.card (UniversalType r Q 1) : ℚ)) :
    let C := LayoutUniversal.data (SubexponentialSAT.Subexp.TailInterval.intervalStart r Q R) R denom hdenom units
    let B := LayoutBlocks.data C P factor color hcolor
    (∑ g, (rowRank ((LayoutHeadPullback.pullback owner factor head B hhead).constraints t g) : ℚ)) ≤
      2 * ε * Fintype.card I := by
  dsimp only
  apply pulled_blocks_total_rank_le
    (LayoutUniversal.data (r := r) (SubexponentialSAT.Subexp.TailInterval.intervalStart r Q R)
      R denom hdenom units) P factor color hcolor owner head hhead t ε hε.le
  · exact universal_total_rank_le R denom hdenom units t ε hr hQ hR hsize hε hwidth
  · exact hcover

end SubexponentialSAT.SqrtLog.LayoutRank

end OAI.Algorithms
