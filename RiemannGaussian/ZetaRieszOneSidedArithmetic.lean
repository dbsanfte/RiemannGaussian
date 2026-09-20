/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaRieszReflectedLinear

/-!
# An independent one-sided estimate for the actual remaining arithmetic sum

The reflected linear class is evaluated with its exact parity and cosine.
Only its negative real observations are charged. The complementary labels
retain the proved antichain allowance. The resulting explicit arithmetic
budget bounds the actual nondominant remainder without zero hypotheses.
Bounding this budget by 3/40 on a cofinal sequence remains open.
-/

namespace RiemannGaussian.ZetaRieszOneSidedArithmetic
noncomputable section
open scoped BigOperators Classical
open ZetaRieszReflectedLinear ZetaRieszJointAllocation ZetaRieszDominantAllocation
open ZetaRieszSperner ZetaRieszCosineCarrier ZetaRieszPrimeCountFrequency

/-- The original nonnegative factorial envelope, without discarding the cosine. -/
def amplitude (N n : ℕ) : ℝ :=
  Real.exp (-(3 / 2 : ℝ) * Real.log n) * (Real.log n) ^ N / N.factorial

/-- The original unassigned fraction multiplies the unchanged factorial envelope. -/
def weight (A : Finset ℕ) (N n : ℕ) : ℝ :=
  (1 - boundedShare A N n) * amplitude N n

/-- Every literal unassigned weight is nonnegative, with no support premise. -/
theorem weight_nonneg (A : Finset ℕ) (N n : ℕ) : 0 ≤ weight A N n :=
  mul_nonneg (sub_nonneg.mpr (boundedShare_bounds A N n).2)
    (factorial_envelope_nonneg N n)

/-- Evaluated arithmetic signs charge only adverse phases; other labels use the antichain bound. -/
def phaseCost (L y : ℝ) (n : ℕ) : ℝ :=
  if LinearClass L n then max 0 (-linearCoefficient L n * Real.cos (y * Real.log n))
  else middleLayerAllowance L n * |Real.cos (y * Real.log n)|

/-- The one-sided cost is a nonnegative, completely explicit finite arithmetic quantity. -/
theorem phaseCost_nonneg {L : ℝ} (hL : 0 < L) (y : ℝ) (n : ℕ) :
    0 ≤ phaseCost L y n := by
  unfold phaseCost
  split_ifs
  · exact le_max_left _ _
  · exact mul_nonneg (middleLayerAllowance_nonneg hL n) (abs_nonneg _)

/-- The new one-sided allowance never exceeds the existing absolute antichain cost. -/
theorem phaseCost_le_antichain {L : ℝ} (hL : 0 < L) (y : ℝ) (n : ℕ) :
    phaseCost L y n ≤ middleLayerAllowance L n * |Real.cos (y * Real.log n)| := by
  unfold phaseCost
  split_ifs with hn
  · have hc := norm_coefficient_le_allowance hL n
    rw [coefficient_eq_linear hn, Complex.norm_real, Real.norm_eq_abs] at hc
    apply max_le (mul_nonneg (middleLayerAllowance_nonneg hL n) (abs_nonneg _))
    calc
      _ ≤ |linearCoefficient L n * Real.cos (y * Real.log n)| := by
        simpa only [neg_mul] using neg_le_abs (linearCoefficient L n * Real.cos (y * Real.log n))
      _ = |linearCoefficient L n| * |Real.cos (y * Real.log n)| := abs_mul _ _
      _ ≤ _ := mul_le_mul_of_nonneg_right hc (abs_nonneg _)
  · rfl

/-- An arithmetically aligned phase has exactly zero lower-bound cost. -/
theorem phaseCost_eq_zero_of_aligned {L y : ℝ} {n : ℕ} (hn : LinearClass L n)
    (hphase : 0 ≤ linearCoefficient L n * Real.cos (y * Real.log n)) :
    phaseCost L y n = 0 := by
  rw [phaseCost, if_pos hn, max_eq_left (by nlinarith)]

/-- Below the four-prime radial sign change, all nonpositive cosines are free in the lower bound. -/
theorem four_phaseCost_zero_below {L y : ℝ} {n : ℕ} (hL : 0 < L)
    (hn : LinearClass L n) (hk : n.primeFactors.card = 4)
    (hrad : 2 * Real.log n ≤ 3 * L) (hcos : Real.cos (y * Real.log n) ≤ 0) :
    phaseCost L y n = 0 := by
  apply phaseCost_eq_zero_of_aligned hn
  rw [linearCoefficient_four hn hk]
  exact mul_nonneg_of_nonpos_of_nonpos
    (mul_nonpos_of_nonneg_of_nonpos (div_nonneg (Real.log_natCast_nonneg n) hL.le)
      (sub_nonpos.mpr hrad)) hcos

/-- Above the four-prime radial sign change, all nonnegative cosines are free in the lower bound. -/
theorem four_phaseCost_zero_above {L y : ℝ} {n : ℕ} (hL : 0 < L)
    (hn : LinearClass L n) (hk : n.primeFactors.card = 4)
    (hrad : 3 * L ≤ 2 * Real.log n) (hcos : 0 ≤ Real.cos (y * Real.log n)) :
    phaseCost L y n = 0 := by
  apply phaseCost_eq_zero_of_aligned hn
  rw [linearCoefficient_four hn hk]
  exact mul_nonneg (mul_nonneg (div_nonneg (Real.log_natCast_nonneg n) hL.le)
    (sub_nonneg.mpr hrad)) hcos

/-- In the explicit central four-prime window the one-sided cost is at most one quarter of the old antichain allowance, for every phase. -/
theorem four_phaseCost_le_quarter {L : ℝ} (hL : 0 < L) (y : ℝ) {n : ℕ}
    (hn : LinearClass L n) (hk : n.primeFactors.card = 4)
    (hlo : (15 / 8 : ℝ) * Real.log n ≤ 3 * L)
    (hhi : 3 * L ≤ (17 / 8 : ℝ) * Real.log n) :
    phaseCost L y n ≤ (1 / 4 : ℝ) *
      (middleLayerAllowance L n * |Real.cos (y * Real.log n)|) := by
  have ht : 0 ≤ Real.log n / L := div_nonneg (Real.log_natCast_nonneg n) hL.le
  have hgap : |2 * Real.log n - 3 * L| ≤ Real.log n / 8 := by
    rw [abs_le]
    constructor <;> linarith
  have hA : |linearCoefficient L n| ≤ (1 / 4 : ℝ) * middleLayerAllowance L n := by
    rw [linearCoefficient_four hn hk, abs_mul, abs_of_nonneg ht]
    apply (mul_le_mul_of_nonneg_left hgap ht).trans_eq
    rw [middleLayerAllowance, if_pos ⟨hn.1, by omega⟩, hk]
    norm_num
    ring
  rw [phaseCost, if_pos hn]
  apply max_le (by positivity [middleLayerAllowance_nonneg hL n])
  calc
    _ ≤ |linearCoefficient L n * Real.cos (y * Real.log n)| := by
      simpa only [neg_mul] using neg_le_abs (linearCoefficient L n * Real.cos (y * Real.log n))
    _ = |linearCoefficient L n| * |Real.cos (y * Real.log n)| := abs_mul _ _
    _ ≤ _ := (mul_le_mul_of_nonneg_right hA (abs_nonneg _)).trans_eq (by ring)

/-- An independent one-sided estimate for every original real coefficient and product phase. -/
theorem coefficient_phase_lower {L : ℝ} (hL : 0 < L) (y : ℝ) (n : ℕ) :
    -phaseCost L y n ≤
      (SquarefreeVaughanLogSource.coefficient L n).re * Real.cos (y * Real.log n) := by
  unfold phaseCost
  split_ifs with hn
  · rw [coefficient_eq_linear hn, Complex.ofReal_re]
    have h := le_max_right 0 (-linearCoefficient L n * Real.cos (y * Real.log n))
    linarith
  · have hc := (Complex.abs_re_le_norm (SquarefreeVaughanLogSource.coefficient L n)).trans
      (norm_coefficient_le_allowance hL n)
    have h : |(SquarefreeVaughanLogSource.coefficient L n).re * Real.cos (y * Real.log n)| ≤
        middleLayerAllowance L n * |Real.cos (y * Real.log n)| := by
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_right hc (abs_nonneg _)
    exact (abs_le.mp h).1

/-- The exact retained atom has its original arithmetic sign, product phase and unassigned weight. -/
theorem re_residual_atom (A : Finset ℕ) (L y : ℝ) (N n : ℕ) :
    (residualCoefficient A L N n * zetaPrimeLogKernel N (3 / 2 + Complex.I * y) n).re =
      weight A N n *
        ((SquarefreeVaughanLogSource.coefficient L n).re * Real.cos (y * Real.log n)) := by
  rw [residualCoefficient, mul_assoc, Complex.mul_re, Complex.ofReal_re,
    Complex.ofReal_im, zero_mul, sub_zero, ← filter_one_eq,
    re_coefficient_filter_one]
  unfold weight amplitude
  ring

/-- The complete actual unassigned atom receives the arithmetic one-sided lower estimate. -/
theorem residual_atom_lower (A : Finset ℕ) {L : ℝ} (hL : 0 < L)
    (y : ℝ) (N n : ℕ) :
    -(weight A N n * phaseCost L y n) ≤
      (residualCoefficient A L N n * zetaPrimeLogKernel N (3 / 2 + Complex.I * y) n).re := by
  rw [re_residual_atom]
  simpa only [mul_neg] using mul_le_mul_of_nonneg_left
    (coefficient_phase_lower hL y n) (weight_nonneg A N n)

/-- The whole remaining finite signed sum has an independent lower bound, with every old mask retained. -/
theorem nondominantResponse_lower (u y : ℝ) (N K : ℕ) :
    -(∑ n ∈ nondominantBand u N K,
      weight (ZetaRieszAnnulusJoint.intermediatePrimes u N) N n *
        phaseCost (SquarefreeVaughanLogSource.length u N) y n) ≤
      (nondominantResponse u y N K).re := by
  rw [nondominantResponse, Complex.re_sum, ← Finset.sum_neg_distrib]
  exact Finset.sum_le_sum (fun n _ => residual_atom_lower _
    (SquarefreeVaughanLogSource.length_pos u N) y N n)

/-- The explicit source-normalized one-sided budget for the actual nondominant carrier. -/
def budget (u y : ℝ) (j : ℕ) : ℝ :=
  u ^ (dyadicMomentOrder j + 1) *
    ∑ n ∈ nondominantBand u (dyadicMomentOrder j) (dyadicPrimeCount j),
      weight (ZetaRieszAnnulusJoint.intermediatePrimes u (dyadicMomentOrder j))
        (dyadicMomentOrder j) n *
          phaseCost (SquarefreeVaughanLogSource.length u (dyadicMomentOrder j)) y n

/-- The complete one-sided arithmetic budget is nonnegative at every admissible source radius. -/
theorem budget_nonneg {u : ℝ} (hu : 0 ≤ u) (y : ℝ) (j : ℕ) : 0 ≤ budget u y j := by
  apply mul_nonneg (pow_nonneg hu _)
  apply Finset.sum_nonneg
  intro n _
  exact mul_nonneg (weight_nonneg _ _ n)
    (phaseCost_nonneg (SquarefreeVaughanLogSource.length_pos _ _) y n)

/-- The requested independent one-sided real estimate, for the actual source-normalized sum and every height. -/
theorem nondominantRemainder_lower {u : ℝ} (hu : 0 ≤ u) (y : ℝ) (j : ℕ) :
    -budget u y j ≤ (nondominantRemainder u y j).re := by
  rw [nondominantRemainder, ← Complex.ofReal_pow, Complex.mul_re,
    Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
  simpa only [budget, mul_neg] using mul_le_mul_of_nonneg_left
    (nondominantResponse_lower u y (dyadicMomentOrder j) (dyadicPrimeCount j))
    (pow_nonneg hu (dyadicMomentOrder j + 1))

/-- The whole new budget is at most the former antichain absolute allowance, at every actual order. -/
theorem budget_le_antichain {u : ℝ} (hu : 0 ≤ u) (y : ℝ) (j : ℕ) :
    budget u y j ≤ u ^ (dyadicMomentOrder j + 1) *
      ∑ n ∈ nondominantBand u (dyadicMomentOrder j) (dyadicPrimeCount j),
        weight (ZetaRieszAnnulusJoint.intermediatePrimes u (dyadicMomentOrder j))
          (dyadicMomentOrder j) n *
            (middleLayerAllowance (SquarefreeVaughanLogSource.length u (dyadicMomentOrder j)) n *
              |Real.cos (y * Real.log n)|) := by
  apply mul_le_mul_of_nonneg_left _ (pow_nonneg hu _)
  exact Finset.sum_le_sum (fun n _ => mul_le_mul_of_nonneg_left
    (phaseCost_le_antichain (SquarefreeVaughanLogSource.length_pos _ _) y n)
    (weight_nonneg _ _ n))

/-- The actual arithmetic and radial conditions under which at least three quarters of the old cost is removed. -/
def FourSavingClass (L : ℝ) (n : ℕ) : Prop :=
  LinearClass L n ∧ n.primeFactors.card = 4 ∧
    (15 / 8 : ℝ) * Real.log n ≤ 3 * L ∧ 3 * L ≤ (17 / 8 : ℝ) * Real.log n

/-- The previous antichain allowance on every original surviving label and phase. -/
def antichainBudget (u y : ℝ) (j : ℕ) : ℝ :=
  u ^ (dyadicMomentOrder j + 1) *
    ∑ n ∈ nondominantBand u (dyadicMomentOrder j) (dyadicPrimeCount j),
      weight (ZetaRieszAnnulusJoint.intermediatePrimes u (dyadicMomentOrder j))
        (dyadicMomentOrder j) n *
          (middleLayerAllowance (SquarefreeVaughanLogSource.length u (dyadicMomentOrder j)) n *
            |Real.cos (y * Real.log n)|)

/-- The old nonnegative charge on the explicitly evaluated four-prime subfamily, without any new support premise. -/
def fourCharge (u y : ℝ) (j : ℕ) : ℝ :=
  u ^ (dyadicMomentOrder j + 1) *
    ∑ n ∈ (nondominantBand u (dyadicMomentOrder j) (dyadicPrimeCount j)).filter
        (FourSavingClass (SquarefreeVaughanLogSource.length u (dyadicMomentOrder j))),
      weight (ZetaRieszAnnulusJoint.intermediatePrimes u (dyadicMomentOrder j))
        (dyadicMomentOrder j) n *
          (middleLayerAllowance (SquarefreeVaughanLogSource.length u (dyadicMomentOrder j)) n *
            |Real.cos (y * Real.log n)|)

/-- The full one-sided budget removes at least three quarters of the entire actual four-prime charge. -/
theorem budget_le_antichain_sub_four {u : ℝ} (hu : 0 ≤ u) (y : ℝ) (j : ℕ) :
    budget u y j ≤ antichainBudget u y j - (3 / 4 : ℝ) * fourCharge u y j := by
  let N := dyadicMomentOrder j
  let L := SquarefreeVaughanLogSource.length u N
  let A := ZetaRieszAnnulusJoint.intermediatePrimes u N
  let S := nondominantBand u N (dyadicPrimeCount j)
  let B := fun n => middleLayerAllowance L n * |Real.cos (y * Real.log n)|
  have hL : 0 < L := SquarefreeVaughanLogSource.length_pos u N
  have hp (n : ℕ) : weight A N n * phaseCost L y n ≤
      weight A N n * B n -
        (if FourSavingClass L n then (3 / 4 : ℝ) * (weight A N n * B n) else 0) := by
    by_cases hn : FourSavingClass L n
    · rw [if_pos hn]
      have h := mul_le_mul_of_nonneg_left
        (four_phaseCost_le_quarter hL y hn.1 hn.2.1 hn.2.2.1 hn.2.2.2)
        (weight_nonneg A N n)
      dsimp only [B]
      nlinarith
    · rw [if_neg hn, sub_zero]
      exact mul_le_mul_of_nonneg_left (phaseCost_le_antichain hL y n) (weight_nonneg A N n)
  have hs := Finset.sum_le_sum (s := S) (fun n _ => hp n)
  rw [Finset.sum_sub_distrib] at hs
  have he : (∑ n ∈ S, if FourSavingClass L n then (3 / 4 : ℝ) * (weight A N n * B n) else 0) =
      (3 / 4 : ℝ) * ∑ n ∈ S.filter (FourSavingClass L), weight A N n * B n := by
    rw [Finset.sum_filter, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro n _
    split_ifs <;> ring
  rw [he] at hs
  have ht := mul_le_mul_of_nonneg_left hs (pow_nonneg hu (N + 1))
  change u ^ (N + 1) * _ ≤ u ^ (N + 1) * _ - (3 / 4 : ℝ) * (u ^ (N + 1) * _)
  dsimp only [B, S, A, L, N] at ht
  nlinarith

/-- A quantitative independent one-sided bound for the complete remaining arithmetic sum, with a proved seventy-five-percent credit on the specified four-prime class. -/
theorem nondominantRemainder_lower_with_four_credit {u : ℝ} (hu : 0 ≤ u) (y : ℝ) (j : ℕ) :
    -antichainBudget u y j + (3 / 4 : ℝ) * fourCharge u y j ≤
      (nondominantRemainder u y j).re := by
  linarith [nondominantRemainder_lower hu y j, budget_le_antichain_sub_four hu y j]

/-- The explicit recovered four-prime charge is nonnegative at every source radius and order. -/
theorem fourCharge_nonneg {u : ℝ} (hu : 0 ≤ u) (y : ℝ) (j : ℕ) :
    0 ≤ fourCharge u y j := by
  apply mul_nonneg (pow_nonneg hu _)
  apply Finset.sum_nonneg
  intro n _
  exact mul_nonneg (weight_nonneg _ _ n)
    (mul_nonneg (middleLayerAllowance_nonneg (SquarefreeVaughanLogSource.length_pos _ _) n)
      (abs_nonneg _))

end
end RiemannGaussian.ZetaRieszOneSidedArithmetic
