/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaNearOneSignedBound
import RiemannGaussian.ZetaSignedExactPole

/-!
# Actual prime phase constraints from shrinking-disc estimates

The complete three-height von Mangoldt positivity inequality combines
with the new signed local bounds. The zero contribution retains its full
multiplicity and radial correction, and both height-dependent allowances
remain explicit. No independent prime-bound hypothesis is assumed here.
-/

namespace RiemannGaussian.ZetaNearOnePhaseConstraint
noncomputable section
open Complex ZetaNearOneLocalDisc ZetaNearOneJensen ZetaNearOneSignedBound
open DerivativeOrderComparison

/-- The complete real-axis and two oscillatory-height allowances in the
actual three-height prime inequality. -/
def budget (k : ℕ) (x t : ℝ) : ℝ :=
  1344 * localZetaLogHeight 0 +
    (32 * allowance k x t + 8 * allowance k x (2 * t)) / delta k

/-- The actual prime phase inequality bounds the selected zero's
complete reciprocal-distance source at every admissible order and shift. -/
theorem source_le_budget (k : ℕ) (hk : 1 ≤ k) (ρ : NontrivialZetaZero)
    {x : ℝ} (ht : 2 ≤ |ρ.1.im|) (hx : 0 < x) (hx' : x ≤ delta k / 4)
    (hnear : x + 1 - ρ.1.re < delta k / 4) :
    4 * (analyticZetaZeroMultiplicity ρ : ℝ) *
      (1 / (x + 1 - ρ.1.re) - 16 * (x + 1 - ρ.1.re) / (delta k) ^ 2) ≤
      3 / x + budget k x ρ.1.im := by
  have hsmall : x ≤ 1 / 4 := by
    have hd := delta_eq_one_sub_line k
    have hl := half_le_line k hk
    linarith
  have hprime := neg_logDeriv_riemannZeta_three_height_nonneg
    (a := 1 + x) (by linarith) ρ.1.im
  have hreal := neg_logDeriv_riemannZeta_real_le_local hx hsmall
  have hzero := neg_logDeriv_re_le_sub_zero k hk ρ ht hx hx' hnear
  have ht2 : 2 ≤ |2 * ρ.1.im| := by rw [abs_mul]; norm_num; linarith
  have hdouble := neg_logDeriv_re_le k hk ht2 hx hx'
  change 0 ≤ 3 * (-logDeriv riemannZeta ((1 + x : ℝ) : ℂ)).re +
    4 * (-logDeriv riemannZeta (center x ρ.1.im)).re +
    (-logDeriv riemannZeta (center x (2 * ρ.1.im))).re at hprime
  unfold budget
  simp only [div_eq_mul_inv] at hreal hzero hdouble ⊢
  nlinarith

/-- At six times the actual boundary gap, prime positivity gives a
fully explicit order-uniform constraint, retaining multiplicity and the
quadratic radial correction. -/
theorem zero_gap_constraint (k : ℕ) (hk : 1 ≤ k) (ρ : NontrivialZetaZero)
    (ht : 2 ≤ |ρ.1.im|) (hnear : 1 - ρ.1.re < delta k / 28) :
    (analyticZetaZeroMultiplicity ρ : ℝ) *
      (8 - 6272 * (1 - ρ.1.re) ^ 2 / (delta k) ^ 2) ≤
      7 + 14 * (1 - ρ.1.re) * budget k (6 * (1 - ρ.1.re)) ρ.1.im := by
  let η : ℝ := 1 - ρ.1.re
  have hη : 0 < η := sub_pos.mpr (NontrivialZetaZero.re_lt_one ρ)
  have hδ := delta_pos k
  have h := source_le_budget k hk ρ ht (by positivity : 0 < 6 * η)
    (by dsimp [η]; linarith : 6 * η ≤ delta k / 4)
    (by dsimp [η]; linarith : 6 * η + 1 - ρ.1.re < delta k / 4)
  rw [show 6 * η + 1 - ρ.1.re = 7 * η by dsimp [η]; ring] at h
  have hm := mul_le_mul_of_nonneg_left h (by positivity : 0 ≤ 14 * η)
  have hleft : 14 * η * (4 * (analyticZetaZeroMultiplicity ρ : ℝ) *
      (1 / (7 * η) - 16 * (7 * η) / (delta k) ^ 2)) =
      (analyticZetaZeroMultiplicity ρ : ℝ) * (8 - 6272 * η ^ 2 / (delta k) ^ 2) := by
    field_simp
    ring
  have hright : 14 * η * (3 / (6 * η) + budget k (6 * η) ρ.1.im) =
      7 + 14 * η * budget k (6 * η) ρ.1.im := by
    field_simp
    ring
  rw [hleft, hright] at hm
  exact hm

end
end RiemannGaussian.ZetaNearOnePhaseConstraint
