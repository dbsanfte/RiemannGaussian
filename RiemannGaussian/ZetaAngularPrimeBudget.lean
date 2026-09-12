/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaNearOneAngularBound
import RiemannGaussian.ZetaNearOneExclusion

/-!
# The actual prime budget with signed angular boundary control

Opposite semicircle estimates divide both oscillatory allowances by pi
and retain the selected multiplicity with its exact endpoint correction.
The resulting source contradiction uses the actual three-height prime
positivity theorem, with no unproved arithmetic bound as an input.
-/

namespace RiemannGaussian.ZetaAngularPrimeBudget
noncomputable section
open Complex Filter ZetaNearOneLocalDisc ZetaNearOneJensen
open ZetaNearOneBudgetLimit ZetaNearOneLogProfile DerivativeOrderComparison
open ZetaNearOneExclusion (margin margin_pos shift_eq_six_margin margin_abs)

/-- The real-axis and complete two-height analytic allowances at the
full available radius, with the signed angular factor retained. -/
def budget (k : ℕ) (x t : ℝ) : ℝ :=
  1344 * localZetaLogHeight 0 +
    (8 * allowance k x t + 2 * allowance k x (2 * t)) / (Real.pi * delta k)

/-- The source-normalized angular budget retains the exact
quadratic endpoint correction along the original center schedule. -/
def cost (k : ℕ) (C t : ℝ) : ℝ :=
  14 * margin C t * budget k (shift C t) t + 392 * (margin C t) ^ 2 / (delta k) ^ 2

/-- The actual prime phase inequality bounds the selected zero's
complete reciprocal-distance source at every admissible order and shift. -/
theorem source_le_budget (k : ℕ) (hk : 2 ≤ k) (ρ : NontrivialZetaZero)
    {x : ℝ} (ht : 2 ≤ |ρ.1.im|) (hx : 0 < x) (hx' : x ≤ delta k / 4)
    (hnear : x + 1 - ρ.1.re < delta k) :
    4 * (analyticZetaZeroMultiplicity ρ : ℝ) *
      (1 / (x + 1 - ρ.1.re) - (x + 1 - ρ.1.re) / (delta k) ^ 2) ≤
      3 / x + budget k x ρ.1.im := by
  have hsmall : x ≤ 1 / 4 := by
    have hd := ZetaNearOneFullDisc.delta_le_two_sevenths hk
    linarith
  have hprime := neg_logDeriv_riemannZeta_three_height_nonneg
    (a := 1 + x) (by linarith) ρ.1.im
  have hreal := neg_logDeriv_riemannZeta_real_le_local hx hsmall
  have hzero := ZetaNearOneAngularBound.neg_logDeriv_re_le_sub_zero k hk ρ ht hx hx' hnear
  have ht2 : 2 ≤ |2 * ρ.1.im| := by rw [abs_mul]; norm_num; linarith
  have hdouble := ZetaNearOneAngularBound.neg_logDeriv_re_le k hk ht2 hx hx'
  change 0 ≤ 3 * (-logDeriv riemannZeta ((1 + x : ℝ) : ℂ)).re +
    4 * (-logDeriv riemannZeta (center x ρ.1.im)).re +
    (-logDeriv riemannZeta (center x (2 * ρ.1.im))).re at hprime
  unfold budget
  simp only [div_eq_mul_inv] at hreal hzero hdouble ⊢
  nlinarith

/-- An actual zero inside the proposed margin forces the complete
normalized cost to be at least one. Every prime and analytic bound has
already been discharged; only geometric eligibility is assumed. -/
theorem one_le_cost_of_zero_near (k : ℕ) (hk : 2 ≤ k) {C : ℝ} (hC : 0 < C)
    (ρ : NontrivialZetaZero) (ht : 2 ≤ |ρ.1.im|)
    (hsmall : 28 * margin C ρ.1.im < delta k)
    (hnear : 1 - ρ.1.re ≤ margin C ρ.1.im) : 1 ≤ cost k C ρ.1.im := by
  let u := margin C ρ.1.im
  let d := 6 * u + 1 - ρ.1.re
  have hu : 0 < u := margin_pos hC _
  have hδ := delta_pos k
  have hd : 0 < d := by dsimp [d]; linarith [NontrivialZetaZero.re_lt_one ρ]
  have hdu : d ≤ 7 * u := by dsimp [d, u]; linarith
  have hdr : d < delta k / 4 := by dsimp [u] at hdu; linarith
  have hx : 6 * u ≤ delta k / 4 := by dsimp [u]; linarith
  have hb := source_le_budget k hk ρ ht (by positivity : 0 < 6 * u) hx (by linarith : d < delta k)
  change 4 * (analyticZetaZeroMultiplicity ρ : ℝ) *
      (1 / d - d / (delta k) ^ 2) ≤ 3 / (6 * u) + budget k (6 * u) ρ.1.im at hb
  have hsq : d ^ 2 ≤ (delta k) ^ 2 :=
    pow_le_pow_left₀ hd.le (by linarith : d ≤ delta k) 2
  have hsource : 0 ≤ 1 / d - d / (delta k) ^ 2 := by
    apply sub_nonneg.mpr
    apply (div_le_div_iff₀ (sq_pos_of_pos hδ) hd).mpr
    nlinarith
  have hm : (1 : ℝ) ≤ (analyticZetaZeroMultiplicity ρ : ℝ) := by
    exact_mod_cast analyticZetaZeroMultiplicity_positive ρ
  have hmass := mul_le_mul_of_nonneg_right hm hsource
  have hi := one_div_le_one_div_of_le hd hdu
  have hrad := div_le_div_of_nonneg_right
    hdu (sq_nonneg (delta k))
  have hlower : 4 * (1 / (7 * u) - (7 * u) / (delta k) ^ 2) ≤
      4 * (analyticZetaZeroMultiplicity ρ : ℝ) * (1 / d - d / (delta k) ^ 2) := by
    nlinarith
  have hbound := hlower.trans hb
  have hmul := mul_le_mul_of_nonneg_left hbound (by positivity : 0 ≤ 14 * u)
  have heL : 14 * u * (4 * (1 / (7 * u) - (7 * u) / (delta k) ^ 2)) =
      8 - 392 * u ^ 2 / (delta k) ^ 2 := by
    field_simp
    ring
  have heR : 14 * u * (3 / (6 * u) + budget k (6 * u) ρ.1.im) =
      7 + 14 * u * budget k (6 * u) ρ.1.im := by
    field_simp
    ring
  rw [heL, heR] at hmul
  unfold cost
  rw [shift_eq_six_margin]
  change 1 ≤ 14 * u * budget k (6 * u) ρ.1.im + 392 * u ^ 2 / (delta k) ^ 2
  linarith

/-- Conjugating the actual ordinate preserves the entire two-height
budget, including its center allowance. -/
theorem budget_abs (k : ℕ) (x t : ℝ) : budget k x |t| = budget k x t := by
  simp [budget, allowance, profile, height, abs_mul]

/-- The full normalized cost retains its value at the absolute ordinate. -/
theorem cost_abs (k : ℕ) (C t : ℝ) : cost k C |t| = cost k C t := by
  unfold cost
  rw [margin_abs, shift_eq_six_margin, margin_abs, budget_abs, shift_eq_six_margin]

end
end RiemannGaussian.ZetaAngularPrimeBudget
