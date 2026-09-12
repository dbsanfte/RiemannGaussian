/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaNearOneBudgetLimit

/-!
# Eventual zero exclusion for every fixed logarithmic coefficient

An arbitrary positive coefficient determines a fixed derivative order.
The complete normalized prime allowance tends to a number strictly below
one at that order, whereas an actual zero in the proposed region forces
the allowance to be at least one. All center, radius, and multiplicity
conditions are proved for the actual zeta function.
-/

namespace RiemannGaussian.ZetaNearOneExclusion
noncomputable section
open Filter ZetaNearOneBudgetLimit ZetaNearOnePhaseConstraint ZetaNearOneJensen
open ZetaNearOneLogProfile DerivativeOrderComparison
open scoped Topology

/-- The proposed arbitrary-coefficient margin at logarithmic height. -/
def margin (C t : ℝ) : ℝ := C / scale t

/-- The complete normalized arithmetic and canonical radial allowance. -/
def cost (k : ℕ) (C t : ℝ) : ℝ :=
  14 * margin C t * budget k (shift C t) t + 6272 * (margin C t) ^ 2 / (delta k) ^ 2

/-- Every positive target coefficient gives a positive margin. -/
theorem margin_pos {C : ℝ} (hC : 0 < C) (t : ℝ) : 0 < margin C t :=
  div_pos hC (scale_pos t)

/-- The actual margin tends to zero at each fixed coefficient. -/
theorem margin_tendsto_zero (C : ℝ) : Tendsto (margin C) atTop (𝓝 0) :=
  scale_atTop.const_div_atTop C

/-- The center shift is exactly six times the proposed margin. -/
theorem shift_eq_six_margin (C t : ℝ) : shift C t = 6 * margin C t := by
  unfold shift margin
  ring

/-- The complete normalized cost has its explicit fixed-order limit. -/
theorem cost_tendsto (k : ℕ) {C : ℝ} (hC : 0 < C) :
    Tendsto (cost k C) atTop (𝓝 (560 * C / ((k : ℝ) + 2))) := by
  have h := ((budget_div_scale k hC).const_mul (14 * C)).add
    ((((margin_tendsto_zero C).pow 2).const_mul 6272).div_const ((delta k) ^ 2))
  simp only [zero_pow (by norm_num : (2 : ℕ) ≠ 0), mul_zero, zero_div, add_zero] at h
  have he : 14 * C * (40 / ((k : ℝ) + 2)) = 560 * C / ((k : ℝ) + 2) := by ring
  rw [he] at h
  convert h using 1
  funext t
  unfold cost margin
  ring

/-- Reflection preserves the proposed margin. -/
theorem margin_abs (C t : ℝ) : margin C |t| = margin C t := by
  simp [margin, scale, height]

/-- Reflection preserves every term of the normalized allowance. -/
theorem cost_abs (k : ℕ) (C t : ℝ) : cost k C |t| = cost k C t := by
  unfold cost
  rw [margin_abs, shift_eq_six_margin, margin_abs, budget_abs, shift_eq_six_margin]

/-- Every positive target coefficient admits a fixed derivative order
with normalized leading cost strictly below one. -/
theorem exists_order (C : ℝ) :
    ∃ k : ℕ, 1 ≤ k ∧ 560 * C / ((k : ℝ) + 2) < 1 := by
  obtain ⟨n, hn⟩ := exists_nat_gt (560 * C)
  refine ⟨n + 1, by omega, ?_⟩
  rw [div_lt_one (by positivity : (0 : ℝ) < ((n + 1 : ℕ) : ℝ) + 2)]
  push_cast
  linarith

/-- An actual zero inside the proposed margin forces the complete
normalized cost to be at least one. Every prime and analytic bound has
already been discharged; only geometric eligibility is assumed. -/
theorem one_le_cost_of_zero_near (k : ℕ) (hk : 1 ≤ k) {C : ℝ} (hC : 0 < C)
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
  have hb := source_le_budget k hk ρ ht (by positivity : 0 < 6 * u) hx hdr
  change 4 * (analyticZetaZeroMultiplicity ρ : ℝ) *
      (1 / d - 16 * d / (delta k) ^ 2) ≤ 3 / (6 * u) + budget k (6 * u) ρ.1.im at hb
  have hsq : d ^ 2 ≤ (delta k / 4) ^ 2 := pow_le_pow_left₀ hd.le hdr.le 2
  have hsource : 0 ≤ 1 / d - 16 * d / (delta k) ^ 2 := by
    apply sub_nonneg.mpr
    apply (div_le_div_iff₀ (sq_pos_of_pos hδ) hd).mpr
    nlinarith
  have hm : (1 : ℝ) ≤ (analyticZetaZeroMultiplicity ρ : ℝ) := by
    exact_mod_cast analyticZetaZeroMultiplicity_positive ρ
  have hmass := mul_le_mul_of_nonneg_right hm hsource
  have hi := one_div_le_one_div_of_le hd hdu
  have hrad := div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_left hdu (by norm_num : (0 : ℝ) ≤ 16)) (sq_nonneg (delta k))
  have hlower : 4 * (1 / (7 * u) - 16 * (7 * u) / (delta k) ^ 2) ≤
      4 * (analyticZetaZeroMultiplicity ρ : ℝ) * (1 / d - 16 * d / (delta k) ^ 2) := by
    nlinarith
  have hbound := hlower.trans hb
  have hmul := mul_le_mul_of_nonneg_left hbound (by positivity : 0 ≤ 14 * u)
  have heL : 14 * u * (4 * (1 / (7 * u) - 16 * (7 * u) / (delta k) ^ 2)) =
      8 - 6272 * u ^ 2 / (delta k) ^ 2 := by
    field_simp
    ring
  have heR : 14 * u * (3 / (6 * u) + budget k (6 * u) ρ.1.im) =
      7 + 14 * u * budget k (6 * u) ρ.1.im := by
    field_simp
    ring
  rw [heL, heR] at hmul
  unfold cost
  rw [shift_eq_six_margin]
  change 1 ≤ 14 * u * budget k (6 * u) ρ.1.im + 6272 * u ^ 2 / (delta k) ^ 2
  linarith

/-- Every positive logarithmic coefficient eventually excludes actual
zeros near the right edge. The order is fixed before the height limit,
and the threshold may depend on the coefficient. -/
theorem exists_eventual_margin {C : ℝ} (hC : 0 < C) :
    ∃ T : ℝ, 2 ≤ T ∧ ∀ ρ : NontrivialZetaZero, T ≤ |ρ.1.im| →
      margin C ρ.1.im < 1 - ρ.1.re := by
  obtain ⟨k, hk, hleading⟩ := exists_order C
  have hc : ∀ᶠ t : ℝ in atTop, cost k C t < 1 :=
    (cost_tendsto k hC).eventually (gt_mem_nhds hleading)
  have hsmall : ∀ᶠ t : ℝ in atTop, 28 * margin C t < delta k := by
    have h := (margin_tendsto_zero C).const_mul 28
    simp only [mul_zero] at h
    exact h.eventually (gt_mem_nhds (delta_pos k))
  have hall : ∀ᶠ t : ℝ in atTop, 2 ≤ t ∧ cost k C t < 1 ∧ 28 * margin C t < delta k := by
    filter_upwards [eventually_ge_atTop (2 : ℝ), hc, hsmall] with t ht hct hst
    exact ⟨ht, hct, hst⟩
  obtain ⟨T, hT⟩ := Filter.eventually_atTop.mp hall
  refine ⟨max T 2, le_max_right _ _, ?_⟩
  intro ρ hρ
  obtain ⟨ht, hct, hst⟩ := hT |ρ.1.im| ((le_max_left T 2).trans hρ)
  rw [cost_abs] at hct
  rw [margin_abs] at hst
  by_contra! hnear
  exact (not_le_of_gt hct) (one_le_cost_of_zero_near k hk hC ρ ht hst hnear)

end
end RiemannGaussian.ZetaNearOneExclusion
