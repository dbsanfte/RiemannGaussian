/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaAngularPhaseLimit

/-!
# Actual zero exclusion for general phase families

The exact selected source competes with the complete countable angular
budget on a single moving-order schedule. Every geometric and analytic
condition holds eventually on that same schedule. The resulting theorem
applies to all eligible families and center shifts without a numerical
search for coefficients.
-/

namespace RiemannGaussian.ZetaAngularPhaseExclusion
noncomputable section
open Filter ZetaNearOneBudgetLimit DerivativeOrderComparison ZetaLogLogScale
open ZetaAngularPhaseAllowance ZetaAngularPhaseFamily
open scoped Topology

/-- Any strict surplus of the exact source margin over the full
limiting budget excludes actual zeros in the proposed eventual width. -/
theorem exists_eventual_margin_of_schedule {a ω : ℕ → ℝ}
    (ha : ∀ n, 0 ≤ a n) (hs : Summable a) (hp : ∀ t, 0 ≤ zetaPhaseKernel a ω t)
    (hω0 : ω 0 = 0) (hω1 : ω 1 = 1) (hω : ∀ n, n ≠ 0 → 1 ≤ ω n)
    (hlog : Summable (fun n ↦ tail a n * Real.log (ω n)))
    {b C r : ℝ} (hb : Real.log 2 < b) (hC : 0 < C) (hr : 0 < r)
    (hcost : 2 * mass a * C * b / Real.pi < PhasePoleMargin.margin (a 0) (a 1) r) :
    ∃ T : ℝ, 2 ≤ T ∧ ∀ ρ : NontrivialZetaZero, T ≤ |ρ.1.im| →
      width C |ρ.1.im| < 1 - ρ.1.re := by
  have hbpos : 0 < b := lt_trans (Real.log_pos (by norm_num : (1 : ℝ) < 2)) hb
  have hc : ∀ᶠ t : ℝ in atTop,
      cost (order b t) r (width C t) t a ω < PhasePoleMargin.margin (a 0) (a 1) r :=
    (ZetaAngularPhaseLimit.cost_tendsto ha hs hω hlog hb hC hr).eventually (gt_mem_nhds hcost)
  have hgeom : ∀ᶠ t : ℝ in atTop, 4 * (r + 1) * width C t < delta (order b t) := by
    have h := (width_div_delta_tendsto hb C).const_mul (4 * (r + 1))
    simp only [mul_zero] at h
    filter_upwards [h.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1))] with t ht
    rw [← mul_div_assoc] at ht
    exact (div_lt_one (delta_pos (order b t))).mp ht
  have hall : ∀ᶠ t : ℝ in atTop,
      2 ≤ t ∧ 2 ≤ order b t ∧ 0 < level t ∧ 1 ≤ scale t ∧
        4 * (r + 1) * width C t < delta (order b t) ∧
          cost (order b t) r (width C t) t a ω < PhasePoleMargin.margin (a 0) (a 1) r := by
    filter_upwards [eventually_ge_atTop (2 : ℝ),
      (order_atTop hbpos).eventually (eventually_ge_atTop (2 : ℕ)),
      level_atTop.eventually (eventually_gt_atTop (0 : ℝ)),
      scale_atTop.eventually (eventually_ge_atTop (1 : ℝ)), hgeom, hc] with t ht ho hl hscale hg hct
    exact ⟨ht, ho, hl, hscale, hg, hct⟩
  obtain ⟨T, hT⟩ := eventually_atTop.mp hall
  refine ⟨max T 2, le_max_right _ _, ?_⟩
  intro ρ hρ
  obtain ⟨ht, ho, hl, hscale, hg, hct⟩ := hT |ρ.1.im| ((le_max_left T 2).trans hρ)
  have hscale' : 1 ≤ scale ρ.1.im := by simpa [scale, ZetaNearOneLogProfile.height] using hscale
  by_contra! hnear
  have hforced := margin_le_cost_of_zero_near ha hs hp hω0 hω1 hω hlog
    (order b |ρ.1.im|) ho ρ ht hscale' hr (width_pos hC hl) hg hnear
  rw [← ZetaAngularPhaseLimit.cost_abs] at hforced
  exact (not_le_of_gt hct) hforced

/-- A strict coefficient surplus supplies one fixed schedule and the
actual eventual exclusion, for every eligible countable phase family. -/
theorem exists_eventual_margin {a ω : ℕ → ℝ}
    (ha : ∀ n, 0 ≤ a n) (hs : Summable a) (hp : ∀ t, 0 ≤ zetaPhaseKernel a ω t)
    (hω0 : ω 0 = 0) (hω1 : ω 1 = 1) (hω : ∀ n, n ≠ 0 → 1 ≤ ω n)
    (hlog : Summable (fun n ↦ tail a n * Real.log (ω n))) (hM : 0 < mass a)
    {C r : ℝ} (hC : 0 < C) (hr : 0 < r)
    (hlim : 2 * mass a * C * Real.log 2 < Real.pi * PhasePoleMargin.margin (a 0) (a 1) r) :
    ∃ T : ℝ, 2 ≤ T ∧ ∀ ρ : NontrivialZetaZero, T ≤ |ρ.1.im| →
      width C |ρ.1.im| < 1 - ρ.1.re := by
  have hpC : 0 < 2 * mass a * C := by positivity
  have hgap : Real.log 2 < Real.pi * PhasePoleMargin.margin (a 0) (a 1) r /
      (2 * mass a * C) := (lt_div_iff₀ hpC).mpr (by nlinarith only [hlim])
  obtain ⟨b, hb, hb'⟩ := exists_between hgap
  apply exists_eventual_margin_of_schedule ha hs hp hω0 hω1 hω hlog hb hC hr
  apply (div_lt_iff₀ Real.pi_pos).mpr
  have h := (lt_div_iff₀ hpC).mp hb'
  nlinarith only [h]

/-- The exact symbolic optimizer supplies the largest source margin
at fixed coefficients. Every eligible family with a strict surplus over
this complete cost yields an actual eventual zero exclusion. -/
theorem exists_eventual_margin_of_optimal_shift {a ω : ℕ → ℝ}
    (ha : ∀ n, 0 ≤ a n) (hs : Summable a) (hp : ∀ t, 0 ≤ zetaPhaseKernel a ω t)
    (hω0 : ω 0 = 0) (hω1 : ω 1 = 1) (hω : ∀ n, n ≠ 0 → 1 ≤ ω n)
    (hlog : Summable (fun n ↦ tail a n * Real.log (ω n)))
    (h₀ : 0 < a 0) (h₁ : a 0 < a 1) {C : ℝ} (hC : 0 < C)
    (hlim : 2 * mass a * C * Real.log 2 < Real.pi * PhasePoleMargin.optimum (a 0) (a 1)) :
    ∃ T : ℝ, 2 ≤ T ∧ ∀ ρ : NontrivialZetaZero, T ≤ |ρ.1.im| →
      width C |ρ.1.im| < 1 - ρ.1.re := by
  have hM : 0 < mass a := by
    apply (tail_summable ha hs).tsum_pos (tail_nonneg ha) 1
    simpa only [tail, show (1 : ℕ) ≠ 0 by norm_num, if_false] using h₀.trans h₁
  apply exists_eventual_margin ha hs hp hω0 hω1 hω hlog hM hC
    (PhasePoleMargin.optimalShift_pos h₀ h₁)
  rwa [PhasePoleMargin.margin_optimalShift h₀ h₁]

end
end RiemannGaussian.ZetaAngularPhaseExclusion
