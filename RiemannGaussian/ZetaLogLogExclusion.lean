/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaLogLogBudget

/-!
# Actual log-log exclusion with a growing derivative order

Every positive coefficient satisfying `140*C*log(2)<1` admits a fixed
schedule parameter `b>log(2)` with complete limiting cost below one.
The actual order then grows as `floor(log(log(abs(t)+2))/b)`. All radius,
center, multiplicity and height conditions are proved on this same
schedule before the actual prime contradiction is applied.
-/

namespace RiemannGaussian.ZetaLogLogExclusion
noncomputable section
open Filter ZetaLogLogScale ZetaLogLogBudget ZetaFullRadiusPrimeBudget
open DerivativeOrderComparison
open scoped Topology

/-- Every coefficient strictly below the available limiting budget
admits a schedule with both positive power saving and a strict surplus. -/
theorem exists_schedule {C : ℝ} (hC : 0 < C) (hlim : 140 * C * Real.log 2 < 1) :
    ∃ b : ℝ, Real.log 2 < b ∧ 140 * C * b < 1 := by
  have hp : 0 < 140 * C := by positivity
  have hgap : Real.log 2 < 1 / (140 * C) := (lt_div_iff₀ hp).mpr (by nlinarith)
  obtain ⟨b, hb, hb'⟩ := exists_between hgap
  refine ⟨b, hb, ?_⟩
  have h := (lt_div_iff₀ hp).mp hb'
  nlinarith

/-- The full local contradiction cost is unchanged when the actual
ordinate is replaced by its absolute value, including the moving order. -/
theorem cost_abs (b C t : ℝ) :
    cost (order b |t|) (C * level |t|) |t| = cost (order b t) (C * level t) t := by
  obtain ⟨hl, ho, _⟩ := abs_invariance b C t
  rw [hl, ho, ZetaFullRadiusPrimeBudget.cost_abs]

/-- Each schedule with complete limiting cost below one excludes
actual right-edge zeros with the specified log-log margin eventually. -/
theorem exists_eventual_margin_of_schedule {b C : ℝ}
    (hb : Real.log 2 < b) (hC : 0 < C) (hcost : 140 * C * b < 1) :
    ∃ T : ℝ, 2 ≤ T ∧ ∀ ρ : NontrivialZetaZero, T ≤ |ρ.1.im| →
      width C ρ.1.im < 1 - ρ.1.re := by
  have hbpos : 0 < b := lt_trans (Real.log_pos (by norm_num : (1 : ℝ) < 2)) hb
  have hc : ∀ᶠ t : ℝ in atTop, cost (order b t) (C * level t) t < 1 :=
    (ZetaLogLogBudget.cost_tendsto hb hC).eventually (gt_mem_nhds hcost)
  have hgeom : ∀ᶠ t : ℝ in atTop, 28 * width C t < delta (order b t) := by
    have h := (width_div_delta_tendsto hb C).const_mul 28
    simp only [mul_zero] at h
    filter_upwards [h.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1))] with t ht
    rw [← mul_div_assoc] at ht
    exact (div_lt_one (delta_pos (order b t))).mp ht
  have hall : ∀ᶠ t : ℝ in atTop,
      2 ≤ t ∧ 2 ≤ order b t ∧ 0 < level t ∧
        28 * width C t < delta (order b t) ∧ cost (order b t) (C * level t) t < 1 := by
    filter_upwards [eventually_ge_atTop (2 : ℝ),
      (order_atTop hbpos).eventually (eventually_ge_atTop (2 : ℕ)),
      level_atTop.eventually (eventually_gt_atTop (0 : ℝ)), hgeom, hc] with t ht ho hl hg hct
    exact ⟨ht, ho, hl, hg, hct⟩
  obtain ⟨T, hT⟩ := eventually_atTop.mp hall
  refine ⟨max T 2, le_max_right _ _, ?_⟩
  intro ρ hρ
  obtain ⟨ht, ho, hl, hg, hct⟩ := hT |ρ.1.im| ((le_max_left T 2).trans hρ)
  obtain ⟨hlabs, hoabs, hwabs⟩ := abs_invariance b C ρ.1.im
  rw [hoabs] at ho
  rw [hlabs] at hl
  rw [hwabs, hoabs] at hg
  rw [cost_abs] at hct
  by_contra! hnear
  have hforced := one_le_cost_of_zero_near (order b ρ.1.im) ho
    (mul_pos hC hl) ρ ht hg hnear
  exact (not_le_of_gt hct) hforced

/-- Every coefficient with `140*C*log(2)<1` gives an actual eventual
right-edge exclusion of log-log shape, with all growing-order costs
discharged. The threshold is existential and coefficient-dependent. -/
theorem exists_eventual_margin {C : ℝ} (hC : 0 < C) (hlim : 140 * C * Real.log 2 < 1) :
    ∃ T : ℝ, 2 ≤ T ∧ ∀ ρ : NontrivialZetaZero, T ≤ |ρ.1.im| →
      width C ρ.1.im < 1 - ρ.1.re := by
  obtain ⟨b, hb, hc⟩ := exists_schedule hC hlim
  exact exists_eventual_margin_of_schedule hb hC hc

end
end RiemannGaussian.ZetaLogLogExclusion
