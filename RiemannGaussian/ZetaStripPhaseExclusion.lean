/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaStripPhaseFamily
import RiemannGaussian.PhaseIncrementInverse

/-!
# Concrete strip zero exclusion for every eligible phase family

The exact cotangent decreases with the proposed horizontal width. Thus a
strict surplus at that width excludes every actual zero at the same height.
Both the full signed arithmetic budget and its uniform Euler upper bound
remain available. No asymptotic threshold or numerical coefficient search is
assumed by these finite-height criteria.
-/

namespace RiemannGaussian.ZetaStripPhaseExclusion
noncomputable section
open ZetaNearOneBudgetLimit DerivativeOrderComparison ZetaAngularPhaseAllowance
open ZetaStripEulerConstraint ZetaStripPhaseFamily

/-- Any actual zero in the proposed width contributes at least the exact
cotangent at its outside edge. The whole analytic multiplicity remains on
the actual source side of the comparison. -/
theorem source_at_margin_le (k : ℕ) (ρ : NontrivialZetaZero) {x u : ℝ}
    (hx : 0 < x) (hu : 0 < u) (hu' : u < delta k) (hnear : 1 - ρ.1.re ≤ u) :
    (Real.pi / (2 * halfWidth k x)) * Real.cot (Real.pi * (x + u) / (2 * halfWidth k x)) ≤
      (analyticZetaZeroMultiplicity ρ : ℝ) * (Real.pi / (2 * halfWidth k x)) *
        Real.cot (Real.pi * (1 + x - ρ.1.re) / (2 * halfWidth k x)) := by
  have hη := halfWidth_pos k hx
  have hd : 0 < 1 + x - ρ.1.re := by linarith [NontrivialZetaZero.re_lt_one ρ]
  have hdu : 1 + x - ρ.1.re ≤ x + u := by linarith
  have huη : x + u < halfWidth k x := by unfold halfWidth; linarith
  have hq : 0 < Real.pi * (1 + x - ρ.1.re) / (2 * halfWidth k x) := by positivity
  have hp : 0 < Real.pi * (x + u) / (2 * halfWidth k x) := by positivity
  have hqp : Real.pi * (1 + x - ρ.1.re) / (2 * halfWidth k x) ≤
      Real.pi * (x + u) / (2 * halfWidth k x) :=
    div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hdu Real.pi_pos.le) (by positivity)
  have hpπ : Real.pi * (x + u) / (2 * halfWidth k x) < Real.pi / 2 := by
    rw [div_lt_iff₀ (by positivity : 0 < 2 * halfWidth k x)]
    nlinarith [Real.pi_pos]
  have hcot := PhaseIncrementInverse.cot_antitoneOn
    (show Real.pi * (1 + x - ρ.1.re) / (2 * halfWidth k x) ∈ Set.Ioo 0 Real.pi from
      ⟨hq, by linarith [Real.pi_pos]⟩)
    (show Real.pi * (x + u) / (2 * halfWidth k x) ∈ Set.Ioo 0 Real.pi from
      ⟨hp, by linarith [Real.pi_pos]⟩) hqp
  have hcpos : 0 < Real.cot (Real.pi * (1 + x - ρ.1.re) / (2 * halfWidth k x)) := by
    rw [Real.cot_eq_cos_div_sin]
    exact div_pos (Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], by linarith⟩)
      (Real.sin_pos_of_pos_of_lt_pi hq (by linarith [Real.pi_pos]))
  have hm : (1 : ℝ) ≤ (analyticZetaZeroMultiplicity ρ : ℝ) := by
    exact_mod_cast analyticZetaZeroMultiplicity_positive ρ
  have hweighted := mul_le_mul_of_nonneg_left hcot
    (by positivity : 0 ≤ Real.pi / (2 * halfWidth k x))
  have hmass := mul_le_mul_of_nonneg_right hm
    (by positivity : 0 ≤ (Real.pi / (2 * halfWidth k x)) *
      Real.cot (Real.pi * (1 + x - ρ.1.re) / (2 * halfWidth k x)))
  nlinarith only [hweighted, hmass]

/-- A surplus over the original signed budget excludes a zero in the
proposed width at that exact height, for every finite retained negative depth. -/
theorem margin_lt_one_sub_re_of_exactBudget {a ω : ℕ → ℝ}
    (ha : ∀ n, 0 ≤ a n) (hs : Summable a) (hp : ∀ t, 0 ≤ zetaPhaseKernel a ω t)
    (hω0 : ω 0 = 0) (hω1 : ω 1 = 1) (hω : ∀ n, n ≠ 0 → 1 ≤ ω n)
    (hlog : Summable (fun n ↦ tail a n * Real.log (ω n)))
    (k : ℕ) (hk : 2 ≤ k) (ρ : NontrivialZetaZero) {x u M : ℝ}
    (ht : 2 ≤ |ρ.1.im|) (hscale : 1 ≤ scale ρ.1.im)
    (hx : 0 < x) (hx' : x ≤ delta k / 4) (hu : 0 < u) (hu' : u < delta k) (hM : 0 ≤ M)
    (hcost : a 0 / x + exactBudget k M x ρ.1.im a ω <
      a 1 * (Real.pi / (2 * halfWidth k x)) * Real.cot (Real.pi * (x + u) / (2 * halfWidth k x))) :
    u < 1 - ρ.1.re := by
  by_contra! hnear
  have hl : DirichletPowerParameters.line k < ρ.1.re := by
    rw [delta_eq_one_sub_line] at hu'
    linarith
  have h := source_le_exactBudget ha hs hp hω0 hω1 hω hlog k hk ρ ht hscale hx hx' hM hl
  have hb := mul_le_mul_of_nonneg_left (source_at_margin_le k ρ hx hu hu' hnear) (ha 1)
  nlinarith only [h, hb, hcost]

/-- A strict surplus over the uniform sharp Euler allowance gives an actual
finite-height zero exclusion for every eligible finite or infinite family. -/
theorem margin_lt_one_sub_re {a ω : ℕ → ℝ}
    (ha : ∀ n, 0 ≤ a n) (hs : Summable a) (hp : ∀ t, 0 ≤ zetaPhaseKernel a ω t)
    (hω0 : ω 0 = 0) (hω1 : ω 1 = 1) (hω : ∀ n, n ≠ 0 → 1 ≤ ω n)
    (hlog : Summable (fun n ↦ tail a n * Real.log (ω n)))
    (k : ℕ) (hk : 2 ≤ k) (ρ : NontrivialZetaZero) {x u : ℝ}
    (ht : 2 ≤ |ρ.1.im|) (hscale : 1 ≤ scale ρ.1.im)
    (hx : 0 < x) (hx' : x ≤ delta k / 4) (hu : 0 < u) (hu' : u < delta k)
    (hcost : a 0 / x + budget k x ρ.1.im a ω <
      a 1 * (Real.pi / (2 * halfWidth k x)) * Real.cot (Real.pi * (x + u) / (2 * halfWidth k x))) :
    u < 1 - ρ.1.re := by
  by_contra! hnear
  have hl : DirichletPowerParameters.line k < ρ.1.re := by
    rw [delta_eq_one_sub_line] at hu'
    linarith
  have h := source_le_budget ha hs hp hω0 hω1 hω hlog k hk ρ ht hscale hx hx' hl
  have hb := mul_le_mul_of_nonneg_left (source_at_margin_le k ρ hx hu hu' hnear) (ha 1)
  nlinarith only [h, hb, hcost]

/-- The wholly elementary allowance supplies the same actual zero
exclusion. Its strict inequality involves no unknown zeta value or integral. -/
theorem margin_lt_one_sub_re_of_elementaryBudget {a ω : ℕ → ℝ}
    (ha : ∀ n, 0 ≤ a n) (hs : Summable a) (hp : ∀ t, 0 ≤ zetaPhaseKernel a ω t)
    (hω0 : ω 0 = 0) (hω1 : ω 1 = 1) (hω : ∀ n, n ≠ 0 → 1 ≤ ω n)
    (hlog : Summable (fun n ↦ tail a n * Real.log (ω n)))
    (k : ℕ) (hk : 2 ≤ k) (ρ : NontrivialZetaZero) {x u : ℝ}
    (ht : 2 ≤ |ρ.1.im|) (hscale : 1 ≤ scale ρ.1.im)
    (hx : 0 < x) (hx' : x ≤ delta k / 4) (hu : 0 < u) (hu' : u < delta k)
    (hcost : a 0 / x + elementaryBudget k x ρ.1.im a ω <
      a 1 * (Real.pi / (2 * halfWidth k x)) * Real.cot (Real.pi * (x + u) / (2 * halfWidth k x))) :
    u < 1 - ρ.1.re :=
  margin_lt_one_sub_re ha hs hp hω0 hω1 hω hlog k hk ρ ht hscale hx hx' hu hu'
    ((add_le_add le_rfl (budget_le_elementaryBudget (ha 0) k hx ρ.1.im)).trans_lt hcost)

/-- A strict elementary budget surplus proves literal zeta nonvanishing
on the full closed right edge at that height. Actual zero membership and
all exceptional real points are handled inside the proof. -/
theorem nonvanishing_of_elementaryBudget {a ω : ℕ → ℝ}
    (ha : ∀ n, 0 ≤ a n) (hs : Summable a) (hp : ∀ t, 0 ≤ zetaPhaseKernel a ω t)
    (hω0 : ω 0 = 0) (hω1 : ω 1 = 1) (hω : ∀ n, n ≠ 0 → 1 ≤ ω n)
    (hlog : Summable (fun n ↦ tail a n * Real.log (ω n)))
    (k : ℕ) (hk : 2 ≤ k) (s : ℂ) {x u : ℝ}
    (ht : 2 ≤ |s.im|) (hscale : 1 ≤ scale s.im)
    (hx : 0 < x) (hx' : x ≤ delta k / 4) (hu : 0 < u) (hu' : u < delta k)
    (hcost : a 0 / x + elementaryBudget k x s.im a ω <
      a 1 * (Real.pi / (2 * halfWidth k x)) * Real.cot (Real.pi * (x + u) / (2 * halfWidth k x)))
    (hedge : 1 - u ≤ s.re) : riemannZeta s ≠ 0 := by
  intro hz
  have hn : ¬ ∃ n : ℕ, s = -2 * (n + 1) := by
    rintro ⟨n, rfl⟩
    norm_num at ht
  have hs1 : s ≠ 1 := by intro he; norm_num [he] at ht
  let ρ : NontrivialZetaZero := ⟨s, hz, hn, hs1⟩
  have h := margin_lt_one_sub_re_of_elementaryBudget ha hs hp hω0 hω1 hω hlog
    k hk ρ ht hscale hx hx' hu hu' hcost
  change u < 1 - s.re at h
  linarith

end
end RiemannGaussian.ZetaStripPhaseExclusion
