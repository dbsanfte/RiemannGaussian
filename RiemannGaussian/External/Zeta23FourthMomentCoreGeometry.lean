import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
# Exact continuum geometry in the fourth-moment core

The endpoint four-cycle geometry reduces, after scaling, to two elementary
cross-section contributions.  The first occupies the whole normalized bulk
`0 <= t <= 1`; the second occupies `0 <= t <= 1/2`.  This file evaluates the
resulting constant exactly.  It is deliberately independent of any unproved
prime-correlation or passage-to-the-limit statement.
-/

namespace RiemannGaussian

noncomputable section

open intervalIntegral

/-- The full-bulk polynomial contribution to the scaled four-cycle core. -/
def fourthMomentCoreBulkIntegral : ℝ :=
  ∫ t in (0 : ℝ)..1, t * (1 - t) ^ 3

/-- The extra short-cell contribution, supported on the first half of the
scaled bulk. -/
def fourthMomentCoreShortIntegral : ℝ :=
  ∫ t in (0 : ℝ)..(1 / 2), t * (1 - 2 * t) ^ 3

/-- The normalized continuum core dictated by the four-cycle geometry. -/
def fourthMomentContinuumCore : ℝ :=
  -(1 / 3 : ℝ) *
    (fourthMomentCoreBulkIntegral + fourthMomentCoreShortIntegral)

lemma fourthMomentCoreBulkIntegral_eq :
    fourthMomentCoreBulkIntegral = 1 / 20 := by
  unfold fourthMomentCoreBulkIntegral
  let F : ℝ → ℝ := fun t =>
    t ^ 2 / 2 - t ^ 3 + 3 * t ^ 4 / 4 - t ^ 5 / 5
  have hderiv : ∀ t ∈ Set.uIcc (0 : ℝ) 1,
      HasDerivAt F (t * (1 - t) ^ 3) t := by
    intro t _
    let G : ℝ → ℝ :=
      (((fun x : ℝ => (id ^ 2) x / 2) - id ^ 3 +
        fun x : ℝ => 3 * (id ^ 4) x / 4) -
        fun x : ℝ => (id ^ 5) x / 5)
    have hF := (((hasDerivAt_id t).pow 2).div_const 2).sub
      ((hasDerivAt_id t).pow 3) |>.add
      ((((hasDerivAt_id t).pow 4).const_mul 3).div_const 4) |>.sub
      (((hasDerivAt_id t).pow 5).div_const 5)
    have hFG : Filter.EventuallyEq (nhds t) F G := by
      apply Filter.Eventually.of_forall
      intro x
      dsimp [F, G]
    have hF' := hF.congr_of_eventuallyEq hFG
    exact hF'.congr_deriv (by simp [id_eq]; ring)
  have hint : IntervalIntegrable (fun t : ℝ => t * (1 - t) ^ 3)
      MeasureTheory.volume 0 1 :=
    (by fun_prop : Continuous (fun t : ℝ => t * (1 - t) ^ 3)).intervalIntegrable _ _
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint]
  norm_num [F]

lemma fourthMomentCoreShortIntegral_eq :
    fourthMomentCoreShortIntegral = 1 / 80 := by
  unfold fourthMomentCoreShortIntegral
  let F : ℝ → ℝ := fun t =>
    t ^ 2 / 2 - 2 * t ^ 3 + 3 * t ^ 4 - 8 * t ^ 5 / 5
  have hderiv : ∀ t ∈ Set.uIcc (0 : ℝ) (1 / 2),
      HasDerivAt F (t * (1 - 2 * t) ^ 3) t := by
    intro t _
    let G : ℝ → ℝ :=
      ((((fun x : ℝ => (id ^ 2) x / 2) -
        fun x : ℝ => 2 * (id ^ 3) x) +
        fun x : ℝ => 3 * (id ^ 4) x) -
        fun x : ℝ => 8 * (id ^ 5) x / 5)
    have hF := (((hasDerivAt_id t).pow 2).div_const 2).sub
      (((hasDerivAt_id t).pow 3).const_mul 2) |>.add
      (((hasDerivAt_id t).pow 4).const_mul 3) |>.sub
      ((((hasDerivAt_id t).pow 5).const_mul 8).div_const 5)
    have hFG : Filter.EventuallyEq (nhds t) F G := by
      apply Filter.Eventually.of_forall
      intro x
      dsimp [F, G]
    have hF' := hF.congr_of_eventuallyEq hFG
    exact hF'.congr_deriv (by simp [id_eq]; ring)
  have hint : IntervalIntegrable (fun t : ℝ => t * (1 - 2 * t) ^ 3)
      MeasureTheory.volume 0 (1 / 2) :=
    (by fun_prop : Continuous
      (fun t : ℝ => t * (1 - 2 * t) ^ 3)).intervalIntegrable _ _
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint]
  norm_num [F]

/-- Exact replacement for the previously numerical continuum quadrature:
the scaled fourth-moment core is `-1/48`. -/
theorem fourthMomentContinuumCore_eq_neg_one_div_fortyEight :
    fourthMomentContinuumCore = -(1 / 48 : ℝ) := by
  rw [fourthMomentContinuumCore, fourthMomentCoreBulkIntegral_eq,
    fourthMomentCoreShortIntegral_eq]
  norm_num

end

end RiemannGaussian
