import RiemannGaussian.ZetaLocalResidualLog
import Mathlib.Analysis.Complex.JensenFormula

/-!
# Logarithmic control of the complete local zero divisor

Jensen's inequality on the actual translated unit disc bounds every zero
removed in the local canonical decomposition, with its full multiplicity.
The bound holds at every real ordinate, including small heights.
-/

open Complex Filter MeasureTheory MeromorphicOn Metric Set Topology
open scoped Classical ComplexConjugate ENNReal Interval Topology

namespace RiemannGaussian

noncomputable section

/-- The number of local zeros in the fixed inner disc, counted with full
analytic multiplicity, is bounded by logarithmic height. -/
theorem sum_divisor_localZetaPoleRemoved_innerDisc_le (y : ℝ) :
    ((∑ᶠ i, divisor (localZetaPoleRemoved y) (closedBall 0 (7 / 8 : ℝ)) i : ℤ) : ℝ) ≤
      32 * localZetaLogHeight y := by
  let T : ℝ := |y| + 22
  let M : ℝ := 8 * T ^ 2
  have hT : 22 ≤ T := by dsimp [T]; linarith [abs_nonneg y]
  have hM : 1 ≤ M := by dsimp [M]; nlinarith
  have han : AnalyticOnNhd ℂ (localZetaPoleRemoved y) (closedBall 0 |(1 : ℝ)|) := by
    simpa using analyticOnNhd_localZetaPoleRemoved_unitDisc y
  have hj := han.sum_divisor_le (r := (7 / 8 : ℝ)) (R := 1) (M := M)
    (by norm_num) (by norm_num) hM (localZetaPoleRemoved_zero_ne_zero y) (by
      intro z hz
      exact norm_localZetaPoleRemoved_le y (sphere_subset_closedBall (by simpa using hz)))
  rw [show |(7 / 8 : ℝ)| = 7 / 8 by norm_num] at hj
  norm_num at hj
  have hfloor := sixteenth_le_norm_localZetaPoleRemoved_zero y
  have hnorm : 0 < ‖localZetaPoleRemoved y 0‖ := by linarith
  have hratio : M / ‖localZetaPoleRemoved y 0‖ ≤ T ^ 4 := by
    rw [div_le_iff₀ hnorm]
    have hp : 128 ≤ T ^ 2 := by nlinarith
    have hprod := mul_le_mul_of_nonneg_right hp (sq_nonneg T)
    have hprod' := mul_le_mul_of_nonneg_left hfloor (pow_nonneg (by linarith : 0 ≤ T) 4)
    dsimp [M]
    nlinarith
  have hlog : Real.log (M / ‖localZetaPoleRemoved y 0‖) ≤ 4 * localZetaLogHeight y := by
    calc
      _ ≤ Real.log (T ^ 4) := Real.log_le_log (by positivity) hratio
      _ = _ := by rw [Real.log_pow]; rfl
  have hden : (1 / 8 : ℝ) ≤ Real.log (8 / 7 : ℝ) := by
    have h := Real.one_sub_inv_le_log_of_pos (by norm_num : (0 : ℝ) < 8 / 7)
    norm_num at h ⊢
    exact h
  apply hj.trans
  rw [div_le_iff₀ (by linarith : 0 < Real.log (8 / 7 : ℝ))]
  nlinarith [two_lt_localZetaLogHeight y]

/-- Every zero in the selected canonical disc is included in the
logarithmic Jensen count, with the same complete analytic divisor. -/
theorem sum_divisor_localZetaPoleRemoved_canonicalBall_le (y : ℝ) :
    ((∑ᶠ i, divisor (localZetaPoleRemoved y) (ball 0 (localZetaCanonicalRadius y)) i : ℤ) : ℝ) ≤
      32 * localZetaLogHeight y := by
  let f := localZetaPoleRemoved y
  let R := localZetaCanonicalRadius y
  let d : ℂ → ℤ := fun i ↦ divisor f (ball 0 R) i
  let e : ℂ → ℤ := fun i ↦ divisor f (closedBall 0 (7 / 8 : ℝ)) i
  have han : AnalyticOnNhd ℂ f (closedBall 0 (7 / 8 : ℝ)) :=
    fun z _ ↦ (differentiable_localZetaPoleRemoved y).analyticAt z
  have hmer : MeromorphicOn f (ball 0 R) :=
    (localZetaCanonicalResidual_decomp y).meromorphicOn.mono_set ball_subset_closedBall
  have hd : (Function.support d).Finite :=
    (localZetaCanonicalResidual_decomp y).meromorphicOn.divisor_ball_support_finite
  have he : (Function.support e).Finite :=
    (divisor f (closedBall 0 (7 / 8 : ℝ))).finiteSupport (isCompact_closedBall ..)
  have hp : ∀ i, d i ≤ e i := by
    intro i
    by_cases hi : i ∈ ball (0 : ℂ) R
    · have hi' : i ∈ closedBall 0 (7 / 8 : ℝ) := by
        rw [mem_closedBall, dist_zero_right]
        exact (show ‖i‖ < R by simpa only [mem_ball, dist_zero_right] using hi).le.trans
          (localZetaCanonicalRadius_spec y).2.1.le
      dsimp [d, e]
      rw [hmer.divisor_apply hi, han.meromorphicOn.divisor_apply hi']
    · have hdi : d i = 0 := by
        change (if MeromorphicOn f (ball 0 R) ∧ i ∈ ball 0 R then _ else 0) = 0
        rw [if_neg (fun h ↦ hi h.2)]
      rw [hdi]
      exact han.divisor_nonneg i
  have hs : ((∑ᶠ i, d i : ℤ) : ℝ) ≤ ((∑ᶠ i, e i : ℤ) : ℝ) := by
    exact_mod_cast finsum_le_finsum' hd he hp
  exact hs.trans (sum_divisor_localZetaPoleRemoved_innerDisc_le y)

end

end RiemannGaussian
