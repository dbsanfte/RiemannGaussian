import RiemannGaussian.GaussianXiSubquadraticGrowth

/-!
# Subquadratic Jensen counting for the xi divisor

The unconditional global `3/2`-power growth bound for `riemannXi` is inserted
into Jensen's inequality.  This gives a multiplicity-aware count of all
nontrivial zeta zeros in a centered disk whose exponent is strictly below
two.  That strict exponent gap is the input needed for a dyadic proof of
inverse-square spectral summability.
-/

namespace RiemannGaussian

noncomputable section

open MeromorphicOn Metric Set

/-- Jensen's inequality turns a global `3/2`-power exponential bound for xi
into a `3/2`-power bound for its divisor in every centered closed ball. -/
theorem jensen_riemannXi_divisor_le_threeHalves
    {A r : ℝ} (hA : 1 ≤ A) (hr : 0 < r)
    (hbound : ∀ z : ℂ,
      ‖riemannXi z‖ ≤
        Real.exp (A * (‖z‖ + 1) ^ (3 / 2 : ℝ))) :
    ∑ᶠ u, divisor riemannXi (closedBall 0 r) u ≤
      A * (2 * r + 1) ^ (3 / 2 : ℝ) / Real.log 2 := by
  have hRpos : 0 < 2 * r := mul_pos (by norm_num) hr
  have hM :
      1 ≤ Real.exp (A * (2 * r + 1) ^ (3 / 2 : ℝ)) := by
    rw [Real.one_le_exp_iff]
    exact mul_nonneg (le_trans (by norm_num) hA)
      (Real.rpow_nonneg (by positivity) _)
  have hJensen := AnalyticOnNhd.sum_divisor_le
    (f := riemannXi) (c := (0 : ℂ)) (r := r) (R := 2 * r)
    (M := Real.exp (A * (2 * r + 1) ^ (3 / 2 : ℝ)))
    (by simpa [abs_of_pos hr] using hr)
    (by simp only [abs_of_pos hr, abs_of_pos hRpos]; linarith)
    hM
    (analyticOnNhd_riemannXi.mono (subset_univ _))
    (by norm_num)
    (by
      intro z hz
      have hnorm : ‖z‖ = 2 * r := by
        simpa [mem_sphere, abs_of_pos hRpos] using hz
      simpa [hnorm] using hbound z)
  have hratio : (2 * r) / r = 2 := by
    field_simp [hr.ne']
  rw [abs_of_pos hr] at hJensen
  simpa [riemannXi_zero, hratio, Real.log_exp] using hJensen

/-- A witness for global `3/2`-growth supplies one uniform subquadratic
divisor-count constant. -/
theorem RiemannXiThreeHalvesGrowth.exists_divisor_bound
    (hGrowth : RiemannXiThreeHalvesGrowth) :
    ∃ A : ℝ, 1 ≤ A ∧ ∀ r : ℝ, 0 < r →
      ∑ᶠ u, divisor riemannXi (closedBall 0 r) u ≤
        A * (2 * r + 1) ^ (3 / 2 : ℝ) / Real.log 2 := by
  rcases hGrowth with ⟨A, hA, hbound⟩
  exact ⟨A, hA, fun r hr =>
    jensen_riemannXi_divisor_le_threeHalves hA hr hbound⟩

/-- Unconditionally, the xi divisor has a centered-disk count of order at
most `r^(3/2)`, with analytic multiplicities included. -/
theorem exists_riemannXi_divisor_threeHalves_bound :
    ∃ A : ℝ, 1 ≤ A ∧ ∀ r : ℝ, 0 < r →
      ∑ᶠ u, divisor riemannXi (closedBall 0 r) u ≤
        A * (2 * r + 1) ^ (3 / 2 : ℝ) / Real.log 2 :=
  riemannXi_threeHalvesGrowth.exists_divisor_bound

end

end RiemannGaussian
