/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaEntireMultiplierBound

/-!
# Variable Cauchy radii for the genuine two-channel zeta response

One ordinate-dependent constant works for every positive radius at most
one. A radius below one leaves a positive margin to real part one half,
so square-divisor overlap sums can converge while the exact signed entire
multipliers of zeta and its derivative remain available. The polynomial
filter keeps its complete radius-weighted coefficient norm.
-/

open Complex Filter Metric Set Topology
open scoped Classical

namespace RiemannGaussian
noncomputable section

private theorem ball_re (y r : ℝ) {s : ℂ}
    (hs : s ∈ closedBall (3 / 2 + I * (y : ℂ)) r) : 3 / 2 - r ≤ s.re := by
  have hr := (Complex.abs_re_le_norm (s - (3 / 2 + I * (y : ℂ)))).trans
    (mem_closedBall_iff_norm.mp hs)
  norm_num at hr
  linarith [(abs_le.mp hr).1]

private theorem ball_ne_one {y : ℝ} (hy : 1 < |y|) {s : ℂ}
    (hs : s ∈ closedBall (3 / 2 + I * (y : ℂ)) 1) : s ≠ 1 := by
  intro he
  have hi := (Complex.abs_im_le_norm (s - (3 / 2 + I * (y : ℂ)))).trans
    (mem_closedBall_iff_norm.mp hs)
  norm_num [he] at hi
  linarith

/-- Every Cauchy radius at most one has the same zeta-dependent
constant. The genuine entire multiplier budgets need hold only on the
half-plane reached by that radius, and the moment pays exactly `r⁻¹^N`. -/
theorem exists_zetaEntireMultiplier_radius_moment_bound (y : ℝ) (hy : 1 < |y|) :
    ∃ C : ℝ, 0 < C ∧ ∀ r : ℝ, 0 < r → r ≤ 1 →
      ∀ (f g : ℂ → ℂ), Differentiable ℂ f → Differentiable ℂ g →
      ∀ A B : ℝ, 0 ≤ A → 0 ≤ B →
      (∀ s : ℂ, 3 / 2 - r ≤ s.re → ‖f s‖ ≤ A) →
      (∀ s : ℂ, 3 / 2 - r ≤ s.re → ‖g s‖ ≤ B) →
      ∀ N : ℕ, ‖signedTaylorMoment N
        (fun s ↦ f s * (-deriv riemannZeta s) + g s * riemannZeta s)
        (3 / 2 + I * y)‖ ≤ C * (A + B) * r⁻¹ ^ N := by
  let c : ℂ := 3 / 2 + I * y
  have hz : AnalyticOnNhd ℂ riemannZeta (closedBall c 1) := by
    intro s hs
    exact analyticOn_riemannZeta s (by simpa using ball_ne_one hy hs)
  have hdz : AnalyticOnNhd ℂ (deriv riemannZeta) (closedBall c 1) :=
    fun s hs ↦ (hz s hs).deriv
  have hc : ContinuousOn (fun s ↦ ‖riemannZeta s‖ + ‖deriv riemannZeta s‖) (closedBall c 1) :=
    hz.continuousOn.norm.add hdz.continuousOn.norm
  obtain ⟨M, hM⟩ := ((isCompact_closedBall c 1).image_of_continuousOn hc).isBounded.exists_norm_le
  have hM0 : 0 ≤ M := (norm_nonneg _).trans
    (hM _ ⟨c, mem_closedBall_self (by norm_num), rfl⟩)
  refine ⟨M + 1, by linarith, ?_⟩
  intro r hr hr1 f g hf hg A B hA hB hfB hgB N
  have hsub : closedBall c r ⊆ closedBall c 1 := closedBall_subset_closedBall hr1
  have ha : AnalyticOnNhd ℂ
      (fun s ↦ f s * (-deriv riemannZeta s) + g s * riemannZeta s) (closedBall c r) :=
    fun s hs ↦ ((hf.analyticAt (z := s)).mul (hdz s (hsub hs)).neg).add
      ((hg.analyticAt (z := s)).mul (hz s (hsub hs)))
  have hd : DiffContOnCl ℂ
      (fun s ↦ f s * (-deriv riemannZeta s) + g s * riemannZeta s) (ball c r) := by
    apply DifferentiableOn.diffContOnCl
    rw [closure_ball _ hr.ne']
    exact ha.differentiableOn
  have hb (s : ℂ) (hs : s ∈ sphere c r) :
      ‖f s * (-deriv riemannZeta s) + g s * riemannZeta s‖ ≤ (M + 1) * (A + B) := by
    have hsB := sphere_subset_closedBall hs
    have hbound := hM _ ⟨s, hsub hsB, rfl⟩
    rw [Real.norm_of_nonneg (add_nonneg (norm_nonneg _) (norm_nonneg _))] at hbound
    have hzr : ‖riemannZeta s‖ ≤ M + 1 := by linarith [norm_nonneg (deriv riemannZeta s)]
    have hzdr : ‖deriv riemannZeta s‖ ≤ M + 1 := by linarith [norm_nonneg (riemannZeta s)]
    apply (norm_add_le _ _).trans
    rw [norm_mul, norm_neg, norm_mul]
    have h1 := mul_le_mul (hfB s (ball_re y r hsB)) hzdr (norm_nonneg _) hA
    have h2 := mul_le_mul (hgB s (ball_re y r hsB)) hzr (norm_nonneg _) hB
    nlinarith
  simpa only [c, div_eq_mul_inv, inv_pow] using norm_signedTaylorMoment_le hr hd hb N

/-- Every polynomial filter inherits the exact radius cost, with all
complex coefficients retained and no pole-jet hypothesis imposed. -/
theorem exists_zetaEntireMultiplier_radius_filter_bound (y : ℝ) (hy : 1 < |y|) :
    ∃ C : ℝ, 0 < C ∧ ∀ r : ℝ, 0 < r → r ≤ 1 →
      ∀ (f g : ℂ → ℂ), Differentiable ℂ f → Differentiable ℂ g →
      ∀ A B : ℝ, 0 ≤ A → 0 ≤ B →
      (∀ s : ℂ, 3 / 2 - r ≤ s.re → ‖f s‖ ≤ A) →
      (∀ s : ℂ, 3 / 2 - r ≤ s.re → ‖g s‖ ≤ B) →
      ∀ (p : Polynomial ℂ) (N : ℕ),
        ‖zetaMomentSequenceFilter p (fun k ↦ signedTaylorMoment k
          (fun s ↦ f s * (-deriv riemannZeta s) + g s * riemannZeta s)
          (3 / 2 + I * y)) N‖ ≤
        C * (A + B) * r⁻¹ ^ N * ∑ k ∈ p.support, ‖p.coeff k‖ * r⁻¹ ^ k := by
  obtain ⟨C, hC, hb⟩ := exists_zetaEntireMultiplier_radius_moment_bound y hy
  refine ⟨C, hC, ?_⟩
  intro r hr hr1 f g hf hg A B hA hB hfB hgB p N
  rw [zetaMomentSequenceFilter, Polynomial.sum]
  apply (norm_sum_le _ _).trans
  calc
    _ ≤ ∑ k ∈ p.support, ‖p.coeff k‖ * (C * (A + B) * r⁻¹ ^ (N + k)) := by
      apply Finset.sum_le_sum
      intro k _
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_left (hb r hr hr1 f g hf hg A B hA hB hfB hgB (N + k)) (norm_nonneg _)
    _ = _ := by
      simp_rw [pow_add, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro k _
      ring

end
end RiemannGaussian
