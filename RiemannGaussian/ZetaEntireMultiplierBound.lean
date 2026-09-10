/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaMoebiusPoleJetFilter
import RiemannGaussian.ZetaCenteredEulerZeroFree

/-!
# Moment bounds for bounded entire multipliers of zeta and its derivative

At every actual nontrivial zero ordinate, a unit Cauchy circle centered
at `3/2+i*y` avoids the pole at one and stays in `Re s ≥ 1/2`.
Two entire multipliers bounded on that half-plane therefore give a moment
bound independent of moment order. Finite Dirichlet prefixes will provide
the actual multipliers and their independent bounds.
-/

open Complex Filter Metric Set Topology
open scoped Classical

namespace RiemannGaussian

noncomputable section

private theorem unit_ball_re (y : ℝ) {s : ℂ}
    (hs : s ∈ closedBall (3 / 2 + I * (y : ℂ)) 1) : 1 / 2 ≤ s.re := by
  have hn := mem_closedBall_iff_norm.mp hs
  have hr := (Complex.abs_re_le_norm (s - (3 / 2 + I * (y : ℂ)))).trans hn
  norm_num at hr
  linarith [(abs_le.mp hr).1]

private theorem unit_ball_ne_one {y : ℝ} (hy : 1 < |y|) {s : ℂ}
    (hs : s ∈ closedBall (3 / 2 + I * (y : ℂ)) 1) : s ≠ 1 := by
  intro he
  have hn := mem_closedBall_iff_norm.mp hs
  have hi := (Complex.abs_im_le_norm (s - (3 / 2 + I * (y : ℂ)))).trans hn
  norm_num [he] at hi
  linarith

/-- One ordinate-dependent constant controls every moment of every
eligible pair of entire multipliers. The two multiplier budgets stay separate. -/
theorem exists_zetaEntireMultiplier_moment_bound (y : ℝ) (hy : 1 < |y|) :
    ∃ C : ℝ, 0 < C ∧ ∀ (f g : ℂ → ℂ), Differentiable ℂ f → Differentiable ℂ g →
      ∀ A B : ℝ, 0 ≤ A → 0 ≤ B →
      (∀ s : ℂ, 1 / 2 ≤ s.re → ‖f s‖ ≤ A) →
      (∀ s : ℂ, 1 / 2 ≤ s.re → ‖g s‖ ≤ B) →
      ∀ N : ℕ, ‖signedTaylorMoment N
        (fun s ↦ f s * (-deriv riemannZeta s) + g s * riemannZeta s)
        (3 / 2 + I * y)‖ ≤ C * (A + B) := by
  let c : ℂ := 3 / 2 + I * y
  have hz : AnalyticOnNhd ℂ riemannZeta (closedBall c 1) := by
    intro s hs
    exact analyticOn_riemannZeta s (by simpa using unit_ball_ne_one hy hs)
  have hdz : AnalyticOnNhd ℂ (deriv riemannZeta) (closedBall c 1) :=
    fun s hs ↦ (hz s hs).deriv
  have hc : ContinuousOn (fun s ↦ ‖riemannZeta s‖ + ‖deriv riemannZeta s‖) (closedBall c 1) :=
    hz.continuousOn.norm.add hdz.continuousOn.norm
  obtain ⟨M, hM⟩ := ((isCompact_closedBall c 1).image_of_continuousOn hc).isBounded.exists_norm_le
  have hM0 : 0 ≤ M := (norm_nonneg _).trans
    (hM _ ⟨c, mem_closedBall_self (by norm_num), rfl⟩)
  refine ⟨M + 1, by linarith, ?_⟩
  intro f g hf hg A B hA hB hfB hgB N
  have ha : AnalyticOnNhd ℂ
      (fun s ↦ f s * (-deriv riemannZeta s) + g s * riemannZeta s) (closedBall c 1) :=
    fun s hs ↦ ((hf.analyticAt (z := s)).mul (hdz s hs).neg).add
      ((hg.analyticAt (z := s)).mul (hz s hs))
  have hd : DiffContOnCl ℂ
      (fun s ↦ f s * (-deriv riemannZeta s) + g s * riemannZeta s) (ball c 1) := by
    apply DifferentiableOn.diffContOnCl
    rw [closure_ball _ (by norm_num : (1 : ℝ) ≠ 0)]
    exact ha.differentiableOn
  have hb (s : ℂ) (hs : s ∈ sphere c 1) :
      ‖f s * (-deriv riemannZeta s) + g s * riemannZeta s‖ ≤ (M + 1) * (A + B) := by
    have hsB := sphere_subset_closedBall hs
    have hbound := hM _ ⟨s, hsB, rfl⟩
    rw [Real.norm_of_nonneg (add_nonneg (norm_nonneg _) (norm_nonneg _))] at hbound
    have hzr : ‖riemannZeta s‖ ≤ M + 1 := by linarith [norm_nonneg (deriv riemannZeta s)]
    have hzdr : ‖deriv riemannZeta s‖ ≤ M + 1 := by linarith [norm_nonneg (riemannZeta s)]
    apply (norm_add_le _ _).trans
    rw [norm_mul, norm_neg, norm_mul]
    have h1 := mul_le_mul (hfB s (unit_ball_re y hsB)) hzdr
      (norm_nonneg _) hA
    have h2 := mul_le_mul (hgB s (unit_ball_re y hsB)) hzr
      (norm_nonneg _) hB
    nlinarith
  simpa only [one_pow, div_one] using norm_signedTaylorMoment_le (by norm_num) hd hb N

/-- Every polynomial filter inherits the same moment-order-independent
bound. No pole cancellation or sign assumption on its coefficients is needed. -/
theorem exists_zetaEntireMultiplier_filter_bound (y : ℝ) (hy : 1 < |y|) :
    ∃ C : ℝ, 0 < C ∧ ∀ (f g : ℂ → ℂ), Differentiable ℂ f → Differentiable ℂ g →
      ∀ A B : ℝ, 0 ≤ A → 0 ≤ B →
      (∀ s : ℂ, 1 / 2 ≤ s.re → ‖f s‖ ≤ A) →
      (∀ s : ℂ, 1 / 2 ≤ s.re → ‖g s‖ ≤ B) →
      ∀ (p : Polynomial ℂ) (N : ℕ),
        ‖zetaMomentSequenceFilter p (fun k ↦ signedTaylorMoment k
          (fun s ↦ f s * (-deriv riemannZeta s) + g s * riemannZeta s)
          (3 / 2 + I * y)) N‖ ≤ C * (A + B) * ∑ k ∈ p.support, ‖p.coeff k‖ := by
  obtain ⟨C, hC, hbound⟩ := exists_zetaEntireMultiplier_moment_bound y hy
  refine ⟨C, hC, ?_⟩
  intro f g hf hg A B hA hB hfB hgB p N
  rw [zetaMomentSequenceFilter, Polynomial.sum]
  apply (norm_sum_le _ _).trans
  calc
    _ ≤ ∑ k ∈ p.support, ‖p.coeff k‖ * (C * (A + B)) := by
      apply Finset.sum_le_sum
      intro k _
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_left (hbound f g hf hg A B hA hB hfB hgB (N + k)) (norm_nonneg _)
    _ = _ := by rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro k _; ring

end
end RiemannGaussian
