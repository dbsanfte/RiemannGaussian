/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaEulerMaclaurinEnclosure
import RiemannGaussian.ZetaEulerTruncation
import RiemannGaussian.AnalyticNewtonIsolation
import Mathlib.NumberTheory.LSeries.HurwitzZetaValues

/-!
# Analytic error budget for the zeta derivative at two

A Cauchy estimate on a disc wholly in the absolute-convergence half-plane
bounds the actual second derivative. The proved Euler--Maclaurin remainder
and a tiny imaginary displacement then control a real derivative sample.
No zero-location or prime-density estimate is assumed.
-/

open Complex Metric Set
namespace RiemannGaussian.RosserSchoenfeldZetaTwoBudget
noncomputable section

/-- Real-part and norm bounds on the outer Cauchy disc. -/
private lemma geometry {s : ℂ} (hs : s ∈ closedBall (2 : ℂ) (1/2 : ℝ)) :
    (3/2 : ℝ) ≤ s.re ∧ ‖s‖ ≤ 3 := by
  have hn := mem_closedBall_iff_norm.mp hs
  have hr := (Complex.abs_re_le_norm (s-2)).trans hn
  have hh := norm_add_le (s-2) (2 : ℂ)
  rw [sub_add_cancel] at hh
  norm_num [Complex.sub_re] at hr
  norm_num at hh
  constructor
  · linarith [(abs_le.mp hr).1]
  · linarith

/-- The literal Euler truncation bounds zeta throughout the outer disc. -/
private lemma bound {s : ℂ} (hs : s ∈ closedBall (2 : ℂ) (1/2 : ℝ)) :
    s ≠ 1 ∧ ‖riemannZeta s‖ ≤ 5 := by
  obtain ⟨hr, hn⟩ := geometry hs
  have hs0 : 0 < s.re := by linarith
  have hsne : s ≠ 1 := by intro he; norm_num [he] at hr
  refine ⟨hsne, ?_⟩
  have he := ZetaEulerTruncation.norm_zeta_sub_partialSum_le hs0 hsne (N:=1) (by norm_num)
  norm_num [ZetaEulerCell.partialSum] at he
  have hd : (1/2 : ℝ) ≤ ‖s-1‖ := by
    have hh := Complex.re_le_norm (s-1)
    norm_num at hh
    linarith
  have hp : (2 : ℝ)^(1-s.re) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by linarith)
  have hq : (2 : ℝ)^(1-s.re) / ‖s-1‖ ≤ 2 := by
    apply (div_le_iff₀ (by linarith : 0 < ‖s-1‖)).mpr
    linarith
  have hq' : ‖s‖/s.re ≤ 2 := (div_le_iff₀ hs0).mpr (by linarith)
  have hh := norm_add_le (riemannZeta s-1) (1 : ℂ)
  rw [sub_add_cancel] at hh
  norm_num at hh
  linarith

/-- The outer disc avoids the unique zeta pole. -/
private lemma analytic : AnalyticOnNhd ℂ riemannZeta (closedBall (2 : ℂ) (1/2 : ℝ)) := by
  have hd : DifferentiableOn ℂ riemannZeta ({1}ᶜ : Set ℂ) := by
    intro z hz
    exact (differentiableAt_riemannZeta (by simpa using hz)).differentiableWithinAt
  intro s hs
  exact hd.analyticOnNhd isOpen_compl_singleton s (by simpa using (bound hs).1)

/-- Cauchy bounds the actual second derivative on the inner disc. -/
private lemma second {s : ℂ} (hs : s ∈ closedBall (2 : ℂ) (1/4 : ℝ)) :
    ‖deriv (deriv riemannZeta) s‖ ≤ 160 := by
  have hsub : closedBall s (1/4 : ℝ) ⊆ closedBall (2 : ℂ) (1/2 : ℝ) := by
    intro z hz
    apply mem_closedBall.mpr
    have hh := dist_triangle z s (2 : ℂ)
    have hz' := mem_closedBall.mp hz
    have hs' := mem_closedBall.mp hs
    linarith
  have hf := (analytic.mono hsub).differentiableOn
  have hh := Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le 2
    (by norm_num : (0 : ℝ) < 1/4)
    ((hf.mono closure_ball_subset_closedBall).diffContOnCl)
    (fun z hz => (bound (hsub (sphere_subset_closedBall hz))).2)
  norm_num [iteratedDeriv_succ, iteratedDeriv_zero, Nat.factorial] at hh
  exact hh

/-- The complete Euler--Maclaurin tail is smaller than the sample budget. -/
theorem error {s : ℂ} (hr : s.re = 2) (hn : ‖s‖ ≤ 3) :
    ‖riemannZeta s-ZetaEulerMaclaurin.approximation 64 s 18‖ < (1/10^25 : ℝ) := by
  have hsne : s ≠ 1 := by intro he; norm_num [he] at hr
  have hh := ZetaEulerMaclaurin.norm_error_le (by rw [hr]; norm_num) hsne 64 18
  have hb := ZetaEulerMaclaurin.norm_rising_le hn 20
  have ha := ZetaEulerMaclaurinBudget.allowance_twenty
  norm_num at hb
  have hm := mul_le_mul_of_nonneg_right hb (ZetaEulerMaclaurinKernel.allowance_nonneg 20)
  have hm' := mul_lt_mul_of_pos_left ha (by norm_num : (0 : ℝ) < 23^20)
  have hp : (65 : ℝ)^(-(21 : ℝ))=1/65^21 := by norm_num [Real.rpow_neg]
  norm_num [hr, hp] at hh
  nlinarith


/-- Positive rational height of the imaginary derivative sample. -/
def height : ℝ := 1/10^12
/-- The exact point used in the derivative sample. -/
def point : ℂ := 2 + (height : ℂ)*Complex.I

/-- The sample lies on the line of real part two and has bounded norm. -/
theorem point_geometry : point.re=2 ∧ ‖point‖ ≤ 3 := by
  constructor
  · norm_num [point]
  · have hh := norm_add_le (2 : ℂ) ((height : ℂ)*Complex.I)
    norm_num [height, point, norm_mul] at *
    linarith

/-- The imaginary sample retains the real derivative, with quadratic error. -/
theorem step_bound : |(riemannZeta point).im - height*(deriv riemannZeta 2).re| ≤
    160*height^2 := by
  have hh0 : 0 ≤ height := by norm_num [height]
  have hn : ‖(height : ℂ)*Complex.I‖ = height := by simp [abs_of_nonneg hh0]
  have hz : point ∈ closedBall (2 : ℂ) height := by
    simpa only [point, mem_closedBall_iff_norm, add_sub_cancel_left, hn] using le_refl height
  have hsub : closedBall (2 : ℂ) height ⊆ closedBall (2 : ℂ) (1/4 : ℝ) :=
    closedBall_subset_closedBall (by norm_num [height])
  have hf := analytic.mono (hsub.trans (closedBall_subset_closedBall (by norm_num : (1/4 : ℝ) ≤ 1/2)))
  have he := AnalyticNewtonIsolation.affine_error hh0 (by norm_num : (0 : ℝ) ≤ 160)
    hf (fun w hw => second (hsub hw)) hz
  simp only [point, add_sub_cancel_left, hn] at he
  have him := (Complex.abs_im_le_norm _).trans he
  have hz2 : (riemannZeta (2 : ℂ)).im = 0 := by norm_num [riemannZeta_two, pow_two, Complex.mul_im]
  convert him using 1 <;> norm_num [point, Complex.sub_im, Complex.mul_im, Complex.mul_re, hz2] <;> first | rfl | ring_nf

end
end RiemannGaussian.RosserSchoenfeldZetaTwoBudget
