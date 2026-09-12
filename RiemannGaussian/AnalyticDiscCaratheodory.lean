/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import Mathlib.Analysis.Complex.BorelCaratheodory

/-!
# Sharp center derivative control from a one-sided real-part bound

The Schwarz transform `f / (2*M-f)` retains the complete complex derivative.
Applying Schwarz directly at the center gives the classical Carathéodory
constant `2`, without first taking a maximum on a smaller auxiliary circle.
The radius is arbitrary, including radii shrinking along another parameter.
-/

namespace RiemannGaussian.AnalyticDiscCaratheodory
noncomputable section
open Complex Metric Set

/-- A normalized holomorphic function with real part at most `M` on a
disc has center derivative bounded by `2*M/R`. The hypothesis is one-sided;
no bound on the imaginary part or the function's norm is required. -/
theorem norm_deriv_zero_le {f : ℂ → ℂ} {M R : ℝ} (hM : 0 < M) (hR : 0 < R)
    (hf : DifferentiableOn ℂ f (ball 0 R)) (hreal : ∀ z ∈ ball 0 R, (f z).re ≤ M)
    (hzero : f 0 = 0) : ‖deriv f 0‖ ≤ 2 * M / R := by
  let w : ℂ → ℂ := fun z ↦ f z / (2 * (M : ℂ) - f z)
  have hden : ∀ z ∈ ball (0 : ℂ) R, 2 * (M : ℂ) - f z ≠ 0 := by
    intro z hz he
    have hr := hreal z hz
    have he' := congrArg Complex.re (sub_eq_zero.mp he)
    norm_num at he'
    linarith
  have hw : DifferentiableOn ℂ w (ball 0 R) :=
    hf.div (hf.const_sub _) hden
  have hwzero : w 0 = 0 := by simp [w, hzero]
  have hmaps : MapsTo w (ball 0 R) (closedBall (w 0) 1) := by
    intro z hz
    rw [hwzero, mem_closedBall, dist_zero_right]
    change ‖f z / (2 * (M : ℂ) - f z)‖ ≤ 1
    rw [norm_div]
    apply div_le_one_of_le₀ _ (norm_nonneg _)
    rw [← sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)]
    have hr := hreal z hz
    simp only [Complex.sq_norm, Complex.normSq_apply, Complex.sub_re,
      Complex.sub_im]
    norm_num
    nlinarith
  have hs := Complex.norm_deriv_le_div_of_mapsTo_ball hw hmaps hR
  have hf0 := (hf 0 (mem_ball_self hR)).differentiableAt (isOpen_ball.mem_nhds
    (mem_ball_self hR))
  have hd := hf0.hasDerivAt.div (hf0.hasDerivAt.const_sub (2 * (M : ℂ)))
    (hden 0 (mem_ball_self hR))
  have hwd : deriv w 0 = deriv f 0 / (2 * (M : ℂ)) := by
    change deriv (f / fun z ↦ 2 * (M : ℂ) - f z) 0 = _
    rw [hd.deriv]
    simp only [hzero, sub_zero, zero_mul, sub_zero]
    field_simp
  rw [hwd, norm_div, norm_mul, Complex.norm_ofNat, Complex.norm_real,
    Real.norm_eq_abs, abs_of_pos hM] at hs
  have h := (div_le_iff₀ (by positivity : 0 < 2 * M)).mp hs
  exact h.trans_eq (by ring)

end
end RiemannGaussian.AnalyticDiscCaratheodory
