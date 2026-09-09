/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SuzukiCarrierSmoothFlux

/-!
# Independent decay of the complete smoothed Gaussian area combination

Both signed area terms are retained in one complex quantity. The exact
Cauchy--Green identity and the global carrier bound control it by the
three remote rectangle sides; the heat vanishes on the real boundary.
The result holds for every positive smoothing radius and heat time.
It does not exchange the expanding-window limit with removal of the
smoothing, or supply a bound for either area term separately.
-/

open Complex Filter MeasureTheory Real Set Topology
namespace RiemannGaussian
noncomputable section

/-- The two full signed Gaussian area terms, before any norm or
real projection. The entire carrier Wronskian remains in the first. -/
def suzukiXiSmoothBoundaryHeatBulk (r x tau : ℝ) (z : ℂ) : ℂ :=
  suzukiSmoothSpectralBoundaryHeat x tau z * suzukiXiSmoothCarrierSource r z -
    I * suzukiXiSmoothCarrier r z * suzukiChebyshevLaplaceBoundaryHeatCauchyGreenSource x tau (I * z)

/-- The combined area density is continuous even at all genuine
carrier poles and at common xi/denominator zeros. -/
theorem continuous_suzukiXiSmoothBoundaryHeatBulk {r : ℝ} (hr : 0 < r) (x tau : ℝ) :
    Continuous (suzukiXiSmoothBoundaryHeatBulk r x tau) := by
  unfold suzukiXiSmoothBoundaryHeatBulk
  exact ((differentiable_suzukiSmoothSpectralBoundaryHeat x tau).continuous.mul
    (continuous_suzukiXiSmoothCarrierSource hr)).sub
      ((continuous_const.mul (contDiff_suzukiXiSmoothCarrier hr).continuous).mul
        ((continuous_suzukiChebyshevLaplaceBoundaryHeatCauchyGreenSource x tau).comp (by fun_prop)))

private lemma heat_outer_bound {x tau R a y : ℝ} (htau : 0 < tau) (hR : 0 < R)
    (hx : 2 * |x| ≤ R) (hy : y ∈ Icc 0 R) (hedge : y = R ∨ |a| = R) :
    ‖suzukiSmoothSpectralBoundaryHeat x tau ((a : ℂ) + (y : ℂ) * I)‖ ≤
      2 * R * Real.exp (-tau * R ^ 2 / 4) := by
  have hy0 := hy.1
  have hyR := hy.2
  have hdist : R ^ 2 / 4 ≤ (x - a) ^ 2 + y ^ 2 := by
    rcases hedge with he | he
    · rw [he]
      nlinarith [sq_nonneg (x - a), sq_nonneg R]
    · have hh : R / 2 ≤ |x - a| := by
        have ha := abs_sub_abs_le_abs_sub a x
        rw [he, abs_sub_comm a x] at ha
        linarith
      nlinarith [sq_abs (x - a), sq_nonneg y]
  have he : Real.exp (-tau * ((x - a) ^ 2 + y ^ 2)) ≤ Real.exp (-tau * R ^ 2 / 4) := by
    apply Real.exp_le_exp.mpr
    nlinarith
  rw [suzukiSmoothSpectralBoundaryHeat_eq, Complex.norm_real, Real.norm_eq_abs]
  simp only [add_re, ofReal_re, mul_re, ofReal_im, I_re, mul_zero, sub_zero,
    add_zero, add_im, mul_im, I_im, mul_one, zero_add]
  rw [abs_of_nonneg (by positivity)]
  gcongr

/-- The actual bounded carrier times the Gaussian decays on every outer
edge, with both parameters and the full complex field retained. -/
theorem norm_suzukiXiSmoothBoundaryHeat_outer_le {r x tau R a y : ℝ} (hr : 0 < r) (htau : 0 < tau) (hR : 0 < R)
    (hx : 2 * |x| ≤ R) (hy : y ∈ Icc 0 R) (hedge : y = R ∨ |a| = R) :
    ‖suzukiSmoothSpectralBoundaryHeat x tau ((a : ℂ) + (y : ℂ) * I) *
      suzukiXiSmoothCarrier r ((a : ℂ) + (y : ℂ) * I)‖ ≤
      R / r * Real.exp (-tau * R ^ 2 / 4) := by
  rw [norm_mul]
  calc
    _ ≤ (2 * R * Real.exp (-tau * R ^ 2 / 4)) * (1 / (2 * r)) := by
      apply mul_le_mul (heat_outer_bound htau hR hx hy hedge) (norm_suzukiXiSmoothCarrier_le hr _)
        (norm_nonneg _)
      positivity
    _ = _ := by ring

/-- Every finite area integral in the estimate is a genuine integral
of the full continuous signed density, including all interior zeros. -/
theorem integrableOn_suzukiXiSmoothBoundaryHeatBulk_rectangle {r : ℝ} (hr : 0 < r)
    (x tau l v b u : ℝ) :
    IntegrableOn (suzukiXiSmoothBoundaryHeatBulk r x tau) (Icc l v ×ℂ Icc b u) :=
  (continuous_suzukiXiSmoothBoundaryHeatBulk hr x tau).continuousOn.integrableOn_compact
    (isCompact_Icc.reProdIm isCompact_Icc)

/-- An independent Gaussian bound for the complete signed area
combination. No internal pole count, separation or simplicity is assumed. -/
theorem norm_suzukiXiSmoothBoundaryHeatBulk_rectangle_le {r tau R : ℝ}
    (hr : 0 < r) (htau : 0 < tau) (hR : 0 < R) (x : ℝ) (hx : 2 * |x| ≤ R) :
    ‖∫ a : ℝ in (-R)..R, ∫ y : ℝ in 0..R,
      suzukiXiSmoothBoundaryHeatBulk r x tau ((a : ℂ) + (y : ℂ) * I)‖ ≤
        4 * R ^ 2 / r * Real.exp (-tau * R ^ 2 / 4) := by
  let F := fun z => suzukiSmoothSpectralBoundaryHeat x tau z * suzukiXiSmoothCarrier r z
  let B := R / r * Real.exp (-tau * R ^ 2 / 4)
  have htop : ‖∫ a : ℝ in (-R)..R, F ((a : ℂ) + (R : ℂ) * I)‖ ≤ B * (2 * R) := by
    have hh := intervalIntegral.norm_integral_le_of_norm_le_const (a := -R) (b := R)
      (fun a _ha => norm_suzukiXiSmoothBoundaryHeat_outer_le hr htau hR hx ⟨hR.le, le_rfl⟩ (Or.inl rfl) (a := a))
    simpa only [sub_neg_eq_add, ← two_mul R,
      abs_of_pos (show 0 < 2 * R from mul_pos (by norm_num) hR)] using hh
  have hside (v : ℝ) (hv : |v| = R) :
      ‖∫ y : ℝ in 0..R, F ((v : ℂ) + (y : ℂ) * I)‖ ≤ B * R := by
    have hh := intervalIntegral.norm_integral_le_of_norm_le_const (a := (0 : ℝ)) (b := R)
      (fun y hy => norm_suzukiXiSmoothBoundaryHeat_outer_le hr htau hR hx
        (by simpa only [uIcc_of_le hR.le] using uIoc_subset_uIcc hy) (Or.inr hv) (y := y))
    simpa only [sub_zero, abs_of_pos hR] using hh
  have hright := hside R (abs_of_pos hR)
  have hleft := hside (-R) (by simp [abs_of_pos hR])
  have he : (∫ a : ℝ in (-R)..R, ∫ y : ℝ in 0..R,
      suzukiXiSmoothBoundaryHeatBulk r x tau ((a : ℂ) + (y : ℂ) * I)) =
        rectangularBoundaryIntegral (-R) R 0 R F := by
    exact (suzukiXiSmoothCarrier_boundaryHeat_rectangularCauchyGreen hr x tau (-R) R 0 R).symm
  rw [he]
  unfold rectangularBoundaryIntegral
  have hbottom : (∫ a : ℝ in (-R)..R, F ((a : ℂ) + ((0 : ℝ) : ℂ) * I)) = 0 := by
    simp [F]
  rw [hbottom, zero_sub]
  calc
    _ ≤ ‖-(∫ a : ℝ in (-R)..R, F ((a : ℂ) + (R : ℂ) * I)) +
          I * (∫ y : ℝ in 0..R, F ((R : ℂ) + (y : ℂ) * I))‖ +
        ‖I * (∫ y : ℝ in 0..R, F (((-R : ℝ) : ℂ) + (y : ℂ) * I))‖ := by
      exact norm_sub_le _ _
    _ ≤ B * (2 * R) + B * R + B * R := by
      have hh := norm_add_le
        (-(∫ a : ℝ in (-R)..R, F ((a : ℂ) + (R : ℂ) * I)))
        (I * (∫ y : ℝ in 0..R, F ((R : ℂ) + (y : ℂ) * I)))
      simp only [norm_neg, norm_mul, norm_I, one_mul] at hh ⊢
      linarith
    _ = _ := by dsimp [B]; ring

private lemma heat_bound_tendsto {r tau : ℝ} (htau : 0 < tau) :
    Tendsto (fun R : ℝ => 4 * R ^ 2 / r * Real.exp (-tau * R ^ 2 / 4)) atTop (𝓝 0) := by
  have h := (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero 1 (tau / 4)
    (by positivity)).comp (tendsto_pow_atTop (by norm_num : (2 : ℕ) ≠ 0))
  have he : (fun R : ℝ => 4 * R ^ 2 / r * Real.exp (-tau * R ^ 2 / 4)) =
      fun R : ℝ => (4 / r) * ((R ^ 2) ^ (1 : ℝ) * Real.exp (-(tau / 4) * R ^ 2)) := by
    funext R
    rw [Real.rpow_one]
    rw [show -tau * R ^ 2 / 4 = -(tau / 4) * R ^ 2 by ring]
    ring
  rw [he]
  simpa only [Function.comp_def, mul_zero] using h.const_mul (4 / r)

/-- For every fixed positive smoothing radius and heat time, the
complete signed area combination tends to zero on expanding rectangles.
No exchange with the singular zero-radius limit is asserted. -/
theorem tendsto_suzukiXiSmoothBoundaryHeatBulk_rectangle_zero {r tau : ℝ}
    (hr : 0 < r) (htau : 0 < tau) (x : ℝ) :
    Tendsto (fun R : ℝ => ∫ a : ℝ in (-R)..R, ∫ y : ℝ in 0..R,
      suzukiXiSmoothBoundaryHeatBulk r x tau ((a : ℂ) + (y : ℂ) * I)) atTop (𝓝 0) := by
  apply squeeze_zero_norm' _ (heat_bound_tendsto (r := r) htau)
  filter_upwards [eventually_gt_atTop (0 : ℝ), eventually_ge_atTop (2 * |x|)] with R hR hx
  exact norm_suzukiXiSmoothBoundaryHeatBulk_rectangle_le hr htau hR x hx

end
end RiemannGaussian
