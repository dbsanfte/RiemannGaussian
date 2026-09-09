/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SuzukiCarrierSmoothExcision

/-!
# Complete expanding Gaussian reflection area source

The full original reflection weight has a Gaussian-decaying outer
boundary. Combining this with proved geometric excision evaluates the
iterated area limit: its nonzero reflected-node source survives at
every positive smoothing radius. The unweighted Gaussian decay cannot
be applied to this weighted area, and no smoothing limit is exchanged.
-/

open Complex Filter MeasureTheory Set Topology
open scoped Interval
namespace RiemannGaussian
noncomputable section

private lemma weight_top_bound (rho : NontrivialZetaZero) {R : ℝ} (hR : 1 ≤ R) (a : ℝ) :
    ‖suzukiXiReflectionWeight rho ((a : ℂ) + (R : ℂ) * I)‖ ≤
      64 * (zetaSpectralCoordinate rho.1).im ^ 2 := by
  let c := zetaSpectralCoordinate rho.1
  let z : ℂ := (a : ℂ) + (R : ℂ) * I
  have hc : |c.im| < 1 / 2 := NontrivialZetaZero.abs_spectralCoordinate_im_lt_half rho
  have hd : 1 / 2 ≤ ‖z-c‖ := by
    calc
      1 / 2 ≤ R-c.im := by linarith [le_abs_self c.im]
      _ ≤ |R-c.im| := le_abs_self _
      _ ≤ ‖z-c‖ := by simpa [z] using Complex.abs_im_le_norm (z-c)
  have he : 1 / 2 ≤ ‖z-starRingEnd ℂ c‖ := by
    calc
      1 / 2 ≤ R+c.im := by linarith [neg_le_abs c.im]
      _ ≤ |R+c.im| := le_abs_self _
      _ ≤ ‖z-starRingEnd ℂ c‖ := by simpa [z] using Complex.abs_im_le_norm (z-starRingEnd ℂ c)
  have hza : z ≠ c := by intro h; simp [h] at hd; linarith
  have hzb : z ≠ starRingEnd ℂ c := by intro h; simp [h] at he; linarith
  rw [suzukiXiReflectionWeight_eq_quartic rho hza hzb, norm_div, norm_mul, norm_pow, norm_pow,
    norm_mul, Complex.norm_real, Real.norm_eq_abs, sq_abs]
  norm_num only [norm_ofNat]
  calc
    _ ≤ 4 * c.im ^ 2 / (((1 : ℝ)/2) * (1/2)) ^ 2 := by gcongr
    _ = _ := by dsimp [c]; ring

private lemma field_outer_bound (rho : NontrivialZetaZero) {r tau R a y : ℝ}
    (hr : 0 < r) (htau : 0 < tau) (hR : 1 ≤ R) (x : ℝ) (hx : 2 * |x| ≤ R)
    (hc : 2 * |(zetaSpectralCoordinate rho.1).re| ≤ R)
    (hy : y ∈ Icc 0 R) (he : y = R ∨ |a| = R) :
    ‖suzukiXiSmoothReflectionField rho r x tau ((a : ℂ) + (y : ℂ) * I)‖ ≤
      64 * (zetaSpectralCoordinate rho.1).im ^ 2 * (R / r * Real.exp (-tau * R ^ 2 / 4)) := by
  have hR0 : 0 < R := lt_of_lt_of_le (by norm_num) hR
  have hw : ‖suzukiXiReflectionWeight rho ((a : ℂ) + (y : ℂ) * I)‖ ≤
      64 * (zetaSpectralCoordinate rho.1).im ^ 2 := by
    rcases he with he | he
    · rw [he]
      exact weight_top_bound rho hR a
    · calc
        _ ≤ 64 * (zetaSpectralCoordinate rho.1).im ^ 2 / R ^ 4 :=
          norm_suzukiXiReflectionWeight_vertical_le rho hR0 he.ge hc
        _ ≤ _ := div_le_self (by positivity) (one_le_pow₀ hR)
  have hBS := norm_suzukiXiSmoothBoundaryHeat_outer_le hr htau hR0 hx hy he
  have heq : suzukiXiSmoothReflectionField rho r x tau ((a : ℂ) + (y : ℂ) * I) =
      suzukiXiReflectionWeight rho ((a : ℂ) + (y : ℂ) * I) *
        (suzukiSmoothSpectralBoundaryHeat x tau ((a : ℂ) + (y : ℂ) * I) *
          suzukiXiSmoothCarrier r ((a : ℂ) + (y : ℂ) * I)) := by
    unfold suzukiXiSmoothReflectionField
    ring
  rw [heq, norm_mul]
  exact mul_le_mul hw hBS (norm_nonneg _) (by positivity)

/-- A coarse independent Gaussian bound for the full reflection-weighted
outer boundary. The reflected node and all genuine carrier poles may
lie inside the rectangle. -/
theorem norm_suzukiXiSmoothReflectionField_boundary_le (rho : NontrivialZetaZero)
    {r tau R : ℝ} (hr : 0 < r) (htau : 0 < tau) (hR : 1 ≤ R) (x : ℝ)
    (hx : 2 * |x| ≤ R) (hc : 2 * |(zetaSpectralCoordinate rho.1).re| ≤ R) :
    ‖rectangularBoundaryIntegral (-R) R 0 R (suzukiXiSmoothReflectionField rho r x tau)‖ ≤
      384 * (zetaSpectralCoordinate rho.1).im ^ 2 * R ^ 2 / r * Real.exp (-tau * R ^ 2 / 4) := by
  let M := 64 * (zetaSpectralCoordinate rho.1).im ^ 2 * (R / r * Real.exp (-tau * R ^ 2 / 4))
  have hR0 : 0 < R := lt_of_lt_of_le (by norm_num) hR
  have hn := norm_rectangularBoundaryIntegral_le_of_norm_le_const
    (l := -R) (r := R) (b := 0) (u := R) (C := M)
    (f := suzukiXiSmoothReflectionField rho r x tau)
    (fun a _ => by simp [suzukiXiSmoothReflectionField]; dsimp [M]; positivity)
    (fun a _ => field_outer_bound rho hr htau hR x hx hc ⟨hR0.le, le_rfl⟩ (Or.inl rfl))
    (fun y hy => field_outer_bound rho hr htau hR x hx hc
      (by simpa only [uIcc_of_le hR0.le] using uIoc_subset_uIcc hy) (Or.inr (abs_of_pos hR0)))
    (fun y hy => field_outer_bound rho hr htau hR x hx hc
      (by simpa only [uIcc_of_le hR0.le] using uIoc_subset_uIcc hy)
      (Or.inr (by simp [abs_of_pos hR0])))
  calc
    _ ≤ M * |R - -R| + M * |R - -R| + M * |R - 0| + M * |R - 0| := hn
    _ = _ := by
      rw [sub_neg_eq_add, ← two_mul R, abs_of_pos (show 0 < 2*R by positivity), sub_zero, abs_of_pos hR0]
      dsimp [M]
      ring

/-- For fixed positive smoothing radius and heat time, the complete
original reflection-weighted outer boundary tends to zero. -/
theorem tendsto_suzukiXiSmoothReflectionField_boundary_zero (rho : NontrivialZetaZero)
    {r tau : ℝ} (hr : 0 < r) (htau : 0 < tau) (x : ℝ) :
    Tendsto (fun R : ℝ => rectangularBoundaryIntegral (-R) R 0 R
      (suzukiXiSmoothReflectionField rho r x tau)) atTop (𝓝 0) := by
  have h := (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero 1 (tau / 4)
    (by positivity)).comp (tendsto_pow_atTop (by norm_num : (2 : ℕ) ≠ 0))
  have he : Tendsto (fun R : ℝ => 384 * (zetaSpectralCoordinate rho.1).im ^ 2 * R ^ 2 / r *
      Real.exp (-tau * R ^ 2 / 4)) atTop (𝓝 0) := by
    have hh := h.const_mul (384 * (zetaSpectralCoordinate rho.1).im ^ 2 / r)
    simp only [Function.comp_def, Real.rpow_one, mul_zero] at hh
    convert hh using 1
    funext R
    rw [show -tau * R ^ 2 / 4 = -(tau / 4) * R ^ 2 by ring]
    ring
  apply squeeze_zero_norm' _ he
  filter_upwards [eventually_ge_atTop (1 : ℝ), eventually_ge_atTop (2*|x|),
    eventually_ge_atTop (2*|(zetaSpectralCoordinate rho.1).re|)] with R hR hx hc
  exact norm_suzukiXiSmoothReflectionField_boundary_le rho hr htau hR x hx hc

/-- The complete geometric area has the original nonzero node source
in the expanding half-plane. The inner square shrinks first; no exchange
of limits, no zero-smoothing limit, and no sign estimate of an individual
area term is used. -/
theorem tendsto_suzukiXiSmoothReflectionSource_iterated_area
    (rho : NontrivialZetaZero) (hzero : 1 / 2 < rho.1.re) {r tau : ℝ}
    (hr : 0 < r) (htau : 0 < tau) (x : ℝ) :
    Tendsto (fun R : ℝ => Filter.limUnder (𝓝[>] (0 : ℝ))
      (fun q : ℝ => rectangularAreaIntegralOutsideCenteredSquare (-R) R 0 R
        (starRingEnd ℂ (zetaSpectralCoordinate rho.1)) q (suzukiXiSmoothReflectionSource rho r x tau)))
      atTop (𝓝 ((2 * Real.pi * I) * ((analyticZetaZeroMultiplicity rho : ℂ)⁻¹ *
        suzukiSmoothSpectralBoundaryHeat x tau (starRingEnd ℂ (zetaSpectralCoordinate rho.1))))) := by
  let c := starRingEnd ℂ (zetaSpectralCoordinate rho.1)
  let L := (2 * Real.pi * I) * ((analyticZetaZeroMultiplicity rho : ℂ)⁻¹ *
    suzukiSmoothSpectralBoundaryHeat x tau c)
  have ht : Tendsto (fun R : ℝ => rectangularBoundaryIntegral (-R) R 0 R
      (suzukiXiSmoothReflectionField rho r x tau) + L) atTop (𝓝 L) := by
    simpa only [zero_add] using (tendsto_suzukiXiSmoothReflectionField_boundary_zero rho hr htau x).add_const L
  apply ht.congr'
  filter_upwards [eventually_gt_atTop |c.re|, eventually_gt_atTop c.im] with R hRe hIm
  have hc : 0 < c.im := by
    dsimp [c]
    rw [zetaSpectralCoordinate_im]
    linarith
  exact (tendsto_area_suzukiXiSmoothReflectionSource rho hzero hr x tau (-R) R 0 R le_rfl
    (by linarith [neg_le_abs c.re]) (lt_of_le_of_lt (le_abs_self c.re) hRe) hc hIm).limUnder_eq.symm

/-- The surviving complete area source has strictly positive imaginary
part at every hypothetical right-half zero. Its true analytic multiplicity
and the moving Gaussian value are retained. -/
theorem suzukiXiSmoothReflectionSource_mass_im_pos
    (rho : NontrivialZetaZero) (hzero : 1 / 2 < rho.1.re) (x tau : ℝ) :
    0 < ((2 * Real.pi * I) * ((analyticZetaZeroMultiplicity rho : ℂ)⁻¹ *
      suzukiSmoothSpectralBoundaryHeat x tau (starRingEnd ℂ (zetaSpectralCoordinate rho.1)))).im := by
  have hm : 0 < (analyticZetaZeroMultiplicity rho : ℝ) :=
    Nat.cast_pos.mpr (analyticZetaZeroMultiplicity_positive rho)
  have hc : 0 < (starRingEnd ℂ (zetaSpectralCoordinate rho.1)).im := by
    rw [conj_im, zetaSpectralCoordinate_im]
    linarith
  rw [show (analyticZetaZeroMultiplicity rho : ℂ) = ((analyticZetaZeroMultiplicity rho : ℝ) : ℂ) by simp,
    ← ofReal_inv, suzukiSmoothSpectralBoundaryHeat_eq]
  simp only [mul_im, mul_re, ofReal_re, ofReal_im, re_ofNat, im_ofNat, I_re, I_im,
    mul_zero, zero_mul, mul_one, add_zero, zero_add, sub_zero]
  positivity

end
end RiemannGaussian
