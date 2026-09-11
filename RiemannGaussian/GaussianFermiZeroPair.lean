/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.FermiLaplaceReflection
import RiemannGaussian.GaussianMellinVertical
import RiemannGaussian.ZetaPoleReserveBootstrap

/-!
# Ideal Gaussian Fermi weights for reflected zeta zeros

Every positive Gaussian scale discharges the all-window reflection theorem.
The actual proved zero-free region then supplies the reflection-strip
hypotheses for each genuine zero. No new numerical zero-free constant or
prime-tail cancellation is assumed or claimed here.
-/

namespace RiemannGaussian.GaussianFermiZeroPair

noncomputable section
open Complex Filter MeasureTheory Set
open scoped Topology
open FermiLaplaceReflection

/-- The full even Gaussian window at an arbitrary positive scale. -/
def window (b : ℝ) (t : ℝ) : ℝ := Real.exp (-b * t ^ 2)

/-- The Gaussian window is continuous at every real argument. -/
theorem continuous_window (b : ℝ) : Continuous (window b) := by
  unfold window
  fun_prop

/-- Reflection preserves the full Gaussian window. -/
theorem even_window (b : ℝ) : Function.Even (window b) := by
  intro t
  simp [window]

/-- Every real exponential moment exists, including negative damping. -/
theorem integrable_window_exp {b : ℝ} (hb : 0 < b) (x : ℝ) :
    Integrable (fun t : ℝ => window b t * Real.exp (-x * t)) := by
  have hc := (integrable_cexp_quadratic' (b := -(b : ℂ))
    (by simpa using neg_neg_of_pos hb) (-(x : ℂ)) 0).norm
  apply hc.congr
  filter_upwards with t
  simp [Complex.norm_exp, ← Complex.ofReal_pow, window, ← Real.exp_add]

/-- The unsmoothed Gaussian boundary signal has its original complex
integrability, independently of any reflection estimate. -/
theorem integrable_boundary {b : ℝ} (hb : 0 < b) (y : ℝ) :
    Integrable (fun t : ℝ => (window b t : ℂ) *
      Complex.exp (-((y : ℂ) * I) * (t : ℂ))) := by
  have hc := integrable_gaussianMellin_vertical (-y) 0 hb
  apply hc.congr
  filter_upwards with t
  rw [window, Complex.ofReal_exp, ← Complex.exp_add]
  congr 1
  push_cast
  ring_nf
  simp [Complex.I_sq, sub_eq_add_neg]

/-- The exact Gaussian Fourier value supplies boundary positivity at every
frequency, with no numerical certificate or frequency cutoff. -/
theorem integral_boundary {b : ℝ} (hb : 0 < b) (y : ℝ) :
    (∫ t : ℝ, (window b t : ℂ) * Complex.exp (-((y : ℂ) * I) * (t : ℂ))) =
      ((Real.sqrt (Real.pi / b) * Real.exp (-y ^ 2 / (4 * b)) : ℝ) : ℂ) := by
  have hc := integral_gaussianMellin_vertical (-y) 0 hb
  rw [neg_sq] at hc
  rw [← hc]
  apply integral_congr_ae
  filter_upwards with t
  rw [window, Complex.ofReal_exp, ← Complex.exp_add]
  congr 1
  push_cast
  ring_nf
  simp [Complex.I_sq]

/-- The half-line cosine transform is exactly half the positive full
Gaussian transform. -/
theorem integral_half_boundary_re {b : ℝ} (hb : 0 < b) (y : ℝ) :
    (∫ t in Ioi (0 : ℝ), (window b t : ℂ) *
      Complex.exp (-((y : ℂ) * I) * (t : ℂ))).re =
      Real.sqrt (Real.pi / b) * Real.exp (-y ^ 2 / (4 * b)) / 2 := by
  let k : ℝ → ℂ := fun t => (window b t : ℂ) *
    Complex.exp (-((y : ℂ) * I) * (t : ℂ))
  have hint : Integrable k := integrable_boundary hb y
  have habs (t : ℝ) : (k |t|).re = (k t).re := by
    dsimp [k, window]
    simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul,
      sub_zero, Complex.exp_re, Complex.neg_re, Complex.neg_im, Complex.I_re,
      Complex.I_im, mul_zero, mul_one, neg_zero, Complex.mul_im, add_zero,
      zero_add, Real.exp_zero, one_mul, sq_abs]
    rw [← Real.cos_abs (-y * |t|), ← Real.cos_abs (-y * t), abs_mul, abs_mul, abs_abs]
  have hsplit := integral_comp_abs (f := fun t => (k t).re)
  have hf : (∫ t, (k t).re) = (∫ t, k t).re := integral_re hint
  have hh : (∫ t in Ioi (0 : ℝ), (k t).re) = (∫ t in Ioi (0 : ℝ), k t).re :=
    integral_re hint.integrableOn
  rw [integral_congr_ae (Eventually.of_forall habs), hf, hh] at hsplit
  have hfull : (∫ t, k t).re =
      Real.sqrt (Real.pi / b) * Real.exp (-y ^ 2 / (4 * b)) := by
    exact congrArg Complex.re (integral_boundary hb y)
  rw [hfull] at hsplit
  change (∫ t in Ioi (0 : ℝ), k t).re = _
  linarith

/-- All analytic and boundary assumptions of the ideal smoothing theorem
hold for every positive Gaussian scale. -/
theorem reflected_pair_re_nonneg {a b : ℝ} (ha : 0 < a) (hb : 0 < b)
    {z : ℂ} (hz0 : 0 ≤ z.re) (hza : z.re ≤ a) :
    0 ≤ (transform a (window b) z +
      transform a (window b) ((a : ℂ) - starRingEnd ℂ z)).re := by
  apply transform_reflected_pair_re_nonneg ha (continuous_window b)
    (integrable_window_exp hb) ?_ hz0 hza
  intro w hw
  have he : w = (w.im : ℂ) * I := by
    apply Complex.ext <;> simp [hw]
  rw [he, integral_half_boundary_re hb]
  positivity

/-- Positive Gaussian scale gives an entire ideal Fermi Laplace transform. -/
theorem analyticAt_gaussian_transform {b : ℝ} (hb : 0 < b) (a : ℝ) (z : ℂ) :
    AnalyticAt ℂ (transform a (window b)) z :=
  analyticAt_transform a (continuous_window b) (integrable_window_exp hb) z

/-- The complex analytic reflection is the bilateral Gaussian Fermi
integral, with the original phases and the full time line retained. -/
theorem gaussian_pair_eq_bilateral {b : ℝ} (hb : 0 < b) (a : ℝ) (z : ℂ) :
    transform a (window b) z + transform a (window b) ((a : ℂ) - z) =
      ∫ t : ℝ, (weight a (window b) t : ℂ) * Complex.exp (-z * (t : ℂ)) :=
  transform_pair_eq_bilateral a (continuous_window b) (even_window b)
    (integrable_window_exp hb) z

/-- The actual same-phase pair attached to a complex point and its critical
reflection is nonnegative whenever the evaluation line encloses the pair. -/
theorem reflected_point_pair_re_nonneg {b σ : ℝ} (hb : 0 < b) (hσ : 1 / 2 < σ)
    (t : ℝ) {ρ : ℂ} (hleft : 1 - σ ≤ ρ.re) (hright : ρ.re ≤ σ) :
    0 ≤ (transform (2 * σ - 1) (window b) ((σ : ℂ) + (t : ℂ) * I - ρ) +
      transform (2 * σ - 1) (window b)
        ((σ : ℂ) + (t : ℂ) * I - (1 - starRingEnd ℂ ρ))).re := by
  have he : ((2 * σ - 1 : ℝ) : ℂ) -
      starRingEnd ℂ ((σ : ℂ) + (t : ℂ) * I - ρ) =
      (σ : ℂ) + (t : ℂ) * I - (1 - starRingEnd ℂ ρ) := by
    push_cast
    simp only [map_sub, map_add, map_mul, Complex.conj_ofReal, Complex.conj_I]
    ring
  rw [← he]
  apply reflected_pair_re_nonneg (a := 2 * σ - 1) (by linarith) hb
  · simpa using sub_nonneg.mpr hright
  · simp only [Complex.sub_re, Complex.add_re, Complex.ofReal_re, Complex.mul_re,
      Complex.ofReal_im, Complex.I_re, Complex.I_im, mul_zero, zero_mul, sub_zero,
      add_zero]
    linarith

/-- The repository's unconditional zero-free strip discharges the actual
reflected-zero geometry for the ideal Gaussian smoother. -/
theorem nontrivial_zero_pair_re_nonneg {b σ : ℝ} (hb : 0 < b)
    (ρ : NontrivialZetaZero)
    (hσ : 1 - zetaPoleReserveZeroMargin ρ.1.im ≤ σ) (t : ℝ) :
    0 ≤ (transform (2 * σ - 1) (window b) ((σ : ℂ) + (t : ℂ) * I - ρ.1) +
      transform (2 * σ - 1) (window b)
        ((σ : ℂ) + (t : ℂ) * I - (1 - starRingEnd ℂ ρ.1))).re := by
  have hz := nontrivialZetaZero_mem_poleReserve_strip ρ
  have hm := (zetaPoleReserveZeroMargin_bounds ρ.1.im).2
  exact reflected_point_pair_re_nonneg hb (by linarith) t (by linarith [hz.1])
    (by linarith [hz.2])

/-- One common evaluation line strictly inside `re s = 1` works for every
actual zero in any specified height band. The known zero-free width supplies
the geometry, rather than an unproved assumption about the zeros. -/
theorem nontrivial_zero_pair_re_nonneg_on_band {b : ℝ} (hb : 0 < b)
    (H t : ℝ) (ρ : NontrivialZetaZero) (hheight : |ρ.1.im| ≤ |H|) :
    let σ := 1 - zetaPoleReserveZeroMargin H
    0 ≤ (transform (2 * σ - 1) (window b) ((σ : ℂ) + (t : ℂ) * I - ρ.1) +
      transform (2 * σ - 1) (window b)
        ((σ : ℂ) + (t : ℂ) * I - (1 - starRingEnd ℂ ρ.1))).re := by
  dsimp only
  exact nontrivial_zero_pair_re_nonneg hb ρ
    (by linarith [zetaPoleReserveZeroMargin_antitone_abs hheight]) t

end
end RiemannGaussian.GaussianFermiZeroPair
