/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.GaussianFermiCosineAverage
import Mathlib.Analysis.Calculus.LHopital
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Sinc
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# The exact second moment of the Fermi spectral probability density

Positive squared-sinc regularizations convert the proved characteristic
function into second-moment approximants. The curvature of the original
centered time signal fixes their limit. Fatou first proves integrability;
dominated convergence then recovers the exact moment. No spectral moment
is assumed in differentiating the characteristic function.
-/

namespace RiemannGaussian.GaussianFermiSpectralMoment

noncomputable section
open Complex Filter MeasureTheory Set
open scoped Topology
open GaussianFermiSpectralWeight GaussianFermiCosineAverage GaussianFermiDerivativeBounds

/-- The centered signal has zero first derivative at its symmetry center. -/
theorem centered_first_zero (a b : ℝ) : dampedOne a b (a / 2) 0 = 0 := by
  norm_num [dampedOne, EtaGammaSmoothing.fermiOne, EtaGammaSmoothing.fermi]
  ring

/-- The exact curvature of the original centered signal. -/
theorem centered_second_zero (a b : ℝ) :
    dampedTwo a b (a / 2) 0 = -b - a ^ 2 / 8 := by
  norm_num [dampedTwo, EtaGammaSmoothing.fermiTwo,
    EtaGammaSmoothing.fermiOne, EtaGammaSmoothing.fermi]
  ring

/-- The characteristic deficit has an exact quadratic limit at zero,
computed from time derivatives without assuming a spectral moment. -/
theorem tendsto_characteristic_deficit (a b : ℝ) :
    Tendsto (fun x : ℝ => (1 - 2 * signal a b x) / x ^ 2)
      (𝓝[≠] 0) (𝓝 (b + a ^ 2 / 8)) := by
  have hd := hasDerivAt_dampedOne a b (a / 2) 0
  rw [centered_second_zero] at hd
  have hs : Tendsto (fun x : ℝ => dampedOne a b (a / 2) x / x)
      (𝓝[≠] 0) (𝓝 (-b - a ^ 2 / 8)) := by
    have he : slope (dampedOne a b (a / 2)) 0 =
        fun x : ℝ => dampedOne a b (a / 2) x / x := by
      funext x
      rw [slope_def_field, centered_first_zero, sub_zero, sub_zero]
    simpa only [he] using hasDerivAt_iff_tendsto_slope.mp hd
  have hratio : Tendsto (fun x : ℝ => (-2 * dampedOne a b (a / 2) x) / (2 * x))
      (𝓝[≠] 0) (𝓝 (b + a ^ 2 / 8)) := by
    convert hs.neg using 1
    · funext x
      ring
    · congr 1
      ring
  apply HasDerivAt.lhopital_zero_nhdsNE (f' := fun x => -2 * dampedOne a b (a / 2) x)
    (g' := fun x : ℝ => 2 * x) ?_ ?_ ?_ ?_ ?_ hratio
  · exact Eventually.of_forall fun x => by
      apply (((hasDerivAt_damped a b (a / 2) x).const_mul 2).const_sub 1).congr_deriv
      ring
  · exact Eventually.of_forall fun x => by
      apply ((hasDerivAt_id x).pow 2).congr_deriv
      simp
  · filter_upwards [self_mem_nhdsWithin] with x hx
    exact mul_ne_zero (by norm_num) (by simpa using hx)
  · have hc : Continuous (fun x : ℝ => 1 - 2 * signal a b x) := by
      have hsig := continuous_signal a b
      fun_prop
    simpa [signal_zero] using (hc.continuousAt (x := 0)).tendsto.mono_left nhdsWithin_le_nhds
  · simpa using ((continuous_pow 2).continuousAt (x := (0 : ℝ))).tendsto.mono_left
      nhdsWithin_le_nhds

/-- The exact squared-sinc identity keeps positivity while regularizing
the unbounded second moment. -/
theorem sinc_moment_identity {x : ℝ} (hx : x ≠ 0) (y : ℝ) :
    y ^ 2 * Real.sinc (y * x / 2) ^ 2 = 2 * (1 - Real.cos (y * x)) / x ^ 2 := by
  by_cases hy : y = 0
  · simp [hy]
  have harg : y * x / 2 ≠ 0 := by positivity
  rw [Real.sinc_of_ne_zero harg, div_pow]
  have hsin : Real.sin (y * x / 2) ^ 2 = (1 - Real.cos (y * x)) / 2 := by
    rw [Real.sin_sq_eq_half_sub, show 2 * (y * x / 2) = y * x by ring]
    ring
  rw [hsin]
  field_simp

/-- A nonnegative, bounded-frequency approximation to the second-moment
integrand, retaining the density and the exact squared-sinc factor. -/
def momentApprox (a b x y : ℝ) : ℝ := density a b y * y ^ 2 * Real.sinc (y * x / 2) ^ 2

/-- Each nonzero-frequency approximation is absolutely integrable. -/
theorem integrable_momentApprox {a b x : ℝ} (ha : 0 ≤ a) (hb : 0 < b) (hx : x ≠ 0) :
    Integrable (momentApprox a b x) := by
  apply (((integrable_density ha hb).sub (integrable_density_cosine ha hb 0 x)).const_mul
    (2 / x ^ 2)).congr
  filter_upwards with y
  dsimp only [Pi.sub_apply]
  unfold momentApprox
  rw [mul_assoc, sinc_moment_identity hx]
  simp only [zero_sub, neg_mul, Real.cos_neg]
  ring

/-- The characteristic function evaluates the entire regularized moment
exactly. -/
theorem integral_momentApprox {a b x : ℝ} (ha : 0 ≤ a) (hb : 0 < b) (hx : x ≠ 0) :
    (∫ y : ℝ, momentApprox a b x y) = 2 * (1 - 2 * signal a b x) / x ^ 2 := by
  calc
    _ = (2 / x ^ 2) * ((∫ y : ℝ, density a b y) -
        ∫ y : ℝ, density a b y * Real.cos ((0 - y) * x)) := by
      rw [← integral_sub (integrable_density ha hb) (integrable_density_cosine ha hb 0 x),
        ← integral_const_mul]
      apply integral_congr_ae
      filter_upwards with y
      unfold momentApprox
      rw [mul_assoc, sinc_moment_identity hx]
      simp only [zero_sub, neg_mul, Real.cos_neg]
      ring
    _ = _ := by
      rw [integral_density ha hb, integral_density_cosine ha hb]
      simp only [zero_mul, Real.cos_zero, mul_one]
      ring

/-- Positivity is retained at every approximation scale. -/
theorem momentApprox_nonneg {a b : ℝ} (ha : 0 < a) (hb : 0 < b) (x y : ℝ) :
    0 ≤ momentApprox a b x y := by
  unfold momentApprox
  exact mul_nonneg (mul_nonneg (density_nonneg ha hb y) (sq_nonneg y)) (sq_nonneg _)

/-- The squared-sinc factor never exceeds the original moment integrand. -/
theorem momentApprox_le {a b : ℝ} (ha : 0 < a) (hb : 0 < b) (x y : ℝ) :
    momentApprox a b x y ≤ density a b y * y ^ 2 := by
  have hsq : Real.sinc (y * x / 2) ^ 2 ≤ 1 := by
    have h := abs_le.mp (Real.abs_sinc_le_one (y * x / 2))
    nlinarith [h.1, h.2]
  exact mul_le_of_le_one_right (mul_nonneg (density_nonneg ha hb y) (sq_nonneg y)) hsq

private def step (n : ℕ) : ℝ := ((n : ℝ) + 1)⁻¹

private theorem step_pos (n : ℕ) : 0 < step n := by unfold step; positivity

private theorem tendsto_step : Tendsto step atTop (𝓝[≠] 0) := by
  apply tendsto_nhdsWithin_iff.mpr
  refine ⟨?_, Eventually.of_forall fun n => ?_⟩
  · exact tendsto_inv_atTop_zero.comp
      (tendsto_atTop_add_const_right atTop 1 (tendsto_natCast_atTop_atTop (R := ℝ)))
  · simpa using (step_pos n).ne'

/-- Positive regularizations converge pointwise to the original second
moment, including zero frequency. -/
theorem tendsto_momentApprox (a b y : ℝ) :
    Tendsto (fun n : ℕ => momentApprox a b (((n : ℝ) + 1)⁻¹) y) atTop
      (𝓝 (density a b y * y ^ 2)) := by
  have hx : Tendsto (fun n : ℕ => y * step n / 2) atTop (𝓝 0) := by
    simpa using ((tendsto_step.mono_right nhdsWithin_le_nhds).const_mul y).div_const 2
  have hs := ((Real.continuous_sinc.tendsto 0).comp hx).pow 2
  simpa only [Real.sinc_zero, one_pow, mul_one, step, momentApprox, Function.comp_apply] using
    hs.const_mul (density a b y * y ^ 2)

/-- The integrated regularizations have the exact curvature limit. -/
theorem tendsto_integral_momentApprox {a b : ℝ} (ha : 0 ≤ a) (hb : 0 < b) :
    Tendsto (fun n : ℕ => ∫ y : ℝ, momentApprox a b (((n : ℝ) + 1)⁻¹) y) atTop
      (𝓝 (2 * b + a ^ 2 / 4)) := by
  have h := ((tendsto_characteristic_deficit a b).comp tendsto_step).const_mul 2
  convert h using 1
  · funext n
    change (∫ y : ℝ, momentApprox a b (step n) y) = _
    rw [integral_momentApprox ha hb (step_pos n).ne']
    dsimp only [Function.comp_apply]
    ring
  · congr 1
    ring

/-- Fatou proves that the true spectral second moment is finite. The
argument uses positivity and characteristic curvature, without assuming
moment integrability to differentiate a Fourier integral. -/
theorem integrable_density_secondMoment {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    Integrable (fun y : ℝ => density a b y * y ^ 2) := by
  have hi (n : ℕ) := integrable_momentApprox ha.le hb (step_pos n).ne'
  have he (n : ℕ) : (∫⁻ y : ℝ, ‖momentApprox a b (step n) y‖ₑ) =
      ENNReal.ofReal (∫ y : ℝ, momentApprox a b (step n) y) := by
    rw [← ofReal_integral_norm_eq_lintegral_enorm (hi n)]
    congr 1
    apply integral_congr_ae
    filter_upwards with y
    rw [Real.norm_eq_abs, abs_of_nonneg (momentApprox_nonneg ha hb _ _)]
  have hlim : Tendsto (fun n : ℕ => ∫⁻ y : ℝ, ‖momentApprox a b (step n) y‖ₑ)
      atTop (𝓝 (ENNReal.ofReal (2 * b + a ^ 2 / 4))) := by
    simp_rw [he]
    exact ENNReal.continuous_ofReal.continuousAt.tendsto.comp
      (tendsto_integral_momentApprox ha.le hb)
  apply integrable_of_tendsto
    (Eventually.of_forall (tendsto_momentApprox a b)) (fun n => (hi n).aestronglyMeasurable)
  change liminf (fun n => ∫⁻ y : ℝ, ‖momentApprox a b (step n) y‖ₑ) atTop ≠ ⊤
  rw [hlim.liminf_eq]
  exact ENNReal.ofReal_ne_top

/-- The spectral probability density has exact second moment
`2*b + a^2/4`, uniformly valid at every positive pair of parameters. -/
theorem integral_density_secondMoment {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    (∫ y : ℝ, density a b y * y ^ 2) = 2 * b + a ^ 2 / 4 := by
  have hlim := tendsto_integral_of_dominated_convergence
    (fun y : ℝ => density a b y * y ^ 2)
    (fun n => (integrable_momentApprox ha.le hb (step_pos n).ne').aestronglyMeasurable)
    (integrable_density_secondMoment ha hb)
    (fun n => Eventually.of_forall fun y => by
      rw [Real.norm_eq_abs, abs_of_nonneg (momentApprox_nonneg ha hb _ _)]
      exact momentApprox_le ha hb (step n) y)
    (Eventually.of_forall (tendsto_momentApprox a b))
  exact tendsto_nhds_unique hlim (tendsto_integral_momentApprox ha.le hb)

/-- The absolute first spectral moment is integrable as a consequence of
the proved unit mass and second moment. -/
theorem integrable_density_abs {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    Integrable (fun y : ℝ => density a b y * |y|) := by
  have hd := continuous_density hb a
  apply ((integrable_density ha.le hb).add (integrable_density_secondMoment ha hb)).mono'
    (by fun_prop)
  filter_upwards with y
  dsimp only [Pi.add_apply]
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (density_nonneg ha hb y), abs_abs]
  have h : |y| ≤ 1 + y ^ 2 := by nlinarith [sq_nonneg (|y| - 1), sq_abs y]
  exact (mul_le_mul_of_nonneg_left h (density_nonneg ha hb y)).trans_eq (by ring)

/-- The first absolute moment is bounded by the square root of the exact
second moment. This is a small explicit spectral-spread allowance. -/
theorem integral_density_abs_le_sqrt {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    (∫ y : ℝ, density a b y * |y|) ≤ Real.sqrt (2 * b + a ^ 2 / 4) := by
  let r := Real.sqrt (2 * b + a ^ 2 / 4)
  have hr : 0 < r := by dsimp [r]; positivity
  have hrsq : r ^ 2 = 2 * b + a ^ 2 / 4 := Real.sq_sqrt (by positivity)
  have hpoint (y : ℝ) : density a b y * |y| ≤
      (r ^ 2 * density a b y + density a b y * y ^ 2) / (2 * r) := by
    have hq : |y| ≤ (r ^ 2 + y ^ 2) / (2 * r) := by
      apply (le_div_iff₀ (by positivity)).mpr
      nlinarith [sq_nonneg (|y| - r), sq_abs y]
    exact (mul_le_mul_of_nonneg_left hq (density_nonneg ha hb y)).trans_eq (by ring)
  calc
    _ ≤ ∫ y : ℝ, (r ^ 2 * density a b y + density a b y * y ^ 2) / (2 * r) :=
      integral_mono (integrable_density_abs ha hb)
        ((((integrable_density ha.le hb).const_mul (r ^ 2)).add
          (integrable_density_secondMoment ha hb)).div_const (2 * r)) hpoint
    _ = (r ^ 2 + (2 * b + a ^ 2 / 4)) / (2 * r) := by
      rw [integral_div, integral_add ((integrable_density ha.le hb).const_mul (r ^ 2))
        (integrable_density_secondMoment ha hb), integral_const_mul,
        integral_density ha.le hb, integral_density_secondMoment ha hb, mul_one]
    _ = r := by
      rw [← hrsq]
      field_simp
      ring

end
end RiemannGaussian.GaussianFermiSpectralMoment
