/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.RosserSchoenfeldLaplace
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
# The exact complex Laplace kernel of one prime event

A logarithmic prime event is the positive hinge at `log n`. Its damped
integral is evaluated by a proved antiderivative and a vanishing limit,
with absolute integrability established independently.
-/

namespace RiemannGaussian.RosserSchoenfeldPrimeKernel
noncomputable section
open Complex Filter MeasureTheory Set
open scoped Topology

/-- The complex exponential has an absolutely integrable first time moment. -/
theorem integrable_time_exponential {s : ℂ} (hs : 0 < s.re) :
    IntegrableOn (fun t : ℝ => (t : ℂ)*Complex.exp (-s*t)) (Ioi 0) := by
  have hh := integrableOn_rpow_mul_exp_neg_mul_rpow
    (s := 1) (p := 1) (b := s.re) (by norm_num) (by norm_num) hs
  simp only [Real.rpow_one] at hh
  apply hh.mono' (by fun_prop)
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  have ht' : 0 < t := ht
  simp [Complex.norm_exp, abs_of_pos ht']

/-- The first time moment tends to zero at positive infinity. -/
theorem tendsto_time_exponential {s : ℂ} (hs : 0 < s.re) :
    Tendsto (fun t : ℝ => (t : ℂ)*Complex.exp (-s*t)) atTop (𝓝 0) := by
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  have hh := tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero 1 s.re hs
  apply hh.congr'
  filter_upwards [eventually_ge_atTop (0 : ℝ)] with t ht
  simp [Complex.norm_exp, abs_of_nonneg ht]

/-- Damping itself tends to zero on its convergence half-plane. -/
theorem tendsto_exponential {s : ℂ} (hs : 0 < s.re) :
    Tendsto (fun t : ℝ => Complex.exp (-s*t)) atTop (𝓝 0) := by
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  have hh := tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero 0 s.re hs
  simpa [Complex.norm_exp] using hh

/-- The complete damped hinge is integrable on its actual half-line. -/
theorem integrable_hinge {s : ℂ} (hs : 0 < s.re) {b : ℝ} (hb : 0 ≤ b) :
    IntegrableOn (fun t : ℝ => Complex.exp (-s*t)*((t-b : ℝ) : ℂ)) (Ioi b) := by
  have he := integrableOn_exp_mul_complex_Ioi (a := -s) (by simpa using neg_neg_of_pos hs) 0
  have hh := ((integrable_time_exponential hs).sub (he.const_mul (b : ℂ))).mono_set
    (show Ioi b ⊆ Ioi (0 : ℝ) from Ioi_subset_Ioi hb)
  apply hh.congr
  filter_upwards with t
  dsimp only [Pi.sub_apply]
  push_cast
  ring

/-- Exact integral of the complex damped hinge, including its endpoint factor. -/
theorem integral_hinge {s : ℂ} (hs : 0 < s.re) {b : ℝ} (hb : 0 ≤ b) :
    (∫ t : ℝ in Ioi b, Complex.exp (-s*t)*((t-b : ℝ) : ℂ)) =
      Complex.exp (-s*b)/s^2 := by
  have hs0 : s ≠ 0 := ne_zero_of_re_pos hs
  let F : ℝ → ℂ := fun t => -Complex.exp (-s*t)*(((t : ℂ)-b)/s+1/s^2)
  have hderiv (t : ℝ) : HasDerivAt F (Complex.exp (-s*t)*((t-b : ℝ) : ℂ)) t := by
    have hid := (hasDerivAt_id t).ofReal_comp
    have he := (hid.const_mul (-s)).cexp
    have hl := ((hid.sub_const (b : ℂ)).div_const s).add_const (1/s^2)
    have hh := he.neg.mul hl
    apply hh.congr_deriv
    dsimp only [Pi.neg_apply, id_eq]
    push_cast
    field_simp
    ring
  have hlim : Tendsto F atTop (𝓝 0) := by
    have hh := ((tendsto_time_exponential hs).div_const s).neg.add
      ((tendsto_exponential hs).const_mul ((b : ℂ)/s-1/s^2))
    norm_num at hh
    apply hh.congr'
    filter_upwards with t
    dsimp only [F, Pi.add_apply, Pi.neg_apply]
    ring_nf
  have hh := integral_Ioi_of_hasDerivAt_of_tendsto'
    (fun t _ => hderiv t) (integrable_hinge hs hb) hlim
  simpa [F, div_eq_mul_inv] using hh

end
end RiemannGaussian.RosserSchoenfeldPrimeKernel
