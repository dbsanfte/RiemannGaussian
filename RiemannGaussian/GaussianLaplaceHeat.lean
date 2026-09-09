/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.GaussianMellinVertical
import Mathlib.MeasureTheory.Integral.Prod

/-!
# Signed time heat from a full Laplace transform

An integrable exponentially damped signal determines an exact Gaussian
average at every positive heat time and every real center. Fubini is
justified on the complete time--ordinate product before taking the complex
integral. The original measure is retained: in particular, positive-time
support is not silently replaced by a bilateral signal.

The contour expression keeps the entire complex phase. Absolute values
occur only in the convergence proof, not in the resulting identity.
-/

namespace RiemannGaussian
noncomputable section
open Complex Filter MeasureTheory

/-- The coupled time--ordinate atom before either integration. -/
def gaussianLaplaceHeatJoint (f : ℝ → ℂ) (a tau sigma y u : ℝ) : ℂ :=
  f u * Complex.exp (((a - u : ℝ) : ℂ) * ((sigma : ℂ) + (y : ℂ) * I) +
    (tau : ℂ) * ((sigma : ℂ) + (y : ℂ) * I) ^ 2)

/-- The same atom factors into the full vertical heat weight and the
original Laplace integrand, with its sign and phase unchanged. -/
theorem gaussianLaplaceHeatJoint_eq_laplace (f : ℝ → ℂ) (a tau sigma y u : ℝ) :
    gaussianLaplaceHeatJoint f a tau sigma y u =
      Complex.exp ((a : ℂ) * ((sigma : ℂ) + (y : ℂ) * I) +
        (tau : ℂ) * ((sigma : ℂ) + (y : ℂ) * I) ^ 2) *
        (f u * Complex.exp (-((sigma : ℂ) + (y : ℂ) * I) * (u : ℂ))) := by
  unfold gaussianLaplaceHeatJoint
  rw [mul_comm _ (f u * _), mul_assoc, ← Complex.exp_add]
  congr 2
  push_cast
  ring

/-- Its exact absolute majorant separates the Gaussian ordinate from the
integrable real-damped signal. -/
theorem norm_gaussianLaplaceHeatJoint (f : ℝ → ℂ) (a tau sigma y u : ℝ) :
    ‖gaussianLaplaceHeatJoint f a tau sigma y u‖ =
      (Real.exp (a * sigma + tau * sigma ^ 2) * Real.exp (-tau * y ^ 2)) *
        ‖f u * Complex.exp (-(sigma : ℂ) * (u : ℂ))‖ := by
  rw [gaussianLaplaceHeatJoint_eq_laplace, norm_mul, norm_gaussianMellin_vertical,
    norm_mul, norm_mul, Complex.norm_exp, Complex.norm_exp]
  simp

/-- Absolute integrability holds on the full product as soon as the
original signal is integrable on the chosen real Laplace line. -/
theorem integrable_gaussianLaplaceHeatJoint {μ : Measure ℝ}
    {f : ℝ → ℂ} {sigma tau : ℝ} (htau : 0 < tau)
    (hf : Integrable (fun u => f u * Complex.exp (-(sigma : ℂ) * (u : ℂ))) μ)
    (a : ℝ) :
    Integrable (fun p : ℝ × ℝ => gaussianLaplaceHeatJoint f a tau sigma p.1 p.2)
      (volume.prod μ) := by
  have hfm : AEStronglyMeasurable f μ := by
    have he : Continuous (fun u : ℝ => Complex.exp ((sigma : ℂ) * (u : ℂ))) := by
      fun_prop
    have hm := hf.aestronglyMeasurable.mul he.aestronglyMeasurable
    convert hm using 1
    ext u
    change f u = (f u * Complex.exp (-(sigma : ℂ) * (u : ℂ))) *
      Complex.exp ((sigma : ℂ) * (u : ℂ))
    rw [mul_assoc, ← Complex.exp_add]
    simp
  have hm : AEStronglyMeasurable
      (fun p : ℝ × ℝ => gaussianLaplaceHeatJoint f a tau sigma p.1 p.2)
      (volume.prod μ) := by
    unfold gaussianLaplaceHeatJoint
    apply hfm.comp_snd.mul
    apply Continuous.aestronglyMeasurable
    fun_prop
  have hg := ((integrable_exp_neg_mul_sq htau).const_mul
    (Real.exp (a * sigma + tau * sigma ^ 2))).mul_prod hf.norm
  apply hg.mono' hm
  exact Eventually.of_forall fun p => (norm_gaussianLaplaceHeatJoint f a tau sigma p.1 p.2).le

/-- Integrating one coupled atom in ordinate gives the exact real-time
Gaussian, independent of the auxiliary Laplace abscissa. -/
theorem integral_gaussianLaplaceHeatJoint (f : ℝ → ℂ) (a sigma u : ℝ)
    {tau : ℝ} (htau : 0 < tau) :
    (∫ y : ℝ, gaussianLaplaceHeatJoint f a tau sigma y u) =
      (Real.sqrt (Real.pi / tau) : ℂ) *
        (f u * (Real.exp (-(a - u) ^ 2 / (4 * tau)) : ℂ)) := by
  unfold gaussianLaplaceHeatJoint
  rw [integral_const_mul, integral_gaussianMellin_vertical _ _ htau]
  push_cast
  ring

/-- The actual time-heat integral is absolutely convergent. This is a
consequence of the proved product bound, not a formal inversion convention. -/
theorem integrable_timeGaussian_mul_of_integrable_laplace
    {μ : Measure ℝ} [SFinite μ] {f : ℝ → ℂ} {sigma tau : ℝ} (htau : 0 < tau)
    (hf : Integrable (fun u => f u * Complex.exp (-(sigma : ℂ) * (u : ℂ))) μ)
    (a : ℝ) :
    Integrable (fun u => f u * (Real.exp (-(a - u) ^ 2 / (4 * tau)) : ℂ)) μ := by
  have h := (integrable_gaussianLaplaceHeatJoint htau hf a).integral_prod_right
  simp_rw [integral_gaussianLaplaceHeatJoint f a sigma _ htau] at h
  have hc : (Real.sqrt (Real.pi / tau) : ℂ) ≠ 0 := by
    exact_mod_cast (Real.sqrt_pos.mpr (div_pos Real.pi_pos htau)).ne'
  exact (integrable_const_mul_iff (isUnit_iff_ne_zero.mpr hc) _).mp h

/-- The full Gaussian-weighted Laplace contour is absolutely integrable. -/
theorem integrable_gaussianLaplace_vertical
    {μ : Measure ℝ} [SFinite μ] {f : ℝ → ℂ} {sigma tau : ℝ} (htau : 0 < tau)
    (hf : Integrable (fun u => f u * Complex.exp (-(sigma : ℂ) * (u : ℂ))) μ)
    (a : ℝ) :
    Integrable (fun y : ℝ =>
      Complex.exp ((a : ℂ) * ((sigma : ℂ) + (y : ℂ) * I) +
        (tau : ℂ) * ((sigma : ℂ) + (y : ℂ) * I) ^ 2) *
        ∫ u : ℝ, f u * Complex.exp (-((sigma : ℂ) + (y : ℂ) * I) * (u : ℂ)) ∂μ) := by
  have h := (integrable_gaussianLaplaceHeatJoint htau hf a).integral_prod_left
  simp_rw [gaussianLaplaceHeatJoint_eq_laplace, integral_const_mul] at h
  exact h

/-- Exact Gaussian inversion for every exponentially integrable complex
signal and its original measure. Neither a sign condition nor a choice of
coefficient family is required. -/
theorem integral_gaussianLaplace_vertical_eq_timeHeat
    {μ : Measure ℝ} [SFinite μ] {f : ℝ → ℂ} {sigma tau : ℝ} (htau : 0 < tau)
    (hf : Integrable (fun u => f u * Complex.exp (-(sigma : ℂ) * (u : ℂ))) μ)
    (a : ℝ) :
    (∫ y : ℝ,
      Complex.exp ((a : ℂ) * ((sigma : ℂ) + (y : ℂ) * I) +
        (tau : ℂ) * ((sigma : ℂ) + (y : ℂ) * I) ^ 2) *
        ∫ u : ℝ, f u * Complex.exp (-((sigma : ℂ) + (y : ℂ) * I) * (u : ℂ)) ∂μ) =
      (Real.sqrt (Real.pi / tau) : ℂ) *
        ∫ u : ℝ, f u * (Real.exp (-(a - u) ^ 2 / (4 * tau)) : ℂ) ∂μ := by
  have hswap := integral_integral_swap
    (f := fun y u => gaussianLaplaceHeatJoint f a tau sigma y u)
    (integrable_gaussianLaplaceHeatJoint htau hf a)
  simp_rw [integral_gaussianLaplaceHeatJoint f a sigma _ htau] at hswap
  simpa only [gaussianLaplaceHeatJoint_eq_laplace, integral_const_mul] using hswap

end
end RiemannGaussian
