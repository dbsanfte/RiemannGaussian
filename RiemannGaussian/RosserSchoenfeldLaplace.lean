/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import Mathlib.Analysis.Fourier.Inversion
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

/-!
# Laplace inversion for the classical smoothed prime formula

The one-sided transform on one vertical line determines a continuous
positive-time function whenever its damped absolute integral converges.
Fourier inversion proves this without an assumed inversion formula or a
conditional convergence convention. These lemmas serve the literal
logarithmically smoothed von-Mangoldt explicit formula.
-/

open Complex Filter MeasureTheory Set
open scoped FourierTransform Topology
namespace RiemannGaussian.RosserSchoenfeldLaplace
noncomputable section

/-- Literal one-sided complex Laplace transform. -/
def transform (s : ℂ) (f : ℝ → ℂ) : ℂ :=
  ∫ t : ℝ in Ioi 0, Complex.exp (-s * t) * f t

/-- One vertical line determines a continuous function on positive time. -/
theorem zero_of_vertical_transform {a : ℝ} {f : ℝ → ℂ}
    (hf : IntegrableOn (fun t : ℝ => Complex.exp (-(a : ℂ) * t) * f t) (Ioi 0))
    (hc : ContinuousOn f (Ioi 0))
    (hz : ∀ y : ℝ, transform ((a : ℂ) + (y : ℂ) * I) f = 0)
    {t : ℝ} (ht : 0 < t) : f t = 0 := by
  let F : ℝ → ℂ := (Ioi (0 : ℝ)).indicator
    (fun x : ℝ => Complex.exp (-(a : ℂ) * x) * f x)
  have hF : Integrable F := (integrable_indicator_iff measurableSet_Ioi).mpr hf
  have hFourier : 𝓕 F = (0 : ℝ → ℂ) := by
    funext w
    rw [Real.fourier_real_eq_integral_exp_smul]
    have he : (fun x : ℝ => Complex.exp ((-2 * Real.pi * x * w : ℝ) * I) • F x) =
        (Ioi (0 : ℝ)).indicator (fun x : ℝ =>
          Complex.exp (-((a : ℂ) + ((2 * Real.pi * w : ℝ) : ℂ) * I) * x) * f x) := by
      funext x
      by_cases hx : x ∈ Ioi (0 : ℝ)
      · simp only [F, Set.indicator_of_mem hx, smul_eq_mul]
        rw [← mul_assoc, ← Complex.exp_add]
        congr 2
        push_cast
        ring
      · simp [F, hx]
    rw [he, integral_indicator measurableSet_Ioi]
    exact hz (2 * Real.pi * w)
  have hFt : ContinuousAt F t := by
    have he : F =ᶠ[𝓝 t] (fun x : ℝ => Complex.exp (-(a : ℂ) * x) * f x) := by
      filter_upwards [Ioi_mem_nhds ht] with x hx
      exact Set.indicator_of_mem hx _
    apply (continuousAt_congr he).mpr
    exact (by fun_prop : ContinuousAt (fun x : ℝ => Complex.exp (-(a : ℂ) * x)) t).mul
      ((hc t ht).continuousAt (Ioi_mem_nhds ht))
  have hh := hF.fourierInv_fourier_eq (by rw [hFourier]; exact integrable_zero _ _ _) hFt
  rw [hFourier] at hh
  have hzero : 𝓕⁻ (0 : ℝ → ℂ) t = 0 := by simp [Real.fourierInv_eq]
  rw [hzero] at hh
  have he : Complex.exp (-(a : ℂ) * t) * f t = 0 := by
    simpa [F, ht] using hh.symm
  exact (mul_eq_zero.mp he).resolve_left (Complex.exp_ne_zero _)

/-- Absolute integrability of one damped complex exponential. -/
theorem integrable_exponential {s z : ℂ} (hz : z.re < s.re) :
    IntegrableOn (fun t : ℝ => Complex.exp (-s*t)*Complex.exp (z*t)) (Ioi 0) := by
  have hh := integrableOn_exp_mul_complex_Ioi
    (a := z-s) (by simpa using sub_neg.mpr hz) 0
  apply hh.congr
  filter_upwards with t
  rw [← Complex.exp_add]
  congr 1
  ring

/-- Exact one-sided transform of an exponential, with genuine convergence. -/
theorem transform_exponential {s z : ℂ} (hz : z.re < s.re) :
    transform s (fun t : ℝ => Complex.exp (z*t)) = 1/(s-z) := by
  have he : (fun t : ℝ => Complex.exp (-s*t)*Complex.exp (z*t)) =
      (fun t : ℝ => Complex.exp ((z-s)*t)) := by
    funext t
    rw [← Complex.exp_add]
    congr 1
    ring
  rw [transform, he, integral_exp_mul_complex_Ioi
    (a := z-s) (by simpa using sub_neg.mpr hz) 0]
  rw [show z-s=-(s-z) by ring]
  simp only [Complex.ofReal_zero, mul_zero, Complex.exp_zero, div_neg, neg_div, neg_neg]

end
end RiemannGaussian.RosserSchoenfeldLaplace
