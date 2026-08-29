import RiemannGaussian.RiemannXiSuzukiPointwiseChebyshevLogAverageMellinXiBridge

/-!
# Suzuki's logarithmic average in one-sided Laplace coordinates

This file performs the global substitution `x = exp t` in the literal
Mellin transform of Suzuki's weighted Chebyshev logarithmic-average error.
The Jacobian is simplified pointwise, genuine integrability is transported
through the exponential change of variables, and the arithmetic recovery of
the spectral-xi logarithmic derivative is restated as a one-sided Laplace
transform.

The resulting formula holds for Laplace parameter `lambda > 1/2`, precisely
the absolutely convergent safe ray.  No continuation to smaller `lambda`,
Tauberian estimate, positivity statement, or zero-location conclusion is
assumed here.
-/

namespace RiemannGaussian

noncomputable section

open Complex MeasureTheory Set

/-- Suzuki's negative logarithmic-average error in logarithmic time. -/
def suzukiChebyshevLogAverageLaplaceSignal (t : ℝ) : ℝ :=
  -suzukiChebyshevLogAverageError (Real.exp t)

/-- The one-sided Laplace kernel of Suzuki's logarithmic-time signal. -/
def suzukiChebyshevLogAverageLaplaceKernel (lambda t : ℝ) : ℝ :=
  suzukiChebyshevLogAverageLaplaceSignal t * Real.exp (-lambda * t)

/-- The exponential Jacobian turns the Mellin integrand pointwise into the shifted Laplace kernel. -/
theorem exp_mul_suzukiChebyshevLogAverageMellinIntegrand_eq_laplaceKernel
    (sigma t : ℝ) :
    Real.exp t *
        (-suzukiChebyshevLogAverageError (Real.exp t) *
          (Real.exp t) ^ (-sigma - 1 / 2 : ℝ)) =
      suzukiChebyshevLogAverageLaplaceKernel (sigma - 1 / 2) t := by
  rw [Real.rpow_def_of_pos (Real.exp_pos t), Real.log_exp]
  unfold suzukiChebyshevLogAverageLaplaceKernel
    suzukiChebyshevLogAverageLaplaceSignal
  calc
    Real.exp t *
          (-suzukiChebyshevLogAverageError (Real.exp t) *
            Real.exp (t * (-sigma - 1 / 2))) =
        -suzukiChebyshevLogAverageError (Real.exp t) *
          (Real.exp t * Real.exp (t * (-sigma - 1 / 2))) := by ring
    _ = -suzukiChebyshevLogAverageError (Real.exp t) *
          Real.exp (t + t * (-sigma - 1 / 2)) := by
      rw [Real.exp_add]
    _ = -suzukiChebyshevLogAverageError (Real.exp t) *
          Real.exp (-(sigma - 1 / 2) * t) := by
      congr 2
      ring

/-- The literal Mellin integral is exactly the one-sided Laplace integral after `x = exp t`. -/
theorem integral_suzukiChebyshevLogAverageLaplaceKernel_eq_mellin
    (sigma : ℝ) :
    (∫ t in Set.Ioi (0 : ℝ),
        suzukiChebyshevLogAverageLaplaceKernel (sigma - 1 / 2) t) =
      ∫ x in Set.Ioi (1 : ℝ),
        -suzukiChebyshevLogAverageError x *
          x ^ (-sigma - 1 / 2 : ℝ) := by
  calc
    (∫ t in Set.Ioi (0 : ℝ),
        suzukiChebyshevLogAverageLaplaceKernel (sigma - 1 / 2) t) =
        ∫ t in Set.Ioi (0 : ℝ), Real.exp t •
          (-suzukiChebyshevLogAverageError (Real.exp t) *
            (Real.exp t) ^ (-sigma - 1 / 2 : ℝ)) := by
      apply setIntegral_congr_fun measurableSet_Ioi
      intro t _ht
      change suzukiChebyshevLogAverageLaplaceKernel (sigma - 1 / 2) t =
        Real.exp t *
          (-suzukiChebyshevLogAverageError (Real.exp t) *
            (Real.exp t) ^ (-sigma - 1 / 2 : ℝ))
      exact
        (exp_mul_suzukiChebyshevLogAverageMellinIntegrand_eq_laplaceKernel
          sigma t).symm
    _ = ∫ x in Set.Ioi (1 : ℝ),
        -suzukiChebyshevLogAverageError x *
          x ^ (-sigma - 1 / 2 : ℝ) := by
      simpa only [Real.exp_zero] using
        integral_comp_exp_Ioi
          (fun x : ℝ => -suzukiChebyshevLogAverageError x *
            x ^ (-sigma - 1 / 2 : ℝ)) 0

/-- For `sigma > 1`, the shifted logarithmic-time Laplace kernel is genuinely integrable. -/
theorem integrableOn_suzukiChebyshevLogAverageLaplaceKernel_shift
    {sigma : ℝ} (hsigma : 1 < sigma) :
    IntegrableOn
      (suzukiChebyshevLogAverageLaplaceKernel (sigma - 1 / 2))
      (Set.Ioi (0 : ℝ)) := by
  have hmellin : IntegrableOn
      (fun x : ℝ => -suzukiChebyshevLogAverageError x *
        x ^ (-sigma - 1 / 2 : ℝ))
      (Set.Ioi (1 : ℝ)) := by
    have h :=
      (integrableOn_suzukiChebyshevLogAverageError_mul_mellinWeight hsigma).neg
    convert h using 1
    funext x
    simp only [Pi.neg_apply]
    ring
  have hcomp : IntegrableOn
      (fun t : ℝ => Real.exp t •
        (-suzukiChebyshevLogAverageError (Real.exp t) *
          (Real.exp t) ^ (-sigma - 1 / 2 : ℝ)))
      (Set.Ioi (0 : ℝ)) := by
    let g : ℝ → ℝ := fun x => -suzukiChebyshevLogAverageError x *
      x ^ (-sigma - 1 / 2 : ℝ)
    have hchange := (integrableOn_comp_exp_Ioi g 0).mpr (by
      simpa only [Real.exp_zero] using hmellin)
    simpa only [g] using hchange
  convert hcomp using 1
  funext t
  rw [smul_eq_mul]
  exact
    (exp_mul_suzukiChebyshevLogAverageMellinIntegrand_eq_laplaceKernel
      sigma t).symm

/-- The logarithmic-time Laplace kernel is integrable for every `lambda > 1/2`. -/
theorem integrableOn_suzukiChebyshevLogAverageLaplaceKernel
    {lambda : ℝ} (hlambda : 1 / 2 < lambda) :
    IntegrableOn
      (suzukiChebyshevLogAverageLaplaceKernel lambda)
      (Set.Ioi (0 : ℝ)) := by
  simpa only [add_sub_cancel_right] using
    integrableOn_suzukiChebyshevLogAverageLaplaceKernel_shift
      (sigma := lambda + 1 / 2) (by linarith)

/-- The spectral-xi negative logarithmic derivative is recovered from the one-sided Laplace transform on the safe ray. -/
theorem xiSpectralNegativeLogDerivative_mellinSpectralPoint_eq_laplaceTransform
    {sigma : ℝ} (hsigma : 1 < sigma) :
    xiSpectralNegativeLogDerivative
        (suzukiChebyshevMellinSpectralPoint sigma) =
      -(((sigma - 1 / 2 : ℝ) ^ 2 : ℝ) : ℂ) *
          ((((∫ t in Set.Ioi (0 : ℝ),
              suzukiChebyshevLogAverageLaplaceKernel
                (sigma - 1 / 2) t) : ℝ) : ℂ) -
            ((4 / (sigma - 1) : ℝ) : ℂ)) -
        suzukiChebyshevMellinCompletedCorrection (sigma : ℂ) := by
  rw [integral_suzukiChebyshevLogAverageLaplaceKernel_eq_mellin]
  exact
    xiSpectralNegativeLogDerivative_mellinSpectralPoint_eq_arithmeticTransform
      hsigma

/-- Shifting by `1/2` sends the Mellin spectral point to the direct Laplace point `-i lambda`. -/
theorem suzukiChebyshevMellinSpectralPoint_add_half (lambda : ℝ) :
    suzukiChebyshevMellinSpectralPoint (lambda + 1 / 2) =
      -Complex.I * (lambda : ℂ) := by
  unfold suzukiChebyshevMellinSpectralPoint
  push_cast
  congr 1
  ring

/-- Direct Laplace-parameter form of the arithmetic recovery of the spectral-xi logarithmic derivative. -/
theorem xiSpectralNegativeLogDerivative_neg_I_mul_eq_laplaceTransform
    {lambda : ℝ} (hlambda : 1 / 2 < lambda) :
    xiSpectralNegativeLogDerivative (-Complex.I * (lambda : ℂ)) =
      -((lambda ^ 2 : ℝ) : ℂ) *
          ((((∫ t in Set.Ioi (0 : ℝ),
              suzukiChebyshevLogAverageLaplaceKernel lambda t) : ℝ) : ℂ) -
            ((4 / (lambda - 1 / 2) : ℝ) : ℂ)) -
        suzukiChebyshevMellinCompletedCorrection
          ((lambda + 1 / 2 : ℝ) : ℂ) := by
  have h :=
    xiSpectralNegativeLogDerivative_mellinSpectralPoint_eq_laplaceTransform
      (sigma := lambda + 1 / 2) (by linarith)
  rw [suzukiChebyshevMellinSpectralPoint_add_half] at h
  have hpole : lambda + 1 / 2 - 1 = lambda - 1 / 2 := by ring
  simpa only [add_sub_cancel_right, hpole] using h

end

end RiemannGaussian
