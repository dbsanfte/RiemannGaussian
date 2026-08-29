import RiemannGaussian.RiemannXiSuzukiPointwiseChebyshevLogAverageMellinTransform
import RiemannGaussian.GaussianCompletedLogDerivative
import RiemannGaussian.GaussianXiDivisorContour

/-!
# From Suzuki's arithmetic Mellin transform to spectral xi

The preceding Mellin-transform module identifies Suzuki's logarithmic-average
error with the logarithmic derivative of zeta on the absolutely convergent
real half-line.  This file completes the pole-clearing step.  It isolates the
elementary and Archimedean correction in the completed-zeta logarithmic
derivative, maps a real Mellin parameter to the corresponding imaginary
spectral point, and proves that the arithmetic transform recovers the genuine
spectral-xi logarithmic derivative there.

For `sigma > 1`, this is an equality on the zero-free safe ray.  It does not
analytically continue the Mellin integral, control its sign, or constrain any
zero in the critical strip.
-/

namespace RiemannGaussian

noncomputable section

open Complex MeasureTheory Set

/-- The elementary pole and Archimedean part of the completed-zeta logarithmic derivative. -/
def suzukiChebyshevMellinCompletedCorrection (s : ℂ) : ℂ :=
  1 / s + 1 / (s - 1) - Complex.log Real.pi / 2 +
    Complex.digamma (s / 2) / 2

/-- On `Re s > 1`, the zeta logarithmic derivative is the completed-xi logarithmic derivative minus the explicit correction. -/
theorem logDeriv_riemannZeta_eq_logDeriv_riemannXi_sub_mellinCompletedCorrection
    {s : ℂ} (hs : 1 < s.re) :
    logDeriv riemannZeta s =
      logDeriv riemannXi s - suzukiChebyshevMellinCompletedCorrection s := by
  have h := logDeriv_riemannXi_of_one_lt_re hs
  rw [logDeriv_apply] at h
  change deriv riemannZeta s / riemannZeta s =
    deriv riemannXi s / riemannXi s -
      suzukiChebyshevMellinCompletedCorrection s
  rw [h]
  unfold suzukiChebyshevMellinCompletedCorrection
  ring

/-- Exact Mellin identity written with the completed-xi logarithmic derivative and all correction terms exposed. -/
theorem ofReal_integral_neg_suzukiChebyshevLogAverageError_mul_mellinWeight_eq_completedXi
    {sigma : ℝ} (hsigma : 1 < sigma) :
    (((∫ x in Set.Ioi (1 : ℝ),
        -suzukiChebyshevLogAverageError x *
          x ^ (-sigma - 1 / 2 : ℝ)) : ℝ) : ℂ) =
      (logDeriv riemannXi (sigma : ℂ) -
          suzukiChebyshevMellinCompletedCorrection (sigma : ℂ)) /
          (((sigma - 1 / 2 : ℝ) ^ 2 : ℝ) : ℂ) +
        ((4 / (sigma - 1) : ℝ) : ℂ) := by
  rw [ofReal_integral_neg_suzukiChebyshevLogAverageError_mul_mellinWeight_eq_logDeriv
    hsigma]
  change logDeriv riemannZeta (sigma : ℂ) /
          (((sigma - 1 / 2 : ℝ) ^ 2 : ℝ) : ℂ) +
        ((4 / (sigma - 1) : ℝ) : ℂ) = _
  rw [logDeriv_riemannZeta_eq_logDeriv_riemannXi_sub_mellinCompletedCorrection
    (by simpa using hsigma)]

/-- The imaginary spectral point whose completed-zeta coordinate is the real Mellin parameter `sigma`. -/
def suzukiChebyshevMellinSpectralPoint (sigma : ℝ) : ℂ :=
  -Complex.I * ((sigma - 1 / 2 : ℝ) : ℂ)

/-- The Mellin spectral point maps exactly to `sigma` under the completed spectral coordinate. -/
@[simp]
theorem completedSpectralCoordinate_suzukiChebyshevMellinSpectralPoint
    (sigma : ℝ) :
    completedSpectralCoordinate (suzukiChebyshevMellinSpectralPoint sigma) =
      (sigma : ℂ) := by
  unfold completedSpectralCoordinate suzukiChebyshevMellinSpectralPoint
  push_cast
  rw [show Complex.I * (-Complex.I * ((sigma : ℂ) - 1 / 2)) =
      (sigma : ℂ) - 1 / 2 by
    rw [← mul_assoc]
    rw [show Complex.I * -Complex.I = 1 by
      rw [mul_neg, Complex.I_mul_I]
      norm_num]
    rw [one_mul]]
  ring

/-- At the Mellin spectral point, the spectral negative logarithmic derivative is minus the completed-xi logarithmic derivative. -/
theorem xiSpectralNegativeLogDerivative_mellinSpectralPoint
    (sigma : ℝ) :
    xiSpectralNegativeLogDerivative
        (suzukiChebyshevMellinSpectralPoint sigma) =
      -logDeriv riemannXi (sigma : ℂ) := by
  unfold xiSpectralNegativeLogDerivative
  rw [completedSpectralCoordinate_suzukiChebyshevMellinSpectralPoint]
  rw [logDeriv_apply]
  ring

/-- Exact arithmetic Mellin identity in the genuine spectral-xi logarithmic-derivative coordinates. -/
theorem ofReal_integral_neg_suzukiChebyshevLogAverageError_mul_mellinWeight_eq_spectralXi
    {sigma : ℝ} (hsigma : 1 < sigma) :
    (((∫ x in Set.Ioi (1 : ℝ),
        -suzukiChebyshevLogAverageError x *
          x ^ (-sigma - 1 / 2 : ℝ)) : ℝ) : ℂ) =
      (-xiSpectralNegativeLogDerivative
            (suzukiChebyshevMellinSpectralPoint sigma) -
          suzukiChebyshevMellinCompletedCorrection (sigma : ℂ)) /
          (((sigma - 1 / 2 : ℝ) ^ 2 : ℝ) : ℂ) +
        ((4 / (sigma - 1) : ℝ) : ℂ) := by
  rw [ofReal_integral_neg_suzukiChebyshevLogAverageError_mul_mellinWeight_eq_completedXi
    hsigma]
  rw [xiSpectralNegativeLogDerivative_mellinSpectralPoint]
  ring

/-- The arithmetic Mellin transform recovers the spectral-xi negative logarithmic derivative on the safe imaginary ray. -/
theorem xiSpectralNegativeLogDerivative_mellinSpectralPoint_eq_arithmeticTransform
    {sigma : ℝ} (hsigma : 1 < sigma) :
    xiSpectralNegativeLogDerivative
        (suzukiChebyshevMellinSpectralPoint sigma) =
      -(((sigma - 1 / 2 : ℝ) ^ 2 : ℝ) : ℂ) *
          ((((∫ x in Set.Ioi (1 : ℝ),
              -suzukiChebyshevLogAverageError x *
                x ^ (-sigma - 1 / 2 : ℝ)) : ℝ) : ℂ) -
            ((4 / (sigma - 1) : ℝ) : ℂ)) -
        suzukiChebyshevMellinCompletedCorrection (sigma : ℂ) := by
  have hdenomReal : (sigma - 1 / 2 : ℝ) ^ 2 ≠ 0 := by
    exact pow_ne_zero 2 (by linarith)
  have hdenomComplex :
      (((sigma - 1 / 2 : ℝ) ^ 2 : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast hdenomReal
  rw [ofReal_integral_neg_suzukiChebyshevLogAverageError_mul_mellinWeight_eq_spectralXi
    hsigma]
  rw [add_sub_cancel_right]
  let D : ℂ := (((sigma - 1 / 2 : ℝ) ^ 2 : ℝ) : ℂ)
  let X : ℂ := xiSpectralNegativeLogDerivative
    (suzukiChebyshevMellinSpectralPoint sigma)
  let C : ℂ := suzukiChebyshevMellinCompletedCorrection (sigma : ℂ)
  change X = -D * ((-X - C) / D) - C
  have hD : D ≠ 0 := hdenomComplex
  rw [div_eq_mul_inv]
  calc
    X = -((D * D⁻¹) * (-X - C)) - C := by
      rw [mul_inv_cancel₀ hD]
      ring
    _ = -D * ((-X - C) * D⁻¹) - C := by ring

end

end RiemannGaussian
