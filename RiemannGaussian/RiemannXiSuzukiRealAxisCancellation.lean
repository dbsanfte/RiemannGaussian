import RiemannGaussian.RiemannXiSuzukiArithmeticSpectralBridge

/-!
# Real-axis cancellation in Suzuki's xi carrier

Suzuki's unconditional real-axis `L²` argument begins with an exact local
cancellation.  On the real axis, spectral xi and its derivative are real,
whereas

`E_xi(x) = xi(x) + i xi'(x)`.

Thus both `xi(x)` and `xi'(x)` have norm at most `‖E_xi(x)‖`.  This file
formalizes those estimates, proves that the theta carrier has norm at most
one even at a totalized zero of `E_xi`, and identifies the carrier-weighted
spectral logarithmic derivative with the bounded quotient `-xi'/E_xi` away
from its removable set.

These are pointwise algebraic ingredients of the real-axis `L²` theorem.
They do not by themselves assert the required global decay or integrability.
-/

open Complex Filter MeasureTheory Metric Polynomial Set Topology
open scoped Classical ENNReal Interval Topology lp

namespace RiemannGaussian

noncomputable section

/-- The derivative of spectral xi is real-valued on the real axis. -/
theorem deriv_riemannXiSpectral_ofReal_im (x : ℝ) :
    (deriv riemannXiSpectral (x : ℂ)).im = 0 := by
  exact deriv_im_eq_zero_of_maps_real_to_real
    differentiable_riemannXiSpectral riemannXiSpectral_ofReal_im x

/-- On the real axis, the real part of `E_xi` is spectral xi itself. -/
theorem suzukiXiEValue_ofReal_re (x : ℝ) :
    (suzukiXiEValue (x : ℂ)).re =
      (riemannXiSpectral (x : ℂ)).re := by
  simp only [suzukiXiEValue_eq, Complex.add_re, Complex.mul_re,
    Complex.I_re, Complex.I_im, zero_mul, one_mul,
    deriv_riemannXiSpectral_ofReal_im, sub_zero, add_zero]

/-- On the real axis, the imaginary part of `E_xi` is the derivative of
spectral xi. -/
theorem suzukiXiEValue_ofReal_im (x : ℝ) :
    (suzukiXiEValue (x : ℂ)).im =
      (deriv riemannXiSpectral (x : ℂ)).re := by
  simp only [suzukiXiEValue_eq, Complex.add_im, Complex.mul_im,
    Complex.I_re, Complex.I_im, zero_mul, one_mul,
    riemannXiSpectral_ofReal_im, zero_add]

/-- The spectral-xi numerator is controlled by its de Branges denominator
on the real axis. -/
theorem norm_riemannXiSpectral_ofReal_le_E (x : ℝ) :
    ‖riemannXiSpectral (x : ℂ)‖ ≤ ‖suzukiXiEValue (x : ℂ)‖ := by
  calc
    ‖riemannXiSpectral (x : ℂ)‖ =
        |(riemannXiSpectral (x : ℂ)).re| := by
      exact (Complex.abs_re_eq_norm.mpr
        (riemannXiSpectral_ofReal_im x)).symm
    _ = |(suzukiXiEValue (x : ℂ)).re| := by
      rw [suzukiXiEValue_ofReal_re]
    _ ≤ ‖suzukiXiEValue (x : ℂ)‖ :=
      Complex.abs_re_le_norm _

/-- The spectral-xi derivative is controlled by the same de Branges
denominator on the real axis. -/
theorem norm_deriv_riemannXiSpectral_ofReal_le_E (x : ℝ) :
    ‖deriv riemannXiSpectral (x : ℂ)‖ ≤
      ‖suzukiXiEValue (x : ℂ)‖ := by
  calc
    ‖deriv riemannXiSpectral (x : ℂ)‖ =
        |(deriv riemannXiSpectral (x : ℂ)).re| := by
      exact (Complex.abs_re_eq_norm.mpr
        (deriv_riemannXiSpectral_ofReal_im x)).symm
    _ = |(suzukiXiEValue (x : ℂ)).im| := by
      rw [suzukiXiEValue_ofReal_im]
    _ ≤ ‖suzukiXiEValue (x : ℂ)‖ :=
      Complex.abs_im_le_norm _

/-- A real point is a zero of `E_xi` exactly when spectral xi and its
derivative vanish there simultaneously. -/
theorem suzukiXiEValue_ofReal_eq_zero_iff (x : ℝ) :
    suzukiXiEValue (x : ℂ) = 0 ↔
      riemannXiSpectral (x : ℂ) = 0 ∧
        deriv riemannXiSpectral (x : ℂ) = 0 := by
  constructor
  · intro hE
    constructor
    · apply norm_eq_zero.mp
      have hnorm := norm_riemannXiSpectral_ofReal_le_E x
      rw [hE, norm_zero] at hnorm
      apply le_antisymm
      · exact hnorm
      · exact norm_nonneg _
    · apply norm_eq_zero.mp
      have hnorm := norm_deriv_riemannXiSpectral_ofReal_le_E x
      rw [hE, norm_zero] at hnorm
      apply le_antisymm
      · exact hnorm
      · exact norm_nonneg _
  · rintro ⟨hxi, hderiv⟩
    simp [suzukiXiEValue_eq, hxi, hderiv]

/-- Away from a zero of `E_xi`, the normalized spectral-xi value has norm at
most one on the real axis. -/
theorem norm_riemannXiSpectral_div_suzukiXiEValue_ofReal_le_one
    (x : ℝ) (hE : suzukiXiEValue (x : ℂ) ≠ 0) :
    ‖riemannXiSpectral (x : ℂ) / suzukiXiEValue (x : ℂ)‖ ≤ 1 := by
  rw [norm_div]
  exact (div_le_one (norm_pos_iff.mpr hE)).2
    (norm_riemannXiSpectral_ofReal_le_E x)

/-- Away from a zero of `E_xi`, the normalized spectral-xi derivative has
norm at most one on the real axis. -/
theorem norm_deriv_riemannXiSpectral_div_suzukiXiEValue_ofReal_le_one
    (x : ℝ) (hE : suzukiXiEValue (x : ℂ) ≠ 0) :
    ‖deriv riemannXiSpectral (x : ℂ) /
        suzukiXiEValue (x : ℂ)‖ ≤ 1 := by
  rw [norm_div]
  exact (div_le_one (norm_pos_iff.mpr hE)).2
    (norm_deriv_riemannXiSpectral_ofReal_le_E x)

/-- Suzuki's common theta carrier has norm at most one at every real point.
The statement includes the totalized value at a zero of `E_xi`. -/
theorem norm_suzukiXiZeroCarrier_ofReal_le_one (x : ℝ) :
    ‖suzukiXiZeroCarrier (x : ℂ)‖ ≤ 1 := by
  by_cases hE : suzukiXiEValue (x : ℂ) = 0
  · rw [suzukiXiZeroCarrier, suzukiXiThetaValue, hE, div_zero]
    norm_num
  · rw [suzukiXiZeroCarrier_eq_i_mul_xi_div_E hE, norm_div,
      norm_mul, Complex.norm_I, one_mul]
    exact (div_le_one (norm_pos_iff.mpr hE)).2
      (norm_riemannXiSpectral_ofReal_le_E x)

/-- Off the removable set, multiplying the spectral negative logarithmic
derivative by Suzuki's carrier cancels the xi denominator exactly. -/
theorem suzukiXiZeroCarrier_mul_xiSpectralNegativeLogDerivative_ofReal
    (x : ℝ) (hE : suzukiXiEValue (x : ℂ) ≠ 0)
    (hxi : riemannXiSpectral (x : ℂ) ≠ 0) :
    suzukiXiZeroCarrier (x : ℂ) *
        xiSpectralNegativeLogDerivative (x : ℂ) =
      -deriv riemannXiSpectral (x : ℂ) /
        suzukiXiEValue (x : ℂ) := by
  rw [suzukiXiZeroCarrier_eq_i_mul_xi_div_E hE,
    xiSpectralNegativeLogDerivative_eq_I_mul_logDeriv]
  rw [logDeriv_apply]
  change
    (Complex.I * riemannXiSpectral (x : ℂ) /
          suzukiXiEValue (x : ℂ)) *
        (Complex.I *
          (deriv riemannXiSpectral (x : ℂ) /
            riemannXiSpectral (x : ℂ))) =
      -deriv riemannXiSpectral (x : ℂ) /
        suzukiXiEValue (x : ℂ)
  field_simp [hE, hxi]
  simp [Complex.I_sq]

/-- The carrier-weighted spectral negative logarithmic derivative is bounded
by one at every nonremovable real point. -/
theorem norm_suzukiXiZeroCarrier_mul_xiSpectralNegativeLogDerivative_ofReal_le_one_of_ne_zero
    (x : ℝ) (hE : suzukiXiEValue (x : ℂ) ≠ 0)
    (hxi : riemannXiSpectral (x : ℂ) ≠ 0) :
    ‖suzukiXiZeroCarrier (x : ℂ) *
        xiSpectralNegativeLogDerivative (x : ℂ)‖ ≤ 1 := by
  rw [suzukiXiZeroCarrier_mul_xiSpectralNegativeLogDerivative_ofReal
    x hE hxi, norm_div, norm_neg]
  exact (div_le_one (norm_pos_iff.mpr hE)).2
    (norm_deriv_riemannXiSpectral_ofReal_le_E x)

/-- With Lean's totalized division, the carrier-weighted spectral negative
logarithmic derivative is bounded by one at every real point.  At a zero of
spectral xi the totalized logarithmic derivative is zero; away from those
points the preceding theorem supplies the genuine cancellation quotient. -/
theorem norm_suzukiXiZeroCarrier_mul_xiSpectralNegativeLogDerivative_ofReal_le_one
    (x : ℝ) :
    ‖suzukiXiZeroCarrier (x : ℂ) *
        xiSpectralNegativeLogDerivative (x : ℂ)‖ ≤ 1 := by
  by_cases hxi : riemannXiSpectral (x : ℂ) = 0
  · rw [xiSpectralNegativeLogDerivative_eq_I_mul_logDeriv,
      logDeriv_apply, hxi, div_zero, mul_zero, mul_zero, norm_zero]
    norm_num
  · have hE : suzukiXiEValue (x : ℂ) ≠ 0 := by
      intro hE
      exact hxi ((suzukiXiEValue_ofReal_eq_zero_iff x).mp hE).1
    exact
      norm_suzukiXiZeroCarrier_mul_xiSpectralNegativeLogDerivative_ofReal_le_one_of_ne_zero
        x hE hxi

end

end RiemannGaussian
