import RiemannGaussian.RiemannXiSuzukiCarrierGramKernel

/-!
# The spectral-xi density inside Suzuki's carrier Gram kernel

The common-carrier Gram kernel is an exact positive resolvent kernel, but its
weight was still written as `conj(carrier) * carrier`.  This file identifies
that weight with a scalar density built directly from spectral xi and its
derivative on the real axis.

Away from a simultaneous zero of `xi` and `xi'`, the density is

`xi(x)^2 / (xi(x)^2 + xi'(x)^2)`.

At a simultaneous zero, Suzuki's literal totalized theta quotient assigns
the carrier the value `i/2`, so the exact pointwise density is `1/4` there.
The exceptional value is recorded explicitly rather than silently replaced
by a removable representative.  The resulting piecewise arithmetic density
is proved pointwise equal to the literal carrier norm square and is then
substituted into every genuine carrier Gram integral.

All statements are unconditional.  In particular, no simplicity of real xi
zeros and no Riemann-hypothesis assumption is used.
-/

open Complex Filter MeasureTheory Metric Set Topology
open scoped Classical ComplexConjugate ENNReal Topology lp

namespace RiemannGaussian

noncomputable section

/-- The real-axis spectral energy `xi(x)^2 + xi'(x)^2`, expressed through
the real parts of the two real-valued complex quantities. -/
def suzukiXiRealAxisSpectralEnergy (x : ℝ) : ℝ :=
  (riemannXiSpectral (x : ℂ)).re ^ 2 +
    (deriv riemannXiSpectral (x : ℂ)).re ^ 2

/-- The literal squared norm of Suzuki's real-axis xi carrier. -/
def suzukiXiRealAxisCarrierDensity (x : ℝ) : ℝ :=
  ‖suzukiRealAxisXiZeroCarrier x‖ ^ 2

/-- The same density written entirely through spectral xi, its derivative,
and the exact exceptional value forced by Lean's totalized theta quotient. -/
def suzukiXiRealAxisArithmeticCarrierDensity (x : ℝ) : ℝ :=
  if suzukiXiEValue (x : ℂ) = 0 then
    1 / 4
  else
    (riemannXiSpectral (x : ℂ)).re ^ 2 /
      suzukiXiRealAxisSpectralEnergy x

/-- The squared norm of the de Branges denominator is exactly the real-axis
spectral energy. -/
theorem norm_sq_suzukiXiEValue_ofReal
    (x : ℝ) :
    ‖suzukiXiEValue (x : ℂ)‖ ^ 2 =
      suzukiXiRealAxisSpectralEnergy x := by
  rw [Complex.sq_norm, Complex.normSq_apply]
  unfold suzukiXiRealAxisSpectralEnergy
  rw [suzukiXiEValue_ofReal_re, suzukiXiEValue_ofReal_im]
  ring

/-- The squared norm of real-axis spectral xi is its real part squared. -/
theorem norm_sq_riemannXiSpectral_ofReal
    (x : ℝ) :
    ‖riemannXiSpectral (x : ℂ)‖ ^ 2 =
      (riemannXiSpectral (x : ℂ)).re ^ 2 := by
  rw [Complex.sq_norm, Complex.normSq_apply,
    riemannXiSpectral_ofReal_im]
  ring

/-- The squared norm of the real-axis spectral-xi derivative is its real
part squared. -/
theorem norm_sq_deriv_riemannXiSpectral_ofReal
    (x : ℝ) :
    ‖deriv riemannXiSpectral (x : ℂ)‖ ^ 2 =
      (deriv riemannXiSpectral (x : ℂ)).re ^ 2 := by
  rw [Complex.sq_norm, Complex.normSq_apply,
    deriv_riemannXiSpectral_ofReal_im]
  ring

/-- The spectral energy is strictly positive away from a simultaneous zero
of spectral xi and its derivative. -/
theorem suzukiXiRealAxisSpectralEnergy_pos_of_E_ne_zero
    (x : ℝ) (hE : suzukiXiEValue (x : ℂ) ≠ 0) :
    0 < suzukiXiRealAxisSpectralEnergy x := by
  rw [← norm_sq_suzukiXiEValue_ofReal]
  exact sq_pos_of_pos (norm_pos_iff.mpr hE)

/-- Away from the simultaneous-zero set, the carrier density is the exact
xi-energy ratio `xi^2 / (xi^2 + xi'^2)`. -/
theorem suzukiXiRealAxisCarrierDensity_eq_ratio_of_E_ne_zero
    (x : ℝ) (hE : suzukiXiEValue (x : ℂ) ≠ 0) :
    suzukiXiRealAxisCarrierDensity x =
      (riemannXiSpectral (x : ℂ)).re ^ 2 /
        suzukiXiRealAxisSpectralEnergy x := by
  unfold suzukiXiRealAxisCarrierDensity suzukiRealAxisXiZeroCarrier
  rw [suzukiXiZeroCarrier_eq_i_mul_xi_div_E hE, norm_div,
    norm_mul, Complex.norm_I, one_mul, div_pow,
    norm_sq_riemannXiSpectral_ofReal,
    norm_sq_suzukiXiEValue_ofReal]

/-- At a simultaneous zero of spectral xi and its derivative, the literal
totalized theta carrier has squared norm `1/4`. -/
theorem suzukiXiRealAxisCarrierDensity_eq_quarter_of_E_eq_zero
    (x : ℝ) (hE : suzukiXiEValue (x : ℂ) = 0) :
    suzukiXiRealAxisCarrierDensity x = 1 / 4 := by
  unfold suzukiXiRealAxisCarrierDensity suzukiRealAxisXiZeroCarrier
  rw [suzukiXiZeroCarrier, suzukiXiThetaValue, hE, div_zero]
  norm_num

/-- The literal carrier density and the piecewise arithmetic spectral-xi
density agree at every real point. -/
theorem suzukiXiRealAxisCarrierDensity_eq_arithmetic
    (x : ℝ) :
    suzukiXiRealAxisCarrierDensity x =
      suzukiXiRealAxisArithmeticCarrierDensity x := by
  by_cases hE : suzukiXiEValue (x : ℂ) = 0
  · rw [suzukiXiRealAxisCarrierDensity_eq_quarter_of_E_eq_zero x hE]
    unfold suzukiXiRealAxisArithmeticCarrierDensity
    rw [if_pos hE]
  · rw [suzukiXiRealAxisCarrierDensity_eq_ratio_of_E_ne_zero x hE]
    unfold suzukiXiRealAxisArithmeticCarrierDensity
    rw [if_neg hE]

/-- The literal carrier density is Borel measurable. -/
theorem measurable_suzukiXiRealAxisCarrierDensity :
    Measurable suzukiXiRealAxisCarrierDensity := by
  change Measurable (fun x : ℝ ↦
    ‖suzukiRealAxisXiZeroCarrier x‖ ^ 2)
  exact measurable_suzukiRealAxisXiZeroCarrier.norm.pow_const 2

/-- The explicit piecewise spectral-xi density is Borel measurable. -/
theorem measurable_suzukiXiRealAxisArithmeticCarrierDensity :
    Measurable suzukiXiRealAxisArithmeticCarrierDensity := by
  have heq : suzukiXiRealAxisArithmeticCarrierDensity =
      suzukiXiRealAxisCarrierDensity := by
    funext x
    exact (suzukiXiRealAxisCarrierDensity_eq_arithmetic x).symm
  rw [heq]
  exact measurable_suzukiXiRealAxisCarrierDensity

/-- The arithmetic carrier density is nonnegative everywhere. -/
theorem suzukiXiRealAxisArithmeticCarrierDensity_nonneg
    (x : ℝ) :
    0 ≤ suzukiXiRealAxisArithmeticCarrierDensity x := by
  rw [← suzukiXiRealAxisCarrierDensity_eq_arithmetic]
  unfold suzukiXiRealAxisCarrierDensity
  positivity

/-- The arithmetic carrier density is at most one everywhere. -/
theorem suzukiXiRealAxisArithmeticCarrierDensity_le_one
    (x : ℝ) :
    suzukiXiRealAxisArithmeticCarrierDensity x ≤ 1 := by
  rw [← suzukiXiRealAxisCarrierDensity_eq_arithmetic]
  unfold suzukiXiRealAxisCarrierDensity
  have hcarrier := norm_suzukiXiZeroCarrier_ofReal_le_one x
  change ‖suzukiXiZeroCarrier (x : ℂ)‖ ^ 2 ≤ 1
  nlinarith [norm_nonneg (suzukiXiZeroCarrier (x : ℂ))]

/-- The conjugate product appearing in the Gram density is the complex
embedding of the arithmetic carrier density. -/
theorem conj_suzukiRealAxisXiZeroCarrier_mul_eq_arithmeticDensity
    (x : ℝ) :
    starRingEnd ℂ (suzukiRealAxisXiZeroCarrier x) *
        suzukiRealAxisXiZeroCarrier x =
      (suzukiXiRealAxisArithmeticCarrierDensity x : ℂ) := by
  rw [RCLike.conj_mul]
  have h := congrArg (fun r : ℝ ↦ (r : ℂ))
    (suzukiXiRealAxisCarrierDensity_eq_arithmetic x)
  simpa [suzukiXiRealAxisCarrierDensity] using h

/-- One carrier Gram density written directly through the arithmetic
spectral-xi energy ratio. -/
def suzukiXiBoundaryArithmeticCarrierGramIntegrand
    (rho sigma : NontrivialZetaZero) (x : ℝ) : ℂ :=
  (suzukiXiRealAxisArithmeticCarrierDensity x : ℂ) /
    (((x : ℂ) - starRingEnd ℂ (zetaSpectralCoordinate rho.1)) *
      ((x : ℂ) - zetaSpectralCoordinate sigma.1))

/-- The common-carrier Gram density is pointwise identical to its explicit
spectral-xi arithmetic form. -/
theorem suzukiXiBoundaryCarrierGramIntegrand_eq_arithmetic
    (rho sigma : NontrivialZetaZero) (x : ℝ) :
    suzukiXiBoundaryCarrierGramIntegrand rho sigma x =
      suzukiXiBoundaryArithmeticCarrierGramIntegrand rho sigma x := by
  unfold suzukiXiBoundaryCarrierGramIntegrand
    suzukiXiBoundaryArithmeticCarrierGramIntegrand
  rw [conj_suzukiRealAxisXiZeroCarrier_mul_eq_arithmeticDensity]

/-- The explicit arithmetic carrier density divided by any pair of genuine
xi resolvents is Lebesgue integrable, including at real multiple nodes. -/
theorem integrable_suzukiXiBoundaryArithmeticCarrierGramIntegrand
    (rho sigma : NontrivialZetaZero) :
    Integrable
      (suzukiXiBoundaryArithmeticCarrierGramIntegrand rho sigma) := by
  apply (integrable_suzukiXiBoundaryCarrierGramIntegrand rho sigma).congr
  exact Eventually.of_forall fun x ↦
    suzukiXiBoundaryCarrierGramIntegrand_eq_arithmetic rho sigma x

/-- Every carrier Gram kernel is the integral of the explicit piecewise
spectral-xi energy density against its two-node resolvent. -/
theorem suzukiXiBoundaryCarrierGramKernel_eq_arithmetic_integral
    (rho sigma : NontrivialZetaZero) :
    suzukiXiBoundaryCarrierGramKernel rho sigma =
      ∫ x : ℝ,
        suzukiXiBoundaryArithmeticCarrierGramIntegrand rho sigma x := by
  unfold suzukiXiBoundaryCarrierGramKernel
  apply integral_congr_ae
  exact Eventually.of_forall fun x ↦
    suzukiXiBoundaryCarrierGramIntegrand_eq_arithmetic rho sigma x

/-- Every genuine Suzuki zero-function Gram entry is therefore an explicit
spectral-xi energy-density resolvent integral with its exact multiplicity
normalizations. -/
theorem suzukiXiZeroFunctionGramEntry_eq_arithmeticCarrierIntegral
    (rho sigma : NontrivialZetaZero) :
    suzukiXiZeroFunctionGramEntry rho sigma =
      (((suzukiXiZeroNormalization rho *
          suzukiXiZeroNormalization sigma : ℝ) : ℂ) *
        ∫ x : ℝ,
          suzukiXiBoundaryArithmeticCarrierGramIntegrand rho sigma x) := by
  rw [suzukiXiZeroFunctionGramEntry_eq_carrierGramKernel,
    suzukiXiBoundaryCarrierGramKernel_eq_arithmetic_integral]

end

end RiemannGaussian
