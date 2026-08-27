import RiemannGaussian.RiemannXiSuzukiCoefficientBridge
import RiemannGaussian.FiniteToEntireTheta

/-!
# Finite genuine-zero form of Suzuki's Hilbert-space expansion

This file installs the exact spectral-xi objects used in Suzuki's arithmetic
Hilbert-space construction:

* `E_xi = A + i A'` and its reflected partner;
* `Theta_xi = E_xi^sharp / E_xi` and the carrier `i(1 + Theta_xi)/2`;
* the normalization `sqrt(m_gamma / pi)` of a zero-function formula;
* finite genuine-zeta-zero windows of `P_t` and the associated signal; and
* the finite-window version of Suzuki's expansion (3.6), with analytic zero
  multiplicities.

All identities here are unconditional.  Complex division in Lean is total,
so `suzukiXiZeroFunctionFormula` records the quotient formula but does not yet
claim the canonical holomorphic value at a removable spectral point.  Nor does
this file claim the infinite expansion or `L²` membership.  Those are the next
analytic steps and must be proved before the finite identity can be promoted to
Suzuki's actual arithmetic signal.
-/

open Complex Filter MeasureTheory Metric Polynomial Set Topology
open scoped Classical ENNReal Interval Topology lp

namespace RiemannGaussian

noncomputable section

/-- Suzuki's de Branges function `E_xi = A + i A'` in spectral coordinates. -/
def suzukiXiEValue (z : ℂ) : ℂ :=
  analyticEValue riemannXiSpectral 1 z

/-- The reflected function `E_xi^sharp = A - i A'`. -/
def suzukiXiESharpValue (z : ℂ) : ℂ :=
  analyticESharpValue riemannXiSpectral 1 z

/-- Suzuki's meromorphic quotient `Theta_xi = E_xi^sharp / E_xi`. -/
def suzukiXiThetaValue (z : ℂ) : ℂ :=
  suzukiXiESharpValue z / suzukiXiEValue z

/-- The common zero-function carrier `i(1 + Theta_xi)/2`. -/
def suzukiXiZeroCarrier (z : ℂ) : ℂ :=
  Complex.I * (1 + suzukiXiThetaValue z) / 2

/-- The normalization `sqrt(m_gamma / pi)` in Suzuki's zero function. -/
def suzukiXiZeroNormalization (rho : NontrivialZetaZero) : ℝ :=
  Real.sqrt ((analyticZetaZeroMultiplicity rho : ℝ) / Real.pi)

/-- The pointwise quotient formula underlying Suzuki's normalized zero
function. At removable spectral points this is only a totalized formula; its
holomorphic extension and `L²` class are deliberately left for the next
analytic layer. -/
def suzukiXiZeroFunctionFormula
    (rho : NontrivialZetaZero) (z : ℂ) : ℂ :=
  (suzukiXiZeroNormalization rho : ℂ) *
    suzukiXiZeroCarrier z /
      (z - zetaSpectralCoordinate rho.1)

/-- The coefficient amplitude `sqrt(pi * m_gamma)` in Suzuki's expansion. -/
def suzukiXiZeroCoefficientAmplitude
    (rho : NontrivialZetaZero) : ℝ :=
  Real.sqrt (Real.pi * (analyticZetaZeroMultiplicity rho : ℝ))

/-- A finite genuine-zero window of Suzuki's meromorphic `P_t`. -/
def suzukiXiSpectralPWindow (t T : ℝ) (z : ℂ) : ℂ :=
  ∑ rho ∈ spectralZetaZeroWindow T,
    (analyticZetaZeroMultiplicity rho : ℂ) *
      suzukiSpectralScrewCoefficient t
        (zetaSpectralCoordinate rho.1) /
          (z - zetaSpectralCoordinate rho.1)

/-- The finite spectral Suzuki signal obtained by multiplying `P_t` by its
common theta carrier. -/
def suzukiXiSignalWindow (t T : ℝ) (z : ℂ) : ℂ :=
  suzukiXiZeroCarrier z * suzukiXiSpectralPWindow t T z

/-- The time derivative of a finite spectral `P_t` window. -/
def suzukiXiSpectralPWindowDerivative (t T : ℝ) (z : ℂ) : ℂ :=
  ∑ rho ∈ spectralZetaZeroWindow T,
    (analyticZetaZeroMultiplicity rho : ℂ) *
      suzukiSpectralScrewCoefficientDerivative t
        (zetaSpectralCoordinate rho.1) /
          (z - zetaSpectralCoordinate rho.1)

/-- The time derivative of a finite spectral Suzuki signal. -/
def suzukiXiSignalWindowDerivative (t T : ℝ) (z : ℂ) : ℂ :=
  suzukiXiZeroCarrier z *
    suzukiXiSpectralPWindowDerivative t T z

/-- Expanded form of Suzuki's spectral de Branges function. -/
@[simp] theorem suzukiXiEValue_eq (z : ℂ) :
    suzukiXiEValue z =
      riemannXiSpectral z + Complex.I * deriv riemannXiSpectral z := by
  simp [suzukiXiEValue, analyticEValue]

/-- Expanded form of Suzuki's reflected de Branges function. -/
@[simp] theorem suzukiXiESharpValue_eq (z : ℂ) :
    suzukiXiESharpValue z =
      riemannXiSpectral z - Complex.I * deriv riemannXiSpectral z := by
  simp [suzukiXiESharpValue, analyticESharpValue]

/-- Averaging `E_xi` and its reflection recovers twice spectral xi. -/
theorem suzukiXiEValue_add_sharp (z : ℂ) :
    suzukiXiEValue z + suzukiXiESharpValue z =
      2 * riemannXiSpectral z := by
  rw [suzukiXiEValue_eq, suzukiXiESharpValue_eq]
  ring

/-- Suzuki's theta quotient is the unit-parameter analytic theta object
already used in the finite-to-entire chain. -/
theorem suzukiXiThetaValue_eq_analyticThetaValue (z : ℂ) :
    suzukiXiThetaValue z =
      analyticThetaValue riemannXiSpectral 1 z := by
  rfl

/-- The sharp de Branges function is the conjugate reflection of `E_xi`. -/
theorem suzukiXiESharpValue_eq_conj_E_conj (z : ℂ) :
    suzukiXiESharpValue z =
      starRingEnd ℂ (suzukiXiEValue (starRingEnd ℂ z)) := by
  exact riemannXiSpectral_analyticESharpValue_eq_conj_analyticEValue_conj 1 z

/-- Away from a real zero of `E_xi`, Suzuki's theta quotient is unimodular. -/
theorem norm_suzukiXiThetaValue_ofReal
    (x : ℝ) (hE : suzukiXiEValue (x : ℂ) ≠ 0) :
    ‖suzukiXiThetaValue (x : ℂ)‖ = 1 := by
  unfold suzukiXiThetaValue
  rw [suzukiXiESharpValue_eq_conj_E_conj]
  have hx : starRingEnd ℂ (x : ℂ) = (x : ℂ) := by simp
  rw [hx, norm_div, norm_conj]
  exact div_self (norm_ne_zero_iff.mpr hE)

/-- Wherever `E_xi` is nonzero, the common carrier is exactly
`i * xi / E_xi`. -/
theorem suzukiXiZeroCarrier_eq_i_mul_xi_div_E
    {z : ℂ} (hE : suzukiXiEValue z ≠ 0) :
    suzukiXiZeroCarrier z =
      Complex.I * riemannXiSpectral z / suzukiXiEValue z := by
  unfold suzukiXiZeroCarrier suzukiXiThetaValue
  field_simp [hE]
  rw [suzukiXiEValue_add_sharp]

/-- The two square-root normalizations in Suzuki's expansion multiply to the
genuine analytic zero multiplicity. -/
theorem suzukiXiZeroCoefficientAmplitude_mul_normalization
    (rho : NontrivialZetaZero) :
    suzukiXiZeroCoefficientAmplitude rho *
        suzukiXiZeroNormalization rho =
      (analyticZetaZeroMultiplicity rho : ℝ) := by
  have hm : 0 ≤ (analyticZetaZeroMultiplicity rho : ℝ) := by positivity
  have hpi : 0 ≤ Real.pi := Real.pi_nonneg
  have hsqrtPi : Real.sqrt Real.pi ≠ 0 :=
    (Real.sqrt_pos.2 Real.pi_pos).ne'
  have hsqrtMSq :
      (Real.sqrt (analyticZetaZeroMultiplicity rho : ℝ)) ^ 2 =
        (analyticZetaZeroMultiplicity rho : ℝ) :=
    Real.sq_sqrt hm
  unfold suzukiXiZeroCoefficientAmplitude suzukiXiZeroNormalization
  rw [Real.sqrt_mul hpi, Real.sqrt_div hm]
  field_simp [hsqrtPi]
  exact hsqrtMSq

/-- Suzuki's coefficient vanishes at time zero for every spectral value,
including the removable frequency zero. -/
@[simp] theorem suzukiSpectralScrewCoefficient_zero_time (alpha : ℂ) :
    suzukiSpectralScrewCoefficient 0 alpha = 0 := by
  by_cases halpha : alpha = 0
  · subst alpha
    simp
  · rw [suzukiSpectralScrewCoefficient_of_ne_zero 0 halpha]
    simp [spectralScrewExponential]

/-- Every finite spectral `P_t` window vanishes at time zero. -/
@[simp] theorem suzukiXiSpectralPWindow_zero_time (T : ℝ) (z : ℂ) :
    suzukiXiSpectralPWindow 0 T z = 0 := by
  simp [suzukiXiSpectralPWindow]

/-- Every finite spectral Suzuki signal vanishes at time zero. -/
@[simp] theorem suzukiXiSignalWindow_zero_time (T : ℝ) (z : ℂ) :
    suzukiXiSignalWindow 0 T z = 0 := by
  simp [suzukiXiSignalWindow]

/-- Differentiation in screw time passes exactly through every finite genuine
zero window. -/
theorem hasDerivAt_suzukiXiSpectralPWindow
    (t T : ℝ) (z : ℂ) :
    HasDerivAt (fun u : ℝ ↦ suzukiXiSpectralPWindow u T z)
      (suzukiXiSpectralPWindowDerivative t T z) t := by
  unfold suzukiXiSpectralPWindow suzukiXiSpectralPWindowDerivative
  apply HasDerivAt.fun_sum
  intro rho _hrho
  exact
    ((hasDerivAt_suzukiSpectralScrewCoefficient t
        (zetaSpectralCoordinate rho.1)).const_mul
          (analyticZetaZeroMultiplicity rho : ℂ)).div_const
            (z - zetaSpectralCoordinate rho.1)

/-- The common theta carrier is time-independent, so the finite Suzuki signal
has the corresponding carrier-weighted derivative. -/
theorem hasDerivAt_suzukiXiSignalWindow
    (t T : ℝ) (z : ℂ) :
    HasDerivAt (fun u : ℝ ↦ suzukiXiSignalWindow u T z)
      (suzukiXiSignalWindowDerivative t T z) t := by
  exact
    (hasDerivAt_suzukiXiSpectralPWindow t T z).const_mul
      (suzukiXiZeroCarrier z)

/-- Finite-window form of Suzuki's zero expansion (3.6), with genuine xi
zeros and their analytic multiplicities. -/
theorem suzukiXiSignalWindow_eq_sum_zeroFunctionFormulas
    (t T : ℝ) (z : ℂ) :
    suzukiXiSignalWindow t T z =
      ∑ rho ∈ spectralZetaZeroWindow T,
        (suzukiXiZeroCoefficientAmplitude rho : ℂ) *
          suzukiSpectralScrewCoefficient t
            (zetaSpectralCoordinate rho.1) *
              suzukiXiZeroFunctionFormula rho z := by
  unfold suzukiXiSignalWindow suzukiXiSpectralPWindow
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro rho _hrho
  unfold suzukiXiZeroFunctionFormula
  have hnormalization :
      (suzukiXiZeroCoefficientAmplitude rho : ℂ) *
          (suzukiXiZeroNormalization rho : ℂ) =
        (analyticZetaZeroMultiplicity rho : ℂ) := by
    exact_mod_cast
      suzukiXiZeroCoefficientAmplitude_mul_normalization rho
  rw [← hnormalization]
  ring

end

end RiemannGaussian
