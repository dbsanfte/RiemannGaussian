import RiemannGaussian.RiemannXiSuzukiCarrierCayleyTimeTraceSpectral
import RiemannGaussian.RiemannXiSpectralReflectionPairing
import RiemannGaussian.RiemannXiBoundaryBlaschkeRigidity

/-!
# Initial Suzuki time response of the off-axis spectral divisor

The finite spectral `P_t` window vanishes at screw time zero, so its first
time response is the natural place to compare Suzuki's dynamics with the
logarithmic derivative of spectral xi.  This file splits that response into
upper and lower spectral halves and takes their signed difference.

At every nonnegative symmetric cutoff, Lean proves the exact identity

`signedInitialVelocity(z,T) = -i * BlaschkeLogDerivativeWindow(z,T)`.

On the real boundary these windows converge to a complete initial velocity
which is exactly the positive Blaschke boundary density.  It therefore
vanishes at any real point exactly under the Riemann hypothesis and is
strictly positive under its negation.  This is a rigorous bridge from Suzuki
screw time to the existing RH rigidity invariant; it does not prove that the
invariant vanishes.
-/

open Complex Filter Set Topology
open scoped Classical ComplexConjugate Topology

namespace RiemannGaussian

noncomputable section

/-- The real-time derivative of one multiplicity-weighted spectral `P_t`
summand. -/
def zetaSuzukiSpectralPTimeDerivativeSummand
    (t : ℝ) (z : ℂ) (rho : NontrivialZetaZero) : ℂ :=
  (analyticZetaZeroMultiplicity rho : ℂ) *
    suzukiSpectralScrewCoefficientDerivative t
      (zetaSpectralCoordinate rho.1) /
        (z - zetaSpectralCoordinate rho.1)

/-- One spectral `P_t` summand has the declared exact real-time
derivative. -/
theorem hasDerivAt_zetaSuzukiSpectralPSummand_time
    (t : ℝ) (z : ℂ) (rho : NontrivialZetaZero) :
    HasDerivAt (fun u : ℝ ↦ zetaSuzukiSpectralPSummand u z rho)
      (zetaSuzukiSpectralPTimeDerivativeSummand t z rho) t := by
  unfold zetaSuzukiSpectralPSummand
    zetaSuzukiSpectralPTimeDerivativeSummand
  exact
    ((hasDerivAt_suzukiSpectralScrewCoefficient t
      (zetaSpectralCoordinate rho.1)).const_mul
        (analyticZetaZeroMultiplicity rho : ℂ)).div_const
          (suzukiXiUpperEvaluationDenominator z
            (zetaSpectralCoordinate rho.1))

/-- The finite upper-half-plane part of the spectral `P_t` time
derivative. -/
def suzukiXiUpperRestrictedSpectralPTimeDerivativeWindow
    (t T : ℝ) (z : ℂ) : ℂ :=
  ∑ rho ∈ spectralZetaZeroWindow T,
    if 0 < (zetaSpectralCoordinate rho.1).im then
      zetaSuzukiSpectralPTimeDerivativeSummand t z rho
    else 0

/-- The finite lower-half-plane part of the spectral `P_t` time
derivative. -/
def suzukiXiLowerRestrictedSpectralPTimeDerivativeWindow
    (t T : ℝ) (z : ℂ) : ℂ :=
  ∑ rho ∈ spectralZetaZeroWindow T,
    if (zetaSpectralCoordinate rho.1).im < 0 then
      zetaSuzukiSpectralPTimeDerivativeSummand t z rho
    else 0

/-- Time differentiation passes through every finite upper restricted
spectral window. -/
theorem hasDerivAt_suzukiXiUpperRestrictedSpectralPWindow_time
    (t T : ℝ) (z : ℂ) :
    HasDerivAt
      (fun u : ℝ ↦ suzukiXiUpperRestrictedSpectralPWindow u T z)
      (suzukiXiUpperRestrictedSpectralPTimeDerivativeWindow t T z) t := by
  unfold suzukiXiUpperRestrictedSpectralPWindow
    suzukiXiUpperRestrictedSpectralPTimeDerivativeWindow
  apply HasDerivAt.fun_sum
  intro rho _hrho
  by_cases hupper : 0 < (zetaSpectralCoordinate rho.1).im
  · simp only [if_pos hupper]
    exact hasDerivAt_zetaSuzukiSpectralPSummand_time t z rho
  · simp only [if_neg hupper]
    exact hasDerivAt_const (x := t) (c := (0 : ℂ))

/-- Time differentiation passes through every finite lower restricted
spectral window. -/
theorem hasDerivAt_suzukiXiLowerRestrictedSpectralPWindow_time
    (t T : ℝ) (z : ℂ) :
    HasDerivAt
      (fun u : ℝ ↦ suzukiXiLowerRestrictedSpectralPWindow u T z)
      (suzukiXiLowerRestrictedSpectralPTimeDerivativeWindow t T z) t := by
  unfold suzukiXiLowerRestrictedSpectralPWindow
    suzukiXiLowerRestrictedSpectralPTimeDerivativeWindow
  apply HasDerivAt.fun_sum
  intro rho _hrho
  by_cases hlower : (zetaSpectralCoordinate rho.1).im < 0
  · simp only [if_pos hlower]
    exact hasDerivAt_zetaSuzukiSpectralPSummand_time t z rho
  · simp only [if_neg hlower]
    exact hasDerivAt_const (x := t) (c := (0 : ℂ))

/-- The finite signed off-axis Suzuki response is the upper restricted
spectral `P_t` window minus its lower counterpart. -/
def suzukiXiOffAxisSignedSpectralPResponseWindow
    (t T : ℝ) (z : ℂ) : ℂ :=
  suzukiXiUpperRestrictedSpectralPWindow t T z -
    suzukiXiLowerRestrictedSpectralPWindow t T z

/-- The exact time derivative of the finite signed off-axis Suzuki
response. -/
def suzukiXiOffAxisSignedSpectralPResponseDerivativeWindow
    (t T : ℝ) (z : ℂ) : ℂ :=
  suzukiXiUpperRestrictedSpectralPTimeDerivativeWindow t T z -
    suzukiXiLowerRestrictedSpectralPTimeDerivativeWindow t T z

/-- The finite signed off-axis response vanishes at screw time zero. -/
@[simp] theorem suzukiXiOffAxisSignedSpectralPResponseWindow_zero_time
    (T : ℝ) (z : ℂ) :
    suzukiXiOffAxisSignedSpectralPResponseWindow 0 T z = 0 := by
  unfold suzukiXiOffAxisSignedSpectralPResponseWindow
    suzukiXiUpperRestrictedSpectralPWindow
    suzukiXiLowerRestrictedSpectralPWindow
  simp [zetaSuzukiSpectralPSummand,
    suzukiSpectralScrewCoefficient_zero_time]

/-- The signed finite response has its declared exact time derivative. -/
theorem hasDerivAt_suzukiXiOffAxisSignedSpectralPResponseWindow_time
    (t T : ℝ) (z : ℂ) :
    HasDerivAt
      (fun u : ℝ ↦ suzukiXiOffAxisSignedSpectralPResponseWindow u T z)
      (suzukiXiOffAxisSignedSpectralPResponseDerivativeWindow t T z) t := by
  exact
    (hasDerivAt_suzukiXiUpperRestrictedSpectralPWindow_time t T z).sub
      (hasDerivAt_suzukiXiLowerRestrictedSpectralPWindow_time t T z)

/-- At time zero, one spectral `P_t` velocity summand is `-i` times the
corresponding logarithmic-derivative principal part. -/
theorem zetaSuzukiSpectralPTimeDerivativeSummand_zero_time
    (z : ℂ) (rho : NontrivialZetaZero) :
    zetaSuzukiSpectralPTimeDerivativeSummand 0 z rho =
      -Complex.I * zetaSpectralLogDerivativePrincipalPart rho z := by
  unfold zetaSuzukiSpectralPTimeDerivativeSummand
    suzukiSpectralScrewCoefficientDerivative
    spectralScrewExponential
    zetaSpectralLogDerivativePrincipalPart
  simp only [ofReal_zero, mul_zero, exp_zero, mul_one]
  ring

/-- The initial upper restricted `P_t` velocity is `-i` times the finite
upper Cauchy divisor window. -/
theorem suzukiXiUpperRestrictedSpectralPTimeDerivativeWindow_zero_time
    (T : ℝ) (z : ℂ) :
    suzukiXiUpperRestrictedSpectralPTimeDerivativeWindow 0 T z =
      -Complex.I * riemannXiSpectralUpperCauchyWindow z T := by
  unfold suzukiXiUpperRestrictedSpectralPTimeDerivativeWindow
    riemannXiSpectralUpperCauchyWindow spectralUpperZetaZeroWindow
  rw [Finset.sum_filter, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro rho _hrho
  by_cases hupper : 0 < (zetaSpectralCoordinate rho.1).im
  · simp only [if_pos hupper]
    rw [zetaSuzukiSpectralPTimeDerivativeSummand_zero_time]
  · simp only [if_neg hupper, mul_zero]

/-- The initial lower restricted `P_t` velocity is `-i` times the finite
lower Cauchy divisor window. -/
theorem suzukiXiLowerRestrictedSpectralPTimeDerivativeWindow_zero_time
    (T : ℝ) (z : ℂ) :
    suzukiXiLowerRestrictedSpectralPTimeDerivativeWindow 0 T z =
      -Complex.I * riemannXiSpectralLowerCauchyWindow z T := by
  unfold suzukiXiLowerRestrictedSpectralPTimeDerivativeWindow
    riemannXiSpectralLowerCauchyWindow spectralLowerZetaZeroWindow
  rw [Finset.sum_filter, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro rho _hrho
  by_cases hlower : (zetaSpectralCoordinate rho.1).im < 0
  · simp only [if_pos hlower]
    rw [zetaSuzukiSpectralPTimeDerivativeSummand_zero_time]
  · simp only [if_neg hlower, mul_zero]

/-- On a nonnegative symmetric window, the finite Blaschke logarithmic
derivative is the upper Cauchy part minus the lower Cauchy part. -/
theorem riemannXiUpperBlaschkeLogDerivativeWindow_eq_upper_sub_lower
    {T : ℝ} (hT : 0 ≤ T) (z : ℂ) :
    riemannXiUpperBlaschkeLogDerivativeWindow z T =
      riemannXiSpectralUpperCauchyWindow z T -
        riemannXiSpectralLowerCauchyWindow z T := by
  rw [riemannXiUpperBlaschkeLogDerivativeWindow_eq_upper_sub_reflected,
    riemannXiSpectralLowerCauchyWindow_eq_upper_conjugatePartner_sum hT]

/-- The initial velocity of the finite signed Suzuki response is exactly
`-i` times the finite spectral Blaschke logarithmic derivative. -/
theorem suzukiXiOffAxisSignedSpectralPResponseDerivativeWindow_zero_time
    {T : ℝ} (hT : 0 ≤ T) (z : ℂ) :
    suzukiXiOffAxisSignedSpectralPResponseDerivativeWindow 0 T z =
      -Complex.I * riemannXiUpperBlaschkeLogDerivativeWindow z T := by
  unfold suzukiXiOffAxisSignedSpectralPResponseDerivativeWindow
  rw [suzukiXiUpperRestrictedSpectralPTimeDerivativeWindow_zero_time,
    suzukiXiLowerRestrictedSpectralPTimeDerivativeWindow_zero_time,
    riemannXiUpperBlaschkeLogDerivativeWindow_eq_upper_sub_lower hT]
  ring

/-- At a noncolliding upper observation point, the finite initial Suzuki
velocity is exactly `-i` times the spectral-xi reflection residual. -/
theorem suzukiXiOffAxisSignedSpectralPResponseDerivativeWindow_zero_time_eq_reflectionResidual
    {z : ℂ} (hz : 0 < z.im) (hxi : riemannXiSpectral z ≠ 0)
    {T : ℝ} (hT : 0 ≤ T) :
    suzukiXiOffAxisSignedSpectralPResponseDerivativeWindow 0 T z =
      -Complex.I * riemannXiUpperSpectralReflectionResidual z T := by
  rw [suzukiXiOffAxisSignedSpectralPResponseDerivativeWindow_zero_time hT,
    riemannXiUpperSpectralReflectionResidual_eq_logDerivativeWindow
      hz hxi hT]

/-- Expanded entire-function form of the finite initial Suzuki velocity:
the only terms are the upper Cauchy divisor, the genuine spectral-xi
logarithmic derivative, its analytic window remainder, and the critical-line
Cauchy part. -/
theorem suzukiXiOffAxisSignedSpectralPResponseDerivativeWindow_zero_time_eq_xiLogDerivative
    {z : ℂ} (hz : 0 < z.im) (hxi : riemannXiSpectral z ≠ 0)
    {T : ℝ} (hT : 0 ≤ T) :
    suzukiXiOffAxisSignedSpectralPResponseDerivativeWindow 0 T z =
      -Complex.I *
        (2 * riemannXiSpectralUpperCauchyWindow z T -
          (logDeriv riemannXiSpectral z -
            riemannXiSpectralWindowLogDerivativeRawRemainder T z -
            riemannXiSpectralCriticalCauchyWindow z T)) := by
  rw [
    suzukiXiOffAxisSignedSpectralPResponseDerivativeWindow_zero_time_eq_reflectionResidual
      hz hxi hT]
  rfl

/-- The signed finite Suzuki response has initial derivative `-i` times its
finite Blaschke logarithmic derivative. -/
theorem hasDerivAt_suzukiXiOffAxisSignedSpectralPResponseWindow_zero_time
    {T : ℝ} (hT : 0 ≤ T) (z : ℂ) :
    HasDerivAt
      (fun t : ℝ ↦ suzukiXiOffAxisSignedSpectralPResponseWindow t T z)
      (-Complex.I * riemannXiUpperBlaschkeLogDerivativeWindow z T) 0 := by
  rw [←
    suzukiXiOffAxisSignedSpectralPResponseDerivativeWindow_zero_time hT z]
  exact
    hasDerivAt_suzukiXiOffAxisSignedSpectralPResponseWindow_time 0 T z

/-- On the real boundary, finite Blaschke logarithmic-derivative windows
converge to the complete absolutely summable boundary value. -/
theorem tendsto_riemannXiUpperBlaschkeLogDerivativeWindow_real
    (x : ℝ) :
    Tendsto (riemannXiUpperBlaschkeLogDerivativeWindow (x : ℂ)) atTop
      (nhds (riemannXiUpperBlaschkeCompleteLogDerivative (x : ℂ))) := by
  have hsum :
      HasSum (zetaUpperBlaschkeSelectedLogDerivativeSummand (x : ℂ))
        (riemannXiUpperBlaschkeCompleteLogDerivative (x : ℂ)) := by
    rw [riemannXiUpperBlaschkeCompleteLogDerivative_real_eq_density_mul_I]
    exact hasSum_zetaUpperBlaschkeSelectedLogDerivativeSummand_real x
  have hlimit := hsum.comp tendsto_spectralZetaZeroWindow_atTop
  apply hlimit.congr'
  exact Eventually.of_forall fun T ↦
    sum_zetaUpperBlaschkeSelectedLogDerivativeSummand_eq_window (x : ℂ) T

/-- The complete initial velocity of the signed off-axis Suzuki spectral
response. -/
def riemannXiSuzukiOffAxisSignedPInitialVelocity (z : ℂ) : ℂ :=
  -Complex.I * riemannXiUpperBlaschkeCompleteLogDerivative z

/-- At every noncolliding upper observation point, finite initial Suzuki
velocities converge to the complete signed initial velocity. -/
theorem tendsto_suzukiXiOffAxisSignedSpectralPResponseDerivativeWindow_zero_time_upper
    {z : ℂ} (hz : 0 < z.im) (hxi : riemannXiSpectral z ≠ 0) :
    Tendsto (fun T : ℝ ↦
      suzukiXiOffAxisSignedSpectralPResponseDerivativeWindow 0 T z) atTop
      (nhds (riemannXiSuzukiOffAxisSignedPInitialVelocity z)) := by
  unfold riemannXiSuzukiOffAxisSignedPInitialVelocity
  refine
    (tendsto_const_nhds.mul
      (tendsto_riemannXiUpperBlaschkeLogDerivativeWindow hz hxi)).congr' ?_
  filter_upwards [eventually_ge_atTop (0 : ℝ)] with T hT
  exact
    (suzukiXiOffAxisSignedSpectralPResponseDerivativeWindow_zero_time
      hT z).symm

/-- Equivalently, the exact spectral-xi reflection residuals, multiplied by
`-i`, converge to the complete Suzuki initial velocity. -/
theorem tendsto_neg_I_mul_riemannXiUpperSpectralReflectionResidual
    {z : ℂ} (hz : 0 < z.im) (hxi : riemannXiSpectral z ≠ 0) :
    Tendsto (fun T : ℝ ↦
      -Complex.I * riemannXiUpperSpectralReflectionResidual z T) atTop
      (nhds (riemannXiSuzukiOffAxisSignedPInitialVelocity z)) := by
  unfold riemannXiSuzukiOffAxisSignedPInitialVelocity
  exact tendsto_const_nhds.mul
    (tendsto_riemannXiUpperSpectralReflectionResidual hz hxi)

/-- On every real boundary line, finite signed Suzuki initial velocities
converge to the complete initial velocity. -/
theorem tendsto_suzukiXiOffAxisSignedSpectralPResponseDerivativeWindow_zero_time
    (x : ℝ) :
    Tendsto (fun T : ℝ ↦
      suzukiXiOffAxisSignedSpectralPResponseDerivativeWindow
        0 T (x : ℂ)) atTop
      (nhds (riemannXiSuzukiOffAxisSignedPInitialVelocity (x : ℂ))) := by
  unfold riemannXiSuzukiOffAxisSignedPInitialVelocity
  refine
    (tendsto_const_nhds.mul
      (tendsto_riemannXiUpperBlaschkeLogDerivativeWindow_real x)).congr' ?_
  filter_upwards [eventually_ge_atTop (0 : ℝ)] with T hT
  exact
    (suzukiXiOffAxisSignedSpectralPResponseDerivativeWindow_zero_time
      hT (x : ℂ)).symm

/-- The complete real-boundary Suzuki initial velocity is exactly the
nonnegative upper-divisor Blaschke density, embedded in the complex line. -/
theorem riemannXiSuzukiOffAxisSignedPInitialVelocity_real_eq_density
    (x : ℝ) :
    riemannXiSuzukiOffAxisSignedPInitialVelocity (x : ℂ) =
      (riemannXiUpperBlaschkeBoundaryDensityTotal x : ℂ) := by
  unfold riemannXiSuzukiOffAxisSignedPInitialVelocity
  rw [riemannXiUpperBlaschkeCompleteLogDerivative_real_eq_density_mul_I]
  calc
    -Complex.I *
        ((riemannXiUpperBlaschkeBoundaryDensityTotal x : ℂ) *
          Complex.I) =
        (riemannXiUpperBlaschkeBoundaryDensityTotal x : ℂ) *
          (-(Complex.I * Complex.I)) := by ring
    _ = (riemannXiUpperBlaschkeBoundaryDensityTotal x : ℂ) := by
      rw [Complex.I_mul_I]
      ring

/-- At every real observation point, vanishing of the complete signed
Suzuki initial velocity is equivalent to the Riemann hypothesis. -/
theorem riemannXiSuzukiOffAxisSignedPInitialVelocity_real_eq_zero_iff_rh
    (x : ℝ) :
    riemannXiSuzukiOffAxisSignedPInitialVelocity (x : ℂ) = 0 ↔
      RiemannHypothesis := by
  rw [riemannXiSuzukiOffAxisSignedPInitialVelocity_real_eq_density]
  constructor
  · intro hzero
    have hdensity : riemannXiUpperBlaschkeBoundaryDensityTotal x = 0 := by
      exact_mod_cast hzero
    exact
      (riemannXiUpperBlaschkeBoundaryDensityTotal_eq_zero_iff_rh x).mp
        hdensity
  · intro hRH
    have hdensity : riemannXiUpperBlaschkeBoundaryDensityTotal x = 0 :=
      (riemannXiUpperBlaschkeBoundaryDensityTotal_eq_zero_iff_rh x).mpr
        hRH
    rw [hdensity]
    simp

/-- The initial signed Suzuki response at the fixed origin vanishes exactly
under the Riemann hypothesis. -/
theorem riemannXiSuzukiOffAxisSignedPInitialVelocity_at_zero_eq_zero_iff_rh :
    riemannXiSuzukiOffAxisSignedPInitialVelocity 0 = 0 ↔
      RiemannHypothesis := by
  simpa using
    riemannXiSuzukiOffAxisSignedPInitialVelocity_real_eq_zero_iff_rh 0

/-- Under failure of RH, the complete signed Suzuki initial velocity has
strictly positive real part at every real observation point. -/
theorem riemannXiSuzukiOffAxisSignedPInitialVelocity_real_re_pos_of_not_rh
    (x : ℝ) (hRH : ¬RiemannHypothesis) :
    0 < (riemannXiSuzukiOffAxisSignedPInitialVelocity (x : ℂ)).re := by
  rw [riemannXiSuzukiOffAxisSignedPInitialVelocity_real_eq_density]
  simp only [ofReal_re]
  exact riemannXiUpperBlaschkeBoundaryDensityTotal_pos_of_not_rh x hRH

/-- In particular, failure of RH gives a strictly positive initial signed
Suzuki time response at the origin. -/
theorem riemannXiSuzukiOffAxisSignedPInitialVelocity_at_zero_re_pos_of_not_rh
    (hRH : ¬RiemannHypothesis) :
    0 < (riemannXiSuzukiOffAxisSignedPInitialVelocity 0).re := by
  simpa using
    riemannXiSuzukiOffAxisSignedPInitialVelocity_real_re_pos_of_not_rh 0 hRH

end

end RiemannGaussian
