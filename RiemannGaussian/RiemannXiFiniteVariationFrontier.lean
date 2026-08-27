import RiemannGaussian.GaussianXiCompleteMassFiniteness
import RiemannGaussian.RiemannXiBlaschkePhaseGeometry

/-!
# The finite-total Blaschke rigidity frontier

Inverse-square divisor summability makes the complete elementary Blaschke
variation a finite real number.  Under failure of RH this number is strictly
positive.  Using the total itself as the finite-window threshold removes the
earlier polynomial-height escape branch: every sufficiently large genuine
spectral window must exhibit either a persistent xi reflection residual or a
persistent positive pairwise phase-dispersion energy.
-/

open Complex Filter MeasureTheory Metric Polynomial Set Topology
open scoped Classical ENNReal Interval Topology

namespace RiemannGaussian

noncomputable section

/-- The finite real total of the complete upper spectral Blaschke derivative
variation. -/
def riemannXiUpperBlaschkeDerivativeVariationTotal (z : ℂ) : ℝ :=
  (riemannXiUpperBlaschkeDerivativeVariationMass z).toReal

/-- The finite real variation total is nonnegative. -/
theorem riemannXiUpperBlaschkeDerivativeVariationTotal_nonneg (z : ℂ) :
    0 ≤ riemannXiUpperBlaschkeDerivativeVariationTotal z :=
  ENNReal.toReal_nonneg

/-- At an upper point, embedding the real total recovers the complete
extended variation mass exactly. -/
theorem ofReal_riemannXiUpperBlaschkeDerivativeVariationTotal
    {z : ℂ} (hz : 0 < z.im) :
    ENNReal.ofReal (riemannXiUpperBlaschkeDerivativeVariationTotal z) =
      riemannXiUpperBlaschkeDerivativeVariationMass z := by
  unfold riemannXiUpperBlaschkeDerivativeVariationTotal
  exact ENNReal.ofReal_toReal
    (riemannXiUpperBlaschkeDerivativeVariationMass_ne_top hz)

/-- The real total is the actual convergent sum of the elementary derivative
variations. -/
theorem riemannXiUpperBlaschkeDerivativeVariationTotal_eq_tsum
    {z : ℂ} (hz : 0 < z.im) :
    riemannXiUpperBlaschkeDerivativeVariationTotal z =
      ∑' rho : NontrivialZetaZero,
        zetaUpperBlaschkeDerivativeVariationSummand z rho := by
  unfold riemannXiUpperBlaschkeDerivativeVariationTotal
  rw [riemannXiUpperBlaschkeDerivativeVariationMass_eq_ofReal_tsum hz]
  apply ENNReal.toReal_ofReal
  exact tsum_nonneg fun rho =>
    zetaUpperBlaschkeDerivativeVariationSummand_nonneg z rho

/-- At every upper point, vanishing of the finite real variation total is
equivalent to RH. -/
theorem riemannXiUpperBlaschkeDerivativeVariationTotal_eq_zero_iff_rh
    {z : ℂ} (hz : 0 < z.im) :
    riemannXiUpperBlaschkeDerivativeVariationTotal z = 0 ↔
      RiemannHypothesis := by
  constructor
  · intro hzero
    apply
      (riemannXiUpperBlaschkeDerivativeVariationMass_eq_zero_iff_riemannHypothesis
        hz).mp
    rw [← ofReal_riemannXiUpperBlaschkeDerivativeVariationTotal hz,
      hzero, ENNReal.ofReal_zero]
  · intro hRH
    have hmass :=
      (riemannXiUpperBlaschkeDerivativeVariationMass_eq_zero_iff_riemannHypothesis
        hz).mpr hRH
    unfold riemannXiUpperBlaschkeDerivativeVariationTotal
    rw [hmass, ENNReal.toReal_zero]

/-- Under failure of RH, the finite real Blaschke variation total is strictly
positive at every upper observation point. -/
theorem riemannXiUpperBlaschkeDerivativeVariationTotal_pos_of_not_rh
    {z : ℂ} (hz : 0 < z.im) (hRH : ¬RiemannHypothesis) :
    0 < riemannXiUpperBlaschkeDerivativeVariationTotal z := by
  have hmassZero :
      riemannXiUpperBlaschkeDerivativeVariationMass z ≠ 0 := by
    intro hzero
    exact hRH
      ((riemannXiUpperBlaschkeDerivativeVariationMass_eq_zero_iff_riemannHypothesis
        hz).mp hzero)
  unfold riemannXiUpperBlaschkeDerivativeVariationTotal
  exact ENNReal.toReal_pos hmassZero
    (riemannXiUpperBlaschkeDerivativeVariationMass_ne_top hz)

/-- Under failure of RH, half of the actual finite total lies in every
sufficiently large finite spectral window. -/
theorem eventually_half_variationTotal_le_window_of_not_rh
    {z : ℂ} (hz : 0 < z.im) (hRH : ¬RiemannHypothesis) :
    ∀ᶠ T : ℝ in atTop,
      ENNReal.ofReal
          (riemannXiUpperBlaschkeDerivativeVariationTotal z / 2) ≤
        riemannXiUpperBlaschkeDerivativeVariationWindow z T := by
  apply eventually_half_le_riemannXiUpperBlaschkeDerivativeVariationWindow
    (riemannXiUpperBlaschkeDerivativeVariationTotal_pos_of_not_rh hz hRH)
  rw [ofReal_riemannXiUpperBlaschkeDerivativeVariationTotal hz]

/-- At a noncolliding upper point and under failure of RH, the actual finite
variation total forces a persistent residual-plus-cancellation threshold,
with no approximation-height alternative. -/
theorem eventually_half_variationTotal_le_reflectionResidual_add_cancellation_of_not_rh
    {z : ℂ} (hz : 0 < z.im) (hxi : riemannXiSpectral z ≠ 0)
    (hRH : ¬RiemannHypothesis) :
    ∀ᶠ T : ℝ in atTop,
      riemannXiUpperBlaschkeDerivativeVariationTotal z / 2 ≤
        ‖riemannXiUpperSpectralReflectionResidual z T‖ +
          riemannXiUpperBlaschkeLogDerivativeCancellation z T := by
  apply eventually_half_threshold_le_reflectionResidual_add_cancellation
    hz hxi
    (riemannXiUpperBlaschkeDerivativeVariationTotal_pos_of_not_rh hz hRH)
  rw [ofReal_riemannXiUpperBlaschkeDerivativeVariationTotal hz]

/-- Thus failure of RH directly forces either arbitrarily late positive xi
reflection residual or eventual positive Blaschke cancellation, normalized
by the complete finite variation total. -/
theorem frequently_reflectionResidual_or_eventually_cancellation_of_not_rh
    {z : ℂ} (hz : 0 < z.im) (hxi : riemannXiSpectral z ≠ 0)
    (hRH : ¬RiemannHypothesis) :
    (∃ᶠ T : ℝ in atTop,
      riemannXiUpperBlaschkeDerivativeVariationTotal z / 4 ≤
        ‖riemannXiUpperSpectralReflectionResidual z T‖) ∨
      ∀ᶠ T : ℝ in atTop,
        riemannXiUpperBlaschkeDerivativeVariationTotal z / 4 ≤
          riemannXiUpperBlaschkeLogDerivativeCancellation z T := by
  exact frequently_reflectionResidual_or_eventually_cancellation
    (eventually_half_variationTotal_le_reflectionResidual_add_cancellation_of_not_rh
      hz hxi hRH)

/-- Replacing cancellation by its pairwise energy gives the direct finite
rigidity frontier: persistent residual or persistent positive phase
dispersion, with no third height-growth branch. -/
theorem frequently_reflectionResidual_or_eventually_phaseDispersion_of_not_rh
    {z : ℂ} (hz : 0 < z.im) (hxi : riemannXiSpectral z ≠ 0)
    (hRH : ¬RiemannHypothesis) :
    (∃ᶠ T : ℝ in atTop,
      riemannXiUpperBlaschkeDerivativeVariationTotal z / 4 ≤
        ‖riemannXiUpperSpectralReflectionResidual z T‖) ∨
      ∀ᶠ T : ℝ in atTop,
        (riemannXiUpperBlaschkeDerivativeVariationTotal z / 4) ^ 2 ≤
          riemannXiUpperBlaschkePhaseDispersionWindow z T := by
  rcases
      frequently_reflectionResidual_or_eventually_cancellation_of_not_rh
        hz hxi hRH with hresidual | hcancellation
  · exact Or.inl hresidual
  · exact Or.inr
      (eventually_phaseDispersion_of_eventually_cancellation
        (riemannXiUpperBlaschkeDerivativeVariationTotal_pos_of_not_rh hz hRH)
        hcancellation)

/-- The phase branch is literally a positive weighted unit-phase chordal
energy branch. -/
theorem frequently_reflectionResidual_or_eventually_phaseChordEnergy_of_not_rh
    {z : ℂ} (hz : 0 < z.im) (hxi : riemannXiSpectral z ≠ 0)
    (hRH : ¬RiemannHypothesis) :
    (∃ᶠ T : ℝ in atTop,
      riemannXiUpperBlaschkeDerivativeVariationTotal z / 4 ≤
        ‖riemannXiUpperSpectralReflectionResidual z T‖) ∨
      ∀ᶠ T : ℝ in atTop,
        (riemannXiUpperBlaschkeDerivativeVariationTotal z / 4) ^ 2 ≤
          riemannXiUpperBlaschkePhaseChordEnergyWindow z T := by
  rcases
      frequently_reflectionResidual_or_eventually_phaseDispersion_of_not_rh
        hz hxi hRH with hresidual | hdispersion
  · exact Or.inl hresidual
  · exact Or.inr
      (eventually_phaseChordEnergy_of_eventually_phaseDispersion hdispersion)

end

end RiemannGaussian
