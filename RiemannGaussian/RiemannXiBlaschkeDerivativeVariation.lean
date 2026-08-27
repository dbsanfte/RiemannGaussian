import RiemannGaussian.RiemannXiSpectralLogDerivativeWindow

/-!
# Poisson mass as spectral Blaschke derivative variation

For an elementary upper-half-plane Blaschke factor, its Schwarz--Pick defect
at `z` is exactly `2 * Im(z)` times the norm of its complex derivative.  This
file applies that identity to every genuine spectral-xi zero, preserving
analytic multiplicity, and identifies the complete Poisson mass with the
extended total derivative variation of the corresponding elementary divisor
factors.
-/

open Complex Filter MeasureTheory Metric Polynomial Set Topology
open scoped Classical ENNReal Interval Topology

namespace RiemannGaussian

noncomputable section

/-- Exact derivative of one elementary upper-half-plane Blaschke factor. -/
theorem deriv_elementaryUpperHalfPlaneBlaschke
    {z alpha : ℂ} (hden : z - starRingEnd ℂ alpha ≠ 0) :
    deriv (elementaryUpperHalfPlaneBlaschke alpha) z =
      (alpha - starRingEnd ℂ alpha) /
        (z - starRingEnd ℂ alpha) ^ 2 := by
  unfold elementaryUpperHalfPlaneBlaschke
  rw [deriv_fun_div
    (c := fun w : ℂ => w - alpha)
    (d := fun w : ℂ => w - starRingEnd ℂ alpha)
    (x := z) (by fun_prop) (by fun_prop) hden]
  simp only [deriv_sub_const, deriv_id'']
  congr 1
  ring

/-- The derivative norm of one elementary factor is its Euclidean Poisson
weight without the observation-height factor. -/
theorem norm_deriv_elementaryUpperHalfPlaneBlaschke
    {z alpha : ℂ} (hz : 0 < z.im) (halpha : 0 < alpha.im) :
    ‖deriv (elementaryUpperHalfPlaneBlaschke alpha) z‖ =
      2 * alpha.im /
        Complex.normSq (z - starRingEnd ℂ alpha) := by
  have hden : z - starRingEnd ℂ alpha ≠ 0 :=
    sub_conj_ne_zero_of_im_pos hz halpha
  rw [deriv_elementaryUpperHalfPlaneBlaschke hden,
    norm_div, norm_pow, ← Complex.normSq_eq_norm_sq]
  have hnum :
      alpha - starRingEnd ℂ alpha =
        (((2 * alpha.im : ℝ) : ℂ)) * Complex.I := by
    apply Complex.ext <;> simp
    ring
  rw [hnum, norm_mul, Complex.norm_real, Complex.norm_I,
    mul_one, Real.norm_eq_abs,
    abs_of_pos (by positivity : 0 < 2 * alpha.im)]

/-- The multiplicity-weighted derivative variation contributed by one upper
spectral zero. -/
def zetaUpperBlaschkeDerivativeVariationSummand
    (z : ℂ) (rho : NontrivialZetaZero) : ℝ :=
  if 0 < (zetaSpectralCoordinate rho.1).im then
    (analyticZetaZeroMultiplicity rho : ℝ) *
      ‖deriv
        (elementaryUpperHalfPlaneBlaschke
          (zetaSpectralCoordinate rho.1)) z‖
  else 0

/-- Every spectral Blaschke derivative-variation summand is nonnegative. -/
theorem zetaUpperBlaschkeDerivativeVariationSummand_nonneg
    (z : ℂ) (rho : NontrivialZetaZero) :
    0 ≤ zetaUpperBlaschkeDerivativeVariationSummand z rho := by
  by_cases hupper : 0 < (zetaSpectralCoordinate rho.1).im
  · rw [zetaUpperBlaschkeDerivativeVariationSummand, if_pos hupper]
    positivity
  · rw [zetaUpperBlaschkeDerivativeVariationSummand, if_neg hupper]

/-- Per spectral zero, Poisson defect is exactly observation height times
twice the elementary Blaschke derivative variation. -/
theorem zetaUpperHyperbolicPoissonDefectSummand_eq_two_mul_im_mul_variation
    {z : ℂ} (hz : 0 < z.im) (rho : NontrivialZetaZero) :
    zetaUpperHyperbolicPoissonDefectSummand z rho =
      2 * z.im * zetaUpperBlaschkeDerivativeVariationSummand z rho := by
  by_cases hupper : 0 < (zetaSpectralCoordinate rho.1).im
  · rw [zetaUpperHyperbolicPoissonDefectSummand, if_pos hupper,
      zetaUpperBlaschkeDerivativeVariationSummand, if_pos hupper,
      norm_deriv_elementaryUpperHalfPlaneBlaschke hz hupper]
    ring
  · rw [zetaUpperHyperbolicPoissonDefectSummand, if_neg hupper,
      zetaUpperBlaschkeDerivativeVariationSummand, if_neg hupper, mul_zero]

/-- The complete extended total variation of the elementary Blaschke
derivatives belonging to upper spectral-xi zeros. -/
def riemannXiUpperBlaschkeDerivativeVariationMass (z : ℂ) : ℝ≥0∞ :=
  ∑' rho : NontrivialZetaZero,
    ENNReal.ofReal (zetaUpperBlaschkeDerivativeVariationSummand z rho)

/-- The same derivative variation in one finite symmetric spectral window. -/
def riemannXiUpperBlaschkeDerivativeVariationWindow
    (z : ℂ) (T : ℝ) : ℝ≥0∞ :=
  ∑ rho ∈ spectralZetaZeroWindow T,
    ENNReal.ofReal (zetaUpperBlaschkeDerivativeVariationSummand z rho)

/-- Cofinal finite windows exhaust the complete Blaschke derivative
variation, whether its value is finite or infinite. -/
theorem tendsto_riemannXiUpperBlaschkeDerivativeVariationWindow (z : ℂ) :
    Tendsto (riemannXiUpperBlaschkeDerivativeVariationWindow z) atTop
      (nhds (riemannXiUpperBlaschkeDerivativeVariationMass z)) := by
  unfold riemannXiUpperBlaschkeDerivativeVariationWindow
    riemannXiUpperBlaschkeDerivativeVariationMass
  exact ENNReal.summable.hasSum.comp tendsto_spectralZetaZeroWindow_atTop

/-- In every finite window, Poisson mass is exactly twice observation height
times total elementary Blaschke derivative variation. -/
theorem riemannXiUpperHyperbolicPoissonDefectWindow_eq_two_im_mul_variation
    {z : ℂ} (hz : 0 < z.im) (T : ℝ) :
    riemannXiUpperHyperbolicPoissonDefectWindow z T =
      ENNReal.ofReal (2 * z.im) *
        riemannXiUpperBlaschkeDerivativeVariationWindow z T := by
  unfold riemannXiUpperHyperbolicPoissonDefectWindow
    riemannXiUpperBlaschkeDerivativeVariationWindow
  calc
    (∑ rho ∈ spectralZetaZeroWindow T,
        ENNReal.ofReal
          (zetaUpperHyperbolicPoissonDefectSummand z rho)) =
        ∑ rho ∈ spectralZetaZeroWindow T,
          (ENNReal.ofReal (2 * z.im) *
            ENNReal.ofReal
              (zetaUpperBlaschkeDerivativeVariationSummand z rho)) := by
      apply Finset.sum_congr rfl
      intro rho _hrho
      rw [← ENNReal.ofReal_mul (by positivity : 0 ≤ 2 * z.im),
        zetaUpperHyperbolicPoissonDefectSummand_eq_two_mul_im_mul_variation
          hz]
    _ = ENNReal.ofReal (2 * z.im) *
        ∑ rho ∈ spectralZetaZeroWindow T,
          ENNReal.ofReal
            (zetaUpperBlaschkeDerivativeVariationSummand z rho) := by
      rw [Finset.mul_sum]

/-- The complete Poisson mass has the same exact derivative-variation
factorization, with both sides allowed to be infinite. -/
theorem riemannXiUpperHyperbolicPoissonDefectMass_eq_two_im_mul_variationMass
    {z : ℂ} (hz : 0 < z.im) :
    riemannXiUpperHyperbolicPoissonDefectMass z =
      ENNReal.ofReal (2 * z.im) *
        riemannXiUpperBlaschkeDerivativeVariationMass z := by
  unfold riemannXiUpperHyperbolicPoissonDefectMass
    riemannXiUpperBlaschkeDerivativeVariationMass
  calc
    (∑' rho : NontrivialZetaZero,
        ENNReal.ofReal
          (zetaUpperHyperbolicPoissonDefectSummand z rho)) =
        ∑' rho : NontrivialZetaZero,
          (ENNReal.ofReal (2 * z.im) *
            ENNReal.ofReal
              (zetaUpperBlaschkeDerivativeVariationSummand z rho)) := by
      apply tsum_congr
      intro rho
      rw [← ENNReal.ofReal_mul (by positivity : 0 ≤ 2 * z.im),
        zetaUpperHyperbolicPoissonDefectSummand_eq_two_mul_im_mul_variation
          hz]
    _ = ENNReal.ofReal (2 * z.im) *
        ∑' rho : NontrivialZetaZero,
          ENNReal.ofReal
            (zetaUpperBlaschkeDerivativeVariationSummand z rho) :=
      ENNReal.tsum_mul_left

/-- Vanishing of the complete Blaschke derivative variation is exactly RH. -/
theorem riemannXiUpperBlaschkeDerivativeVariationMass_eq_zero_iff_riemannHypothesis
    {z : ℂ} (hz : 0 < z.im) :
    riemannXiUpperBlaschkeDerivativeVariationMass z = 0 ↔
      RiemannHypothesis := by
  constructor
  · intro hzero
    apply
      (riemannXiUpperHyperbolicPoissonDefectMass_eq_zero_iff_riemannHypothesis
        hz).mp
    rw [riemannXiUpperHyperbolicPoissonDefectMass_eq_two_im_mul_variationMass
      hz, hzero, mul_zero]
  · intro hRH
    have hpoisson :=
      (riemannXiUpperHyperbolicPoissonDefectMass_eq_zero_iff_riemannHypothesis
        hz).mpr hRH
    rw [riemannXiUpperHyperbolicPoissonDefectMass_eq_two_im_mul_variationMass
      hz] at hpoisson
    exact (mul_eq_zero.mp hpoisson).resolve_left
      (ENNReal.ofReal_ne_zero_iff.mpr (by positivity : 0 < 2 * z.im))

end

end RiemannGaussian
