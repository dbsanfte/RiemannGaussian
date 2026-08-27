import RiemannGaussian.GaussianXiInverseSquareSummability
import RiemannGaussian.RiemannXiHyperbolicDefectPoissonEquivalence
import RiemannGaussian.RiemannXiBlaschkeDerivativeVariation

/-!
# Finiteness of the complete spectral defect masses

The unconditional inverse-square xi-divisor sum controls the complete
Poisson mass at every upper-half-plane observation point.  The established
finite-gap comparison and exact Blaschke factorization then transfer this
finiteness to the logarithmic proper-time action and elementary Blaschke
derivative variation at every noncolliding point.
-/

open Complex Filter MeasureTheory Metric Polynomial Set Topology
open scoped Classical ENNReal Interval Topology

namespace RiemannGaussian

noncomputable section

/-- Fixed-observation coefficient comparing spectral inverse squares with
the reflected upper-half-plane denominator. -/
def upperHalfPlaneInverseSquareCoefficient (z : ℂ) : ℝ :=
  2 + (1 + 2 * z.re ^ 2) / z.im ^ 2

/-- At an upper observation point, the reflected Blaschke denominator
controls `1 + alpha.re^2` uniformly over all upper `alpha`. -/
theorem one_add_re_sq_le_upperHalfPlaneInverseSquareCoefficient_mul_normSq
    {z alpha : ℂ} (hz : 0 < z.im) (halpha : 0 < alpha.im) :
    1 + alpha.re ^ 2 ≤
      upperHalfPlaneInverseSquareCoefficient z *
        Complex.normSq (z - starRingEnd ℂ alpha) := by
  let D : ℝ := Complex.normSq (z - starRingEnd ℂ alpha)
  have hhorizontal : (z.re - alpha.re) ^ 2 ≤ D := by
    dsimp [D]
    simp [Complex.normSq_apply]
    nlinarith [sq_nonneg (z.im + alpha.im)]
  have hvertical : z.im ^ 2 ≤ D := by
    dsimp [D]
    simp [Complex.normSq_apply]
    nlinarith [sq_nonneg (z.re - alpha.re), mul_pos hz halpha]
  have hshift :
      alpha.re ^ 2 ≤ 2 * z.re ^ 2 + 2 * (z.re - alpha.re) ^ 2 := by
    nlinarith [sq_nonneg (2 * z.re - alpha.re)]
  have hconstant :
      1 + 2 * z.re ^ 2 ≤
        ((1 + 2 * z.re ^ 2) / z.im ^ 2) * D := by
    calc
      1 + 2 * z.re ^ 2 =
          ((1 + 2 * z.re ^ 2) / z.im ^ 2) * z.im ^ 2 := by
        field_simp [hz.ne']
      _ ≤ ((1 + 2 * z.re ^ 2) / z.im ^ 2) * D :=
        mul_le_mul_of_nonneg_left hvertical (by positivity)
  unfold upperHalfPlaneInverseSquareCoefficient
  nlinarith

/-- The fixed-observation inverse-square coefficient is positive in the
upper half-plane. -/
theorem upperHalfPlaneInverseSquareCoefficient_pos
    {z : ℂ} (hz : 0 < z.im) :
    0 < upperHalfPlaneInverseSquareCoefficient z := by
  unfold upperHalfPlaneInverseSquareCoefficient
  positivity

/-- Each multiplicity-counted Poisson summand is dominated by a fixed
multiple of the inverse-square spectral-ordinate summand. -/
theorem zetaUpperHyperbolicPoissonDefectSummand_le_inverseSquare
    {z : ℂ} (hz : 0 < z.im) (rho : NontrivialZetaZero) :
    zetaUpperHyperbolicPoissonDefectSummand z rho ≤
      (2 * z.im * upperHalfPlaneInverseSquareCoefficient z) *
        ((analyticZetaZeroMultiplicity rho : ℝ) /
          (1 + (zetaSpectralCoordinate rho.1).re ^ 2)) := by
  by_cases hupper : 0 < (zetaSpectralCoordinate rho.1).im
  · let alpha : ℂ := zetaSpectralCoordinate rho.1
    let D : ℝ := Complex.normSq (z - starRingEnd ℂ alpha)
    let Q : ℝ := 1 + alpha.re ^ 2
    let C : ℝ := upperHalfPlaneInverseSquareCoefficient z
    have hD : 0 < D := by
      dsimp [D]
      exact Complex.normSq_pos.mpr
        (sub_conj_ne_zero_of_im_pos hz hupper)
    have hQ : 0 < Q := by
      dsimp [Q]
      positivity
    have hC : 0 < C := by
      exact upperHalfPlaneInverseSquareCoefficient_pos hz
    have hhalf : alpha.im ≤ 1 / 2 := by
      dsimp [alpha]
      have habs := NontrivialZetaZero.abs_spectralCoordinate_im_lt_half rho
      exact (le_abs_self _).trans habs.le
    have hden : Q ≤ C * D := by
      exact
        one_add_re_sq_le_upperHalfPlaneInverseSquareCoefficient_mul_normSq
          hz hupper
    have hrecip : 1 / D ≤ C / Q := by
      rw [div_le_div_iff₀ hD hQ]
      simpa only [one_mul] using hden
    have hnum : 4 * z.im * alpha.im ≤ 2 * z.im := by
      have hmul := mul_le_mul_of_nonneg_left hhalf
        (show 0 ≤ 4 * z.im by positivity)
      nlinarith
    have hcore : 4 * z.im * alpha.im / D ≤
        (2 * z.im * C) / Q := by
      calc
        4 * z.im * alpha.im / D ≤ 2 * z.im / D :=
          div_le_div_of_nonneg_right hnum hD.le
        _ = (2 * z.im) * (1 / D) := by ring
        _ ≤ (2 * z.im) * (C / Q) :=
          mul_le_mul_of_nonneg_left hrecip (by positivity)
        _ = (2 * z.im * C) / Q := by ring
    rw [zetaUpperHyperbolicPoissonDefectSummand, if_pos hupper]
    change (analyticZetaZeroMultiplicity rho : ℝ) *
        (4 * z.im * alpha.im / D) ≤
      (2 * z.im * C) *
        ((analyticZetaZeroMultiplicity rho : ℝ) / Q)
    calc
      (analyticZetaZeroMultiplicity rho : ℝ) *
          (4 * z.im * alpha.im / D) ≤
        (analyticZetaZeroMultiplicity rho : ℝ) *
          ((2 * z.im * C) / Q) :=
        mul_le_mul_of_nonneg_left hcore (Nat.cast_nonneg _)
      _ = (2 * z.im * C) *
          ((analyticZetaZeroMultiplicity rho : ℝ) / Q) := by ring
  · rw [zetaUpperHyperbolicPoissonDefectSummand, if_neg hupper]
    apply mul_nonneg
    · exact mul_nonneg (mul_nonneg (by norm_num) hz.le)
        (upperHalfPlaneInverseSquareCoefficient_pos hz).le
    · exact div_nonneg (Nat.cast_nonneg _) (by positivity)

/-- The complete real Poisson-defect summand is summable at every upper
observation point. -/
theorem summable_zetaUpperHyperbolicPoissonDefectSummand
    {z : ℂ} (hz : 0 < z.im) :
    Summable (zetaUpperHyperbolicPoissonDefectSummand z) := by
  apply
    (summable_distinct_zetaZeroInverseSquareSpectralRe.mul_left
      (2 * z.im * upperHalfPlaneInverseSquareCoefficient z)).of_nonneg_of_le
      (zetaUpperHyperbolicPoissonDefectSummand_nonneg hz)
  intro rho
  exact zetaUpperHyperbolicPoissonDefectSummand_le_inverseSquare hz rho

/-- The complete extended Poisson defect is therefore finite at every upper
observation point. -/
theorem riemannXiUpperHyperbolicPoissonDefectMass_ne_top
    {z : ℂ} (hz : 0 < z.im) :
    riemannXiUpperHyperbolicPoissonDefectMass z ≠ ∞ := by
  unfold riemannXiUpperHyperbolicPoissonDefectMass
  exact (summable_zetaUpperHyperbolicPoissonDefectSummand hz).tsum_ofReal_ne_top

/-- Strict order form of complete Poisson-mass finiteness. -/
theorem riemannXiUpperHyperbolicPoissonDefectMass_lt_top
    {z : ℂ} (hz : 0 < z.im) :
    riemannXiUpperHyperbolicPoissonDefectMass z < ∞ :=
  (lt_top_iff_ne_top).2
    (riemannXiUpperHyperbolicPoissonDefectMass_ne_top hz)

/-- The complete Poisson mass is exactly the extended-real embedding of its
convergent nonnegative real series. -/
theorem riemannXiUpperHyperbolicPoissonDefectMass_eq_ofReal_tsum
    {z : ℂ} (hz : 0 < z.im) :
    riemannXiUpperHyperbolicPoissonDefectMass z =
      ENNReal.ofReal
        (∑' rho : NontrivialZetaZero,
          zetaUpperHyperbolicPoissonDefectSummand z rho) := by
  unfold riemannXiUpperHyperbolicPoissonDefectMass
  exact (ENNReal.ofReal_tsum_of_nonneg
    (zetaUpperHyperbolicPoissonDefectSummand_nonneg hz)
    (summable_zetaUpperHyperbolicPoissonDefectSummand hz)).symm

/-- At every noncolliding upper point, the real logarithmic-defect summand is
summable.  The uniform zero gap supplies the finite comparison coefficient. -/
theorem summable_zetaUpperHyperbolicLogDefectSummand
    {z : ℂ} (hz : 0 < z.im) (hxi : riemannXiSpectral z ≠ 0) :
    Summable (zetaUpperHyperbolicLogDefectSummand z) := by
  obtain ⟨delta, hdelta, hgap⟩ :=
    exists_uniform_zetaSpectralCoordinate_gap_of_ne_zero hxi
  let C : ℝ := 1 + 2 * z.im / delta ^ 2
  have hC : 0 ≤ C := by
    dsimp [C]
    positivity
  apply
    ((summable_zetaUpperHyperbolicPoissonDefectSummand hz).mul_left C).of_nonneg_of_le
  · intro rho
    apply zetaUpperHyperbolicLogDefectSummand_nonneg hz rho
    intro heq
    apply hxi
    rw [heq]
    exact (riemannXiSpectral_eq_zero_iff_exists_zetaZero _).2 ⟨rho, rfl⟩
  · intro rho
    exact
      zetaUpperHyperbolicLogDefectSummand_le_gapCoefficient_mul_poisson
        hz hdelta (fun sigma _ ↦ hgap sigma) rho

/-- Hence the complete logarithmic defect is finite at every noncolliding
upper observation point. -/
theorem riemannXiUpperHyperbolicLogDefectMass_ne_top
    {z : ℂ} (hz : 0 < z.im) (hxi : riemannXiSpectral z ≠ 0) :
    riemannXiUpperHyperbolicLogDefectMass z ≠ ∞ := by
  unfold riemannXiUpperHyperbolicLogDefectMass
  exact
    (summable_zetaUpperHyperbolicLogDefectSummand hz hxi).tsum_ofReal_ne_top

/-- The complete logarithmic defect is exactly its convergent nonnegative
real series embedded in `ℝ≥0∞`. -/
theorem riemannXiUpperHyperbolicLogDefectMass_eq_ofReal_tsum
    {z : ℂ} (hz : 0 < z.im) (hxi : riemannXiSpectral z ≠ 0) :
    riemannXiUpperHyperbolicLogDefectMass z =
      ENNReal.ofReal
        (∑' rho : NontrivialZetaZero,
          zetaUpperHyperbolicLogDefectSummand z rho) := by
  unfold riemannXiUpperHyperbolicLogDefectMass
  apply Eq.symm
  apply ENNReal.ofReal_tsum_of_nonneg
  · intro rho
    apply zetaUpperHyperbolicLogDefectSummand_nonneg hz rho
    intro heq
    apply hxi
    rw [heq]
    exact (riemannXiSpectral_eq_zero_iff_exists_zetaZero _).2 ⟨rho, rfl⟩
  · exact summable_zetaUpperHyperbolicLogDefectSummand hz hxi

/-- The complete positive-proper-time heat action is finite at every
noncolliding upper point. -/
theorem riemannXiUpperHyperbolicHeatAction_ne_top
    {z : ℂ} (hz : 0 < z.im) (hxi : riemannXiSpectral z ≠ 0) :
    riemannXiUpperHyperbolicHeatAction z ≠ ∞ := by
  rw [riemannXiUpperHyperbolicHeatAction_eq_logDefectMass hz hxi]
  exact riemannXiUpperHyperbolicLogDefectMass_ne_top hz hxi

/-- The complete positive-proper-time heat action is the same convergent real
logarithmic-defect series embedded in `ℝ≥0∞`. -/
theorem riemannXiUpperHyperbolicHeatAction_eq_ofReal_tsum
    {z : ℂ} (hz : 0 < z.im) (hxi : riemannXiSpectral z ≠ 0) :
    riemannXiUpperHyperbolicHeatAction z =
      ENNReal.ofReal
        (∑' rho : NontrivialZetaZero,
          zetaUpperHyperbolicLogDefectSummand z rho) := by
  rw [riemannXiUpperHyperbolicHeatAction_eq_logDefectMass hz hxi,
    riemannXiUpperHyperbolicLogDefectMass_eq_ofReal_tsum hz hxi]

/-- The real elementary Blaschke derivative-variation summand is summable at
every upper observation point. -/
theorem summable_zetaUpperBlaschkeDerivativeVariationSummand
    {z : ℂ} (hz : 0 < z.im) :
    Summable (zetaUpperBlaschkeDerivativeVariationSummand z) := by
  refine
    ((summable_zetaUpperHyperbolicPoissonDefectSummand hz).mul_left
      (2 * z.im)⁻¹).congr fun rho => ?_
  rw [zetaUpperHyperbolicPoissonDefectSummand_eq_two_mul_im_mul_variation
    hz]
  field_simp [hz.ne']

/-- Thus the complete elementary Blaschke derivative variation is finite at
every upper observation point. -/
theorem riemannXiUpperBlaschkeDerivativeVariationMass_ne_top
    {z : ℂ} (hz : 0 < z.im) :
    riemannXiUpperBlaschkeDerivativeVariationMass z ≠ ∞ := by
  unfold riemannXiUpperBlaschkeDerivativeVariationMass
  exact
    (summable_zetaUpperBlaschkeDerivativeVariationSummand hz).tsum_ofReal_ne_top

/-- The complete elementary Blaschke variation is exactly its convergent
nonnegative real series embedded in `ℝ≥0∞`. -/
theorem riemannXiUpperBlaschkeDerivativeVariationMass_eq_ofReal_tsum
    {z : ℂ} (hz : 0 < z.im) :
    riemannXiUpperBlaschkeDerivativeVariationMass z =
      ENNReal.ofReal
        (∑' rho : NontrivialZetaZero,
          zetaUpperBlaschkeDerivativeVariationSummand z rho) := by
  unfold riemannXiUpperBlaschkeDerivativeVariationMass
  exact (ENNReal.ofReal_tsum_of_nonneg
    (zetaUpperBlaschkeDerivativeVariationSummand_nonneg z)
    (summable_zetaUpperBlaschkeDerivativeVariationSummand hz)).symm

end

end RiemannGaussian
