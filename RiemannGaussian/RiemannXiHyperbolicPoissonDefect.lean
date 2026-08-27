import RiemannGaussian.RiemannXiSpectralWindowMass

/-!
# The Poisson lower bound for the complete spectral defect

The logarithmic pseudo-hyperbolic defect has both an upper height bound and a
canonical lower bound.  The lower bound is the disk defect
`1 - rho_H(z, alpha)^2`, equivalently the upper-half-plane Poisson weight
`4 * Im(z) * Im(alpha) / |z - conj(alpha)|^2`.  This file proves that bound
per zero and then lifts it, with genuine analytic multiplicities, to the full
extended spectral divisor.
-/

open Complex Filter MeasureTheory Metric Polynomial Set Topology
open scoped Classical ENNReal Interval Topology

namespace RiemannGaussian

noncomputable section

/-- The disk defect `1 - rho^2` is exactly the upper-half-plane Poisson
weight in real coordinates. -/
theorem one_sub_sq_pairHyperbolicRadius_eq_height_div_lowerSq
    {d v a : ℝ} (hv : 0 < v) (ha : 0 < a) :
    1 - pairHyperbolicRadius d v a ^ 2 =
      4 * v * a / pairHyperbolicLowerSq d v a := by
  have hlower : 0 < pairHyperbolicLowerSq d v a :=
    pairHyperbolicLowerSq_pos ha hv
  have hratio :
      0 ≤ pairHyperbolicUpperSq d v a /
        pairHyperbolicLowerSq d v a :=
    div_nonneg (pairHyperbolicUpperSq_nonneg d v a) hlower.le
  unfold pairHyperbolicRadius
  rw [Real.sq_sqrt hratio]
  field_simp [ne_of_gt hlower]
  unfold pairHyperbolicLowerSq pairHyperbolicUpperSq
  ring

/-- The Poisson weight of one upper-half-plane pair is bounded by its
logarithmic pseudo-hyperbolic defect. -/
theorem height_div_lowerSq_le_neg_two_log_pairHyperbolicRadius
    {d v a : ℝ} (hv : 0 < v) (ha : 0 < a)
    (hupper : 0 < pairHyperbolicUpperSq d v a) :
    4 * v * a / pairHyperbolicLowerSq d v a ≤
      -2 * Real.log (pairHyperbolicRadius d v a) := by
  rw [← pairHyperbolicLogRatio_eq_neg_two_log_radius hv ha hupper]
  have hlower : 0 < pairHyperbolicLowerSq d v a :=
    pairHyperbolicLowerSq_pos ha hv
  have hratio :
      0 < pairHyperbolicLowerSq d v a /
        pairHyperbolicUpperSq d v a :=
    div_pos hlower hupper
  calc
    4 * v * a / pairHyperbolicLowerSq d v a =
        1 - (pairHyperbolicLowerSq d v a /
          pairHyperbolicUpperSq d v a)⁻¹ := by
      rw [inv_div]
      field_simp [ne_of_gt hlower]
      unfold pairHyperbolicLowerSq pairHyperbolicUpperSq
      ring
    _ ≤ Real.log
          (pairHyperbolicLowerSq d v a /
            pairHyperbolicUpperSq d v a) :=
      Real.one_sub_inv_le_log_of_pos hratio

/-- Coordinate-free Poisson lower bound for one distinct pair in the open
upper half-plane. -/
theorem height_div_conjugate_normSq_le_neg_two_log_upperHalfPlaneDistance
    {z alpha : ℂ} (hz : 0 < z.im) (halpha : 0 < alpha.im)
    (hne : z ≠ alpha) :
    4 * z.im * alpha.im /
        Complex.normSq (z - starRingEnd ℂ alpha) ≤
      -2 * Real.log (upperHalfPlanePseudoHyperbolicDistance z alpha) := by
  have hupperEq :
      pairHyperbolicUpperSq (z.re - alpha.re) z.im alpha.im =
        Complex.normSq (z - alpha) := by
    unfold pairHyperbolicUpperSq Complex.normSq
    simp
    ring
  have hlowerEq :
      pairHyperbolicLowerSq (z.re - alpha.re) z.im alpha.im =
        Complex.normSq (z - starRingEnd ℂ alpha) := by
    unfold pairHyperbolicLowerSq Complex.normSq
    simp
    ring
  have hupper :
      0 < pairHyperbolicUpperSq (z.re - alpha.re) z.im alpha.im := by
    rw [hupperEq]
    exact Complex.normSq_pos.mpr (sub_ne_zero.mpr hne)
  have halphaForm :
      (alpha.re : ℂ) + Complex.I * (alpha.im : ℂ) = alpha := by
    rw [mul_comm]
    exact Complex.re_add_im alpha
  have hzForm :
      (z.re : ℂ) + Complex.I * (z.im : ℂ) = z := by
    rw [mul_comm]
    exact Complex.re_add_im z
  have hdistance :
      upperHalfPlanePseudoHyperbolicDistance z alpha =
        pairHyperbolicRadius (z.re - alpha.re) z.im alpha.im := by
    rw [← halphaForm, ← hzForm,
      upperHalfPlanePseudoHyperbolicDistance_eq_pairRadius
        alpha.re alpha.im z.re z.im halpha hz]
    simp
  rw [hdistance, ← hlowerEq]
  exact height_div_lowerSq_le_neg_two_log_pairHyperbolicRadius
    hz halpha hupper

/-- Coordinate-free form of the exact disk-defect/Poisson-weight identity. -/
theorem one_sub_sq_upperHalfPlanePseudoHyperbolicDistance_eq_height_div_normSq
    {z alpha : ℂ} (hz : 0 < z.im) (halpha : 0 < alpha.im) :
    1 - upperHalfPlanePseudoHyperbolicDistance z alpha ^ 2 =
      4 * z.im * alpha.im /
        Complex.normSq (z - starRingEnd ℂ alpha) := by
  have hlowerEq :
      pairHyperbolicLowerSq (z.re - alpha.re) z.im alpha.im =
        Complex.normSq (z - starRingEnd ℂ alpha) := by
    unfold pairHyperbolicLowerSq Complex.normSq
    simp
    ring
  have halphaForm :
      (alpha.re : ℂ) + Complex.I * (alpha.im : ℂ) = alpha := by
    rw [mul_comm]
    exact Complex.re_add_im alpha
  have hzForm :
      (z.re : ℂ) + Complex.I * (z.im : ℂ) = z := by
    rw [mul_comm]
    exact Complex.re_add_im z
  have hdistance :
      upperHalfPlanePseudoHyperbolicDistance z alpha =
        pairHyperbolicRadius (z.re - alpha.re) z.im alpha.im := by
    rw [← halphaForm, ← hzForm,
      upperHalfPlanePseudoHyperbolicDistance_eq_pairRadius
        alpha.re alpha.im z.re z.im halpha hz]
    simp
  rw [hdistance, ← hlowerEq]
  exact one_sub_sq_pairHyperbolicRadius_eq_height_div_lowerSq hz halpha

/-- The disk defect itself is bounded by the logarithmic defect. -/
theorem one_sub_sq_upperHalfPlanePseudoHyperbolicDistance_le_neg_two_log
    {z alpha : ℂ} (hz : 0 < z.im) (halpha : 0 < alpha.im)
    (hne : z ≠ alpha) :
    1 - upperHalfPlanePseudoHyperbolicDistance z alpha ^ 2 ≤
      -2 * Real.log (upperHalfPlanePseudoHyperbolicDistance z alpha) := by
  rw [one_sub_sq_upperHalfPlanePseudoHyperbolicDistance_eq_height_div_normSq
    hz halpha]
  exact height_div_conjugate_normSq_le_neg_two_log_upperHalfPlaneDistance
    hz halpha hne

/-! ## Multiplicity-counted spectral Poisson mass -/

/-- The Poisson defect contributed by one upper spectral zero, with its
genuine analytic multiplicity. -/
def zetaUpperHyperbolicPoissonDefectSummand
    (z : ℂ) (rho : NontrivialZetaZero) : ℝ :=
  if 0 < (zetaSpectralCoordinate rho.1).im then
    (analyticZetaZeroMultiplicity rho : ℝ) *
      (4 * z.im * (zetaSpectralCoordinate rho.1).im /
        Complex.normSq
          (z - starRingEnd ℂ (zetaSpectralCoordinate rho.1)))
  else 0

/-- Every selected spectral Poisson defect is nonnegative at an upper
observation point. -/
theorem zetaUpperHyperbolicPoissonDefectSummand_nonneg
    {z : ℂ} (hz : 0 < z.im) (rho : NontrivialZetaZero) :
    0 ≤ zetaUpperHyperbolicPoissonDefectSummand z rho := by
  by_cases hupper : 0 < (zetaSpectralCoordinate rho.1).im
  · rw [zetaUpperHyperbolicPoissonDefectSummand, if_pos hupper]
    exact mul_nonneg (Nat.cast_nonneg _)
      (div_nonneg (by positivity) (Complex.normSq_nonneg _))
  · rw [zetaUpperHyperbolicPoissonDefectSummand, if_neg hupper]

/-- An upper spectral zero contributes a strictly positive Poisson defect at
every upper observation point.  Unlike the logarithmic defect, this expression
has no collision singularity because its pole is at the reflected lower point.
-/
theorem zetaUpperHyperbolicPoissonDefectSummand_pos
    {z : ℂ} (hz : 0 < z.im) (rho : NontrivialZetaZero)
    (hupper : 0 < (zetaSpectralCoordinate rho.1).im) :
    0 < zetaUpperHyperbolicPoissonDefectSummand z rho := by
  let alpha : ℂ := zetaSpectralCoordinate rho.1
  have hneConj : z ≠ starRingEnd ℂ alpha := by
    intro heq
    have him : z.im = -alpha.im := by
      rw [heq]
      simp
    linarith
  have hden :
      0 < Complex.normSq (z - starRingEnd ℂ alpha) :=
    Complex.normSq_pos.mpr (sub_ne_zero.mpr hneConj)
  rw [zetaUpperHyperbolicPoissonDefectSummand, if_pos hupper]
  apply mul_pos
  · exact_mod_cast analyticZetaZeroMultiplicity_positive rho
  · apply div_pos
    · positivity
    · simpa only [alpha] using hden

/-- Per zero, the Poisson defect is no larger than the logarithmic defect. -/
theorem zetaUpperHyperbolicPoissonDefectSummand_le_logDefectSummand
    {z : ℂ} (hz : 0 < z.im) (rho : NontrivialZetaZero)
    (hne : z ≠ zetaSpectralCoordinate rho.1) :
    zetaUpperHyperbolicPoissonDefectSummand z rho ≤
      zetaUpperHyperbolicLogDefectSummand z rho := by
  by_cases hupper : 0 < (zetaSpectralCoordinate rho.1).im
  · rw [zetaUpperHyperbolicPoissonDefectSummand, if_pos hupper,
      zetaUpperHyperbolicLogDefectSummand, if_pos hupper]
    exact mul_le_mul_of_nonneg_left
      (height_div_conjugate_normSq_le_neg_two_log_upperHalfPlaneDistance
        hz hupper hne)
      (Nat.cast_nonneg _)
  · rw [zetaUpperHyperbolicPoissonDefectSummand, if_neg hupper,
      zetaUpperHyperbolicLogDefectSummand, if_neg hupper]

/-- The complete extended Poisson defect of the upper spectral-xi divisor. -/
def riemannXiUpperHyperbolicPoissonDefectMass (z : ℂ) : ℝ≥0∞ :=
  ∑' rho : NontrivialZetaZero,
    ENNReal.ofReal (zetaUpperHyperbolicPoissonDefectSummand z rho)

/-- The Poisson defect in one finite symmetric spectral window. -/
def riemannXiUpperHyperbolicPoissonDefectWindow
    (z : ℂ) (T : ℝ) : ℝ≥0∞ :=
  ∑ rho ∈ spectralZetaZeroWindow T,
    ENNReal.ofReal (zetaUpperHyperbolicPoissonDefectSummand z rho)

/-- Cofinal finite windows exhaust the complete Poisson defect, with no
finiteness assumption on its value. -/
theorem tendsto_riemannXiUpperHyperbolicPoissonDefectWindow (z : ℂ) :
    Tendsto (riemannXiUpperHyperbolicPoissonDefectWindow z) atTop
      (nhds (riemannXiUpperHyperbolicPoissonDefectMass z)) := by
  unfold riemannXiUpperHyperbolicPoissonDefectWindow
    riemannXiUpperHyperbolicPoissonDefectMass
  exact ENNReal.summable.hasSum.comp tendsto_spectralZetaZeroWindow_atTop

/-- In every finite window, the Poisson defect is below the logarithmic
defect at a noncolliding upper observation point. -/
theorem riemannXiUpperHyperbolicPoissonDefectWindow_le_logDefectWindow
    {z : ℂ} (hz : 0 < z.im) (hxi : riemannXiSpectral z ≠ 0) (T : ℝ) :
    riemannXiUpperHyperbolicPoissonDefectWindow z T ≤
      riemannXiUpperHyperbolicLogDefectWindow z T := by
  unfold riemannXiUpperHyperbolicPoissonDefectWindow
    riemannXiUpperHyperbolicLogDefectWindow
  apply Finset.sum_le_sum
  intro rho _hrho
  apply ENNReal.ofReal_le_ofReal
  apply zetaUpperHyperbolicPoissonDefectSummand_le_logDefectSummand hz
  intro heq
  apply hxi
  rw [heq]
  exact (riemannXiSpectral_eq_zero_iff_exists_zetaZero _).2 ⟨rho, rfl⟩

/-- The complete Poisson defect is below the complete logarithmic defect,
including when either side is infinite. -/
theorem riemannXiUpperHyperbolicPoissonDefectMass_le_logDefectMass
    {z : ℂ} (hz : 0 < z.im) (hxi : riemannXiSpectral z ≠ 0) :
    riemannXiUpperHyperbolicPoissonDefectMass z ≤
      riemannXiUpperHyperbolicLogDefectMass z := by
  unfold riemannXiUpperHyperbolicPoissonDefectMass
    riemannXiUpperHyperbolicLogDefectMass
  apply ENNReal.tsum_le_tsum
  intro rho
  apply ENNReal.ofReal_le_ofReal
  apply zetaUpperHyperbolicPoissonDefectSummand_le_logDefectSummand hz
  intro heq
  apply hxi
  rw [heq]
  exact (riemannXiSpectral_eq_zero_iff_exists_zetaZero _).2 ⟨rho, rfl⟩

/-- Equivalently, the complete Poisson defect is a rigorous lower bound for
the full positive-proper-time spectral heat action. -/
theorem riemannXiUpperHyperbolicPoissonDefectMass_le_heatAction
    {z : ℂ} (hz : 0 < z.im) (hxi : riemannXiSpectral z ≠ 0) :
    riemannXiUpperHyperbolicPoissonDefectMass z ≤
      riemannXiUpperHyperbolicHeatAction z := by
  rw [riemannXiUpperHyperbolicHeatAction_eq_logDefectMass hz hxi]
  exact riemannXiUpperHyperbolicPoissonDefectMass_le_logDefectMass hz hxi

/-- At every upper observation point, vanishing of the complete Poisson
defect is exactly RH. -/
theorem riemannXiUpperHyperbolicPoissonDefectMass_eq_zero_iff_riemannHypothesis
    {z : ℂ} (hz : 0 < z.im) :
    riemannXiUpperHyperbolicPoissonDefectMass z = 0 ↔
      RiemannHypothesis := by
  constructor
  · intro hzero
    by_contra hRH
    obtain ⟨w, hwzero, hwupper⟩ :=
      exists_riemannXiSpectral_upper_zero_of_not_riemannHypothesis hRH
    obtain ⟨rho, rfl⟩ :=
      (riemannXiSpectral_eq_zero_iff_exists_zetaZero w).mp hwzero
    have hsummand :
        0 < zetaUpperHyperbolicPoissonDefectSummand z rho :=
      zetaUpperHyperbolicPoissonDefectSummand_pos hz rho hwupper
    have hterm :
        0 < ENNReal.ofReal
          (zetaUpperHyperbolicPoissonDefectSummand z rho) :=
      ENNReal.ofReal_pos.mpr hsummand
    have hle :
        ENNReal.ofReal
            (zetaUpperHyperbolicPoissonDefectSummand z rho) ≤
          riemannXiUpperHyperbolicPoissonDefectMass z :=
      ENNReal.le_tsum rho
    rw [hzero] at hle
    exact (not_lt_of_ge hle) hterm
  · intro hRH
    unfold riemannXiUpperHyperbolicPoissonDefectMass
    rw [ENNReal.tsum_eq_zero]
    intro rho
    have him : (zetaSpectralCoordinate rho.1).im = 0 :=
      (riemannHypothesis_iff_spectralCoordinate_real.mp hRH)
        rho.1 rho.2.1 rho.2.2.1 rho.2.2.2
    have hnupper : ¬0 < (zetaSpectralCoordinate rho.1).im := by
      linarith
    rw [zetaUpperHyperbolicPoissonDefectSummand, if_neg hnupper,
      ENNReal.ofReal_zero]

/-- The Poisson-weighted divisor statistic and the full absolute
critical-line displacement have exactly the same zero set. -/
theorem riemannXiUpperHyperbolicPoissonDefectMass_eq_zero_iff_absoluteDeviation
    {z : ℂ} (hz : 0 < z.im) :
    riemannXiUpperHyperbolicPoissonDefectMass z = 0 ↔
      riemannXiAbsoluteCriticalLineDeviationMass = 0 := by
  rw [riemannXiUpperHyperbolicPoissonDefectMass_eq_zero_iff_riemannHypothesis
      hz,
    riemannXiAbsoluteCriticalLineDeviationMass_eq_zero_iff_riemannHypothesis]

end

end RiemannGaussian
