import RiemannGaussian.RiemannXiSpectralReflectionPairing

/-!
# Quantitative equivalence of logarithmic and Poisson spectral defect

Poisson defect is always below logarithmic pseudo-hyperbolic defect.  At a
fixed observation point outside the spectral-xi divisor, the converse holds
up to one finite positive constant.  The proof uses the uniform Euclidean gap
from that point to every spectral zero and the strict critical-strip height
bound.  Both complete masses remain extended nonnegative reals.
-/

open Complex Filter MeasureTheory Metric Polynomial Set Topology
open scoped Classical ENNReal Interval Topology

namespace RiemannGaussian

noncomputable section

/-- A lower bound on numerator distance and an upper bound `a ≤ 1/2` make
logarithmic pair defect at most a fixed multiple of Poisson pair defect. -/
theorem neg_two_log_pairHyperbolicRadius_le_gapCoefficient_mul_poisson
    {d v a delta : ℝ} (hv : 0 < v) (ha : 0 < a)
    (hupper : 0 < pairHyperbolicUpperSq d v a)
    (hdelta : 0 < delta)
    (hgap : delta ^ 2 ≤ pairHyperbolicUpperSq d v a)
    (haHalf : a ≤ 1 / 2) :
    -2 * Real.log (pairHyperbolicRadius d v a) ≤
      (1 + 2 * v / delta ^ 2) *
        (4 * v * a / pairHyperbolicLowerSq d v a) := by
  have hlower : 0 < pairHyperbolicLowerSq d v a :=
    pairHyperbolicLowerSq_pos ha hv
  have hnum : 0 ≤ 4 * v * a := by positivity
  have hnumLe : 4 * v * a ≤ 2 * v := by
    nlinarith
  have hfrac :
      4 * v * a / pairHyperbolicUpperSq d v a ≤
        2 * v / delta ^ 2 := by
    calc
      4 * v * a / pairHyperbolicUpperSq d v a ≤
          2 * v / pairHyperbolicUpperSq d v a :=
        div_le_div_of_nonneg_right hnumLe hupper.le
      _ ≤ 2 * v / delta ^ 2 :=
        div_le_div_of_nonneg_left (by positivity)
          (sq_pos_of_pos hdelta) hgap
  have hratioEq :
      pairHyperbolicLowerSq d v a /
          pairHyperbolicUpperSq d v a =
        1 + 4 * v * a / pairHyperbolicUpperSq d v a := by
    field_simp [ne_of_gt hupper]
    unfold pairHyperbolicLowerSq pairHyperbolicUpperSq
    ring
  have hratioLe :
      pairHyperbolicLowerSq d v a /
          pairHyperbolicUpperSq d v a ≤
        1 + 2 * v / delta ^ 2 := by
    rw [hratioEq]
    linarith
  have hfactor :
      4 * v * a / pairHyperbolicUpperSq d v a =
        (pairHyperbolicLowerSq d v a /
          pairHyperbolicUpperSq d v a) *
            (4 * v * a / pairHyperbolicLowerSq d v a) := by
    field_simp [ne_of_gt hupper, ne_of_gt hlower]
  calc
    -2 * Real.log (pairHyperbolicRadius d v a) ≤
        4 * v * a / pairHyperbolicUpperSq d v a :=
      neg_two_log_pairHyperbolicRadius_le_height_div_upperSq
        hv ha hupper
    _ = (pairHyperbolicLowerSq d v a /
          pairHyperbolicUpperSq d v a) *
            (4 * v * a / pairHyperbolicLowerSq d v a) := hfactor
    _ ≤ (1 + 2 * v / delta ^ 2) *
          (4 * v * a / pairHyperbolicLowerSq d v a) :=
      mul_le_mul_of_nonneg_right hratioLe (div_nonneg hnum hlower.le)

/-- Coordinate-free reverse comparison for one upper-half-plane pair. -/
theorem neg_two_log_upperHalfPlaneDistance_le_gapCoefficient_mul_poisson
    {z alpha : ℂ} (hz : 0 < z.im) (halpha : 0 < alpha.im)
    (hne : z ≠ alpha) {delta : ℝ} (hdelta : 0 < delta)
    (hgap : delta ≤ ‖z - alpha‖) (halphaHalf : alpha.im ≤ 1 / 2) :
    -2 * Real.log (upperHalfPlanePseudoHyperbolicDistance z alpha) ≤
      (1 + 2 * z.im / delta ^ 2) *
        (4 * z.im * alpha.im /
          Complex.normSq (z - starRingEnd ℂ alpha)) := by
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
  have hgapSq :
      delta ^ 2 ≤
        pairHyperbolicUpperSq (z.re - alpha.re) z.im alpha.im := by
    rw [hupperEq, Complex.normSq_eq_norm_sq]
    have hnorm : 0 ≤ ‖z - alpha‖ := norm_nonneg _
    nlinarith
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
  exact
    neg_two_log_pairHyperbolicRadius_le_gapCoefficient_mul_poisson
      hz halpha hupper hdelta hgapSq halphaHalf

/-- Per selected upper spectral zero, a common upper-divisor Euclidean gap
controls logarithmic defect by the corresponding Poisson defect. -/
theorem zetaUpperHyperbolicLogDefectSummand_le_gapCoefficient_mul_poisson
    {z : ℂ} (hz : 0 < z.im) {delta : ℝ} (hdelta : 0 < delta)
    (hgap : ∀ rho : NontrivialZetaZero,
      0 < (zetaSpectralCoordinate rho.1).im →
        delta ≤ ‖z - zetaSpectralCoordinate rho.1‖)
    (rho : NontrivialZetaZero) :
    zetaUpperHyperbolicLogDefectSummand z rho ≤
      (1 + 2 * z.im / delta ^ 2) *
        zetaUpperHyperbolicPoissonDefectSummand z rho := by
  by_cases hupper : 0 < (zetaSpectralCoordinate rho.1).im
  · have hne : z ≠ zetaSpectralCoordinate rho.1 := by
      intro heq
      have hzeroNorm : ‖z - zetaSpectralCoordinate rho.1‖ = 0 := by
        rw [heq, sub_self, norm_zero]
      have := hgap rho hupper
      rw [hzeroNorm] at this
      linarith
    have hhalf : (zetaSpectralCoordinate rho.1).im ≤ 1 / 2 := by
      have habs := NontrivialZetaZero.abs_spectralCoordinate_im_lt_half rho
      exact (le_abs_self _).trans habs.le
    rw [zetaUpperHyperbolicLogDefectSummand, if_pos hupper,
      zetaUpperHyperbolicPoissonDefectSummand, if_pos hupper]
    calc
      (analyticZetaZeroMultiplicity rho : ℝ) *
          (-2 * Real.log
            (upperHalfPlanePseudoHyperbolicDistance z
              (zetaSpectralCoordinate rho.1))) ≤
        (analyticZetaZeroMultiplicity rho : ℝ) *
          ((1 + 2 * z.im / delta ^ 2) *
            (4 * z.im * (zetaSpectralCoordinate rho.1).im /
              Complex.normSq
                (z - starRingEnd ℂ
                  (zetaSpectralCoordinate rho.1)))) :=
        mul_le_mul_of_nonneg_left
          (neg_two_log_upperHalfPlaneDistance_le_gapCoefficient_mul_poisson
            hz hupper hne hdelta (hgap rho hupper) hhalf)
          (Nat.cast_nonneg _)
      _ = (1 + 2 * z.im / delta ^ 2) *
          ((analyticZetaZeroMultiplicity rho : ℝ) *
            (4 * z.im * (zetaSpectralCoordinate rho.1).im /
              Complex.normSq
                (z - starRingEnd ℂ
                  (zetaSpectralCoordinate rho.1)))) := by ring
  · rw [zetaUpperHyperbolicLogDefectSummand, if_neg hupper,
      zetaUpperHyperbolicPoissonDefectSummand, if_neg hupper, mul_zero]

/-- The complete logarithmic defect is bounded by a finite upper-divisor gap
coefficient times the complete Poisson defect. -/
theorem riemannXiUpperHyperbolicLogDefectMass_le_gapCoefficient_mul_poissonMass
    {z : ℂ} (hz : 0 < z.im) {delta : ℝ} (hdelta : 0 < delta)
    (hgap : ∀ rho : NontrivialZetaZero,
      0 < (zetaSpectralCoordinate rho.1).im →
        delta ≤ ‖z - zetaSpectralCoordinate rho.1‖) :
    riemannXiUpperHyperbolicLogDefectMass z ≤
      ENNReal.ofReal (1 + 2 * z.im / delta ^ 2) *
        riemannXiUpperHyperbolicPoissonDefectMass z := by
  unfold riemannXiUpperHyperbolicLogDefectMass
    riemannXiUpperHyperbolicPoissonDefectMass
  have hcoefficient : 0 ≤ 1 + 2 * z.im / delta ^ 2 := by positivity
  calc
    (∑' rho : NontrivialZetaZero,
        ENNReal.ofReal (zetaUpperHyperbolicLogDefectSummand z rho)) ≤
        ∑' rho : NontrivialZetaZero,
          ENNReal.ofReal
            ((1 + 2 * z.im / delta ^ 2) *
              zetaUpperHyperbolicPoissonDefectSummand z rho) := by
      apply ENNReal.tsum_le_tsum
      intro rho
      exact ENNReal.ofReal_le_ofReal
        (zetaUpperHyperbolicLogDefectSummand_le_gapCoefficient_mul_poisson
          hz hdelta hgap rho)
    _ = ENNReal.ofReal (1 + 2 * z.im / delta ^ 2) *
        ∑' rho : NontrivialZetaZero,
          ENNReal.ofReal
            (zetaUpperHyperbolicPoissonDefectSummand z rho) := by
      simp_rw [ENNReal.ofReal_mul hcoefficient]
      exact ENNReal.tsum_mul_left

/-- At every noncolliding upper observation point, logarithmic and Poisson
defect are comparable in both directions by a finite positive constant. -/
theorem exists_pos_riemannXiUpperHyperbolicDefectMass_comparable_to_poisson
    {z : ℂ} (hz : 0 < z.im) (hxi : riemannXiSpectral z ≠ 0) :
    ∃ C : ℝ, 0 < C ∧
      riemannXiUpperHyperbolicPoissonDefectMass z ≤
        riemannXiUpperHyperbolicLogDefectMass z ∧
      riemannXiUpperHyperbolicLogDefectMass z ≤
        ENNReal.ofReal C *
          riemannXiUpperHyperbolicPoissonDefectMass z := by
  obtain ⟨delta, hdelta, hgap⟩ :=
    exists_uniform_zetaSpectralCoordinate_gap_of_ne_zero hxi
  let C : ℝ := 1 + 2 * z.im / delta ^ 2
  have hC : 0 < C := by
    dsimp [C]
    positivity
  exact ⟨C, hC,
    riemannXiUpperHyperbolicPoissonDefectMass_le_logDefectMass hz hxi,
    riemannXiUpperHyperbolicLogDefectMass_le_gapCoefficient_mul_poissonMass
      hz hdelta (fun rho _ ↦ hgap rho)⟩

/-- The same two-sided comparison stated for the complete proper-time heat
action. -/
theorem exists_pos_riemannXiUpperHyperbolicHeatAction_comparable_to_poisson
    {z : ℂ} (hz : 0 < z.im) (hxi : riemannXiSpectral z ≠ 0) :
    ∃ C : ℝ, 0 < C ∧
      riemannXiUpperHyperbolicPoissonDefectMass z ≤
        riemannXiUpperHyperbolicHeatAction z ∧
      riemannXiUpperHyperbolicHeatAction z ≤
        ENNReal.ofReal C *
          riemannXiUpperHyperbolicPoissonDefectMass z := by
  obtain ⟨C, hC, hlower, hupper⟩ :=
    exists_pos_riemannXiUpperHyperbolicDefectMass_comparable_to_poisson
      hz hxi
  rw [riemannXiUpperHyperbolicHeatAction_eq_logDefectMass hz hxi]
  exact ⟨C, hC, hlower, hupper⟩

end

end RiemannGaussian
