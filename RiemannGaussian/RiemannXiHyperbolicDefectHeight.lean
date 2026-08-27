import RiemannGaussian.FiniteToEntireProperTimeActionTransfer

/-!
# Comparing the complete spectral defect with spectral height

This file quantitatively connects the two entire-side endpoint objects.  At
an observation point outside the spectral-xi divisor, continuity gives a
uniform positive distance from every spectral zero.  The elementary bound
`log(1+x) ≤ x` then controls each logarithmic pseudo-hyperbolic defect by
its upper spectral height.  Summing in `ℝ≥0∞` preserves the possibility of
divergence and introduces no finiteness hypothesis.
-/

open Complex Filter MeasureTheory Metric Polynomial Set Topology
open scoped Classical ENNReal Interval Topology

namespace RiemannGaussian

noncomputable section

/-- Any point outside the spectral-xi divisor has one positive Euclidean gap
from every nontrivial spectral zero. -/
theorem exists_uniform_zetaSpectralCoordinate_gap_of_ne_zero
    {z : ℂ} (hxi : riemannXiSpectral z ≠ 0) :
    ∃ delta : ℝ, 0 < delta ∧
      ∀ rho : NontrivialZetaZero,
        delta ≤ ‖z - zetaSpectralCoordinate rho.1‖ := by
  let U : Set ℂ := {w | riemannXiSpectral w ≠ 0}
  have hUOpen : IsOpen U :=
    isOpen_ne.preimage differentiable_riemannXiSpectral.continuous
  have hzU : z ∈ U := hxi
  obtain ⟨delta, hdelta, hball⟩ :=
    (Metric.isOpen_iff.mp hUOpen) z hzU
  refine ⟨delta, hdelta, ?_⟩
  intro rho
  by_contra hgap
  have hlt : ‖z - zetaSpectralCoordinate rho.1‖ < delta :=
    lt_of_not_ge hgap
  have hmem : zetaSpectralCoordinate rho.1 ∈ ball z delta := by
    simpa only [mem_ball, dist_eq, norm_sub_rev] using hlt
  have hnonzero := hball hmem
  exact hnonzero
    ((riemannXiSpectral_eq_zero_iff_exists_zetaZero _).2 ⟨rho, rfl⟩)

/-- One logarithmic pair defect is bounded by its height numerator divided by
the squared distance to the observation point. -/
theorem neg_two_log_pairHyperbolicRadius_le_height_div_upperSq
    {d v a : ℝ} (hv : 0 < v) (ha : 0 < a)
    (hupper : 0 < pairHyperbolicUpperSq d v a) :
    -2 * Real.log (pairHyperbolicRadius d v a) ≤
      4 * v * a / pairHyperbolicUpperSq d v a := by
  rw [← pairHyperbolicLogRatio_eq_neg_two_log_radius hv ha hupper]
  have hlower : 0 < pairHyperbolicLowerSq d v a :=
    pairHyperbolicLowerSq_pos ha hv
  calc
    Real.log
          (pairHyperbolicLowerSq d v a /
            pairHyperbolicUpperSq d v a) ≤
        pairHyperbolicLowerSq d v a /
            pairHyperbolicUpperSq d v a - 1 :=
      Real.log_le_sub_one_of_pos (div_pos hlower hupper)
    _ = 4 * v * a / pairHyperbolicUpperSq d v a := by
      field_simp [ne_of_gt hupper]
      unfold pairHyperbolicLowerSq pairHyperbolicUpperSq
      ring

/-- Coordinate-free form of the same one-zero logarithmic-defect bound. -/
theorem neg_two_log_upperHalfPlanePseudoHyperbolicDistance_le_height_div_normSq
    {z alpha : ℂ} (hz : 0 < z.im) (halpha : 0 < alpha.im)
    (hne : z ≠ alpha) :
    -2 * Real.log (upperHalfPlanePseudoHyperbolicDistance z alpha) ≤
      4 * z.im * alpha.im / Complex.normSq (z - alpha) := by
  have hupperEq :
      pairHyperbolicUpperSq (z.re - alpha.re) z.im alpha.im =
        Complex.normSq (z - alpha) := by
    unfold pairHyperbolicUpperSq Complex.normSq
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
  rw [hdistance, ← hupperEq]
  exact neg_two_log_pairHyperbolicRadius_le_height_div_upperSq
    hz halpha hupper

/-- A common Euclidean gap turns the one-zero estimate into a linear bound
by upper height. -/
theorem neg_two_log_upperHalfPlanePseudoHyperbolicDistance_le_mul_height_of_gap
    {z alpha : ℂ} (hz : 0 < z.im) (halpha : 0 < alpha.im)
    (hne : z ≠ alpha) {delta : ℝ} (hdelta : 0 < delta)
    (hgap : delta ≤ ‖z - alpha‖) :
    -2 * Real.log (upperHalfPlanePseudoHyperbolicDistance z alpha) ≤
      (4 * z.im / delta ^ 2) * alpha.im := by
  have hnormSq : delta ^ 2 ≤ Complex.normSq (z - alpha) := by
    rw [Complex.normSq_eq_norm_sq]
    have hnorm : 0 ≤ ‖z - alpha‖ := norm_nonneg _
    nlinarith
  have hnumerator : 0 ≤ 4 * z.im * alpha.im := by positivity
  calc
    -2 * Real.log (upperHalfPlanePseudoHyperbolicDistance z alpha) ≤
        4 * z.im * alpha.im / Complex.normSq (z - alpha) :=
      neg_two_log_upperHalfPlanePseudoHyperbolicDistance_le_height_div_normSq
        hz halpha hne
    _ ≤ 4 * z.im * alpha.im / delta ^ 2 :=
      div_le_div_of_nonneg_left hnumerator (sq_pos_of_pos hdelta) hnormSq
    _ = (4 * z.im / delta ^ 2) * alpha.im := by ring

/-- The multiplicity-counted logarithmic defect of one spectral zero is
bounded by the same gap coefficient times its upper-height summand. -/
theorem zetaUpperHyperbolicLogDefectSummand_le_mul_heightSummand_of_gap
    {z : ℂ} (hz : 0 < z.im) {delta : ℝ} (hdelta : 0 < delta)
    (hgap : ∀ rho : NontrivialZetaZero,
      delta ≤ ‖z - zetaSpectralCoordinate rho.1‖)
    (rho : NontrivialZetaZero) :
    zetaUpperHyperbolicLogDefectSummand z rho ≤
      (4 * z.im / delta ^ 2) *
        zetaUpperSpectralHeightSummand rho := by
  by_cases hupper : 0 < (zetaSpectralCoordinate rho.1).im
  · have hne : z ≠ zetaSpectralCoordinate rho.1 := by
      intro heq
      have hzeroNorm : ‖z - zetaSpectralCoordinate rho.1‖ = 0 := by
        rw [heq, sub_self, norm_zero]
      have := hgap rho
      rw [hzeroNorm] at this
      linarith
    rw [zetaUpperHyperbolicLogDefectSummand, if_pos hupper,
      zetaUpperSpectralHeightSummand, if_pos hupper]
    calc
      (analyticZetaZeroMultiplicity rho : ℝ) *
            (-2 * Real.log
              (upperHalfPlanePseudoHyperbolicDistance z
                (zetaSpectralCoordinate rho.1))) ≤
          (analyticZetaZeroMultiplicity rho : ℝ) *
            ((4 * z.im / delta ^ 2) *
              (zetaSpectralCoordinate rho.1).im) :=
        mul_le_mul_of_nonneg_left
          (neg_two_log_upperHalfPlanePseudoHyperbolicDistance_le_mul_height_of_gap
            hz hupper hne hdelta (hgap rho))
          (Nat.cast_nonneg _)
      _ = (4 * z.im / delta ^ 2) *
          ((analyticZetaZeroMultiplicity rho : ℝ) *
            (zetaSpectralCoordinate rho.1).im) := by ring
  · rw [zetaUpperHyperbolicLogDefectSummand, if_neg hupper,
      zetaUpperSpectralHeightSummand, if_neg hupper, mul_zero]

/-- The complete spectral logarithmic defect is bounded by the complete
upper-height mass times the explicit common-gap coefficient. -/
theorem riemannXiUpperHyperbolicLogDefectMass_le_heightMass_of_gap
    {z : ℂ} (hz : 0 < z.im) {delta : ℝ} (hdelta : 0 < delta)
    (hgap : ∀ rho : NontrivialZetaZero,
      delta ≤ ‖z - zetaSpectralCoordinate rho.1‖) :
    riemannXiUpperHyperbolicLogDefectMass z ≤
      ENNReal.ofReal (4 * z.im / delta ^ 2) *
        riemannXiUpperSpectralHeightMass := by
  unfold riemannXiUpperHyperbolicLogDefectMass
    riemannXiUpperSpectralHeightMass
  have hcoefficient : 0 ≤ 4 * z.im / delta ^ 2 := by positivity
  calc
    (∑' rho : NontrivialZetaZero,
        ENNReal.ofReal (zetaUpperHyperbolicLogDefectSummand z rho)) ≤
        ∑' rho : NontrivialZetaZero,
          ENNReal.ofReal
            ((4 * z.im / delta ^ 2) *
              zetaUpperSpectralHeightSummand rho) := by
      apply ENNReal.tsum_le_tsum
      intro rho
      exact ENNReal.ofReal_le_ofReal
        (zetaUpperHyperbolicLogDefectSummand_le_mul_heightSummand_of_gap
          hz hdelta hgap rho)
    _ = ENNReal.ofReal (4 * z.im / delta ^ 2) *
          ∑' rho : NontrivialZetaZero,
            ENNReal.ofReal (zetaUpperSpectralHeightSummand rho) := by
      simp_rw [ENNReal.ofReal_mul hcoefficient]
      exact ENNReal.tsum_mul_left

/-- At every noncolliding upper observation point, one finite positive
constant controls the complete spectral logarithmic defect by the complete
upper-height mass. -/
theorem exists_pos_riemannXiUpperHyperbolicLogDefectMass_le_heightMass
    {z : ℂ} (hz : 0 < z.im) (hxi : riemannXiSpectral z ≠ 0) :
    ∃ C : ℝ, 0 < C ∧
      riemannXiUpperHyperbolicLogDefectMass z ≤
        ENNReal.ofReal C * riemannXiUpperSpectralHeightMass := by
  obtain ⟨delta, hdelta, hgap⟩ :=
    exists_uniform_zetaSpectralCoordinate_gap_of_ne_zero hxi
  let C : ℝ := 4 * z.im / delta ^ 2
  have hC : 0 < C := by
    dsimp [C]
    positivity
  exact ⟨C, hC,
    riemannXiUpperHyperbolicLogDefectMass_le_heightMass_of_gap
      hz hdelta hgap⟩

/-- The same comparison stated directly for the complete proper-time heat
action. -/
theorem exists_pos_riemannXiUpperHyperbolicHeatAction_le_heightMass
    {z : ℂ} (hz : 0 < z.im) (hxi : riemannXiSpectral z ≠ 0) :
    ∃ C : ℝ, 0 < C ∧
      riemannXiUpperHyperbolicHeatAction z ≤
        ENNReal.ofReal C * riemannXiUpperSpectralHeightMass := by
  obtain ⟨C, hC, hbound⟩ :=
    exists_pos_riemannXiUpperHyperbolicLogDefectMass_le_heightMass hz hxi
  rw [riemannXiUpperHyperbolicHeatAction_eq_logDefectMass hz hxi]
  exact ⟨C, hC, hbound⟩

/-- Finiteness of the complete upper spectral height mass forces finiteness
of the complete logarithmic proper-time action at every noncolliding upper
observation point. -/
theorem riemannXiUpperHyperbolicHeatAction_ne_top_of_heightMass_ne_top
    {z : ℂ} (hz : 0 < z.im) (hxi : riemannXiSpectral z ≠ 0)
    (hheight : riemannXiUpperSpectralHeightMass ≠ ⊤) :
    riemannXiUpperHyperbolicHeatAction z ≠ ⊤ := by
  obtain ⟨C, _hC, hbound⟩ :=
    exists_pos_riemannXiUpperHyperbolicHeatAction_le_heightMass hz hxi
  have hproduct :
      ENNReal.ofReal C * riemannXiUpperSpectralHeightMass ≠ ⊤ :=
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top hheight
  intro htop
  rw [htop] at hbound
  exact hproduct (top_unique hbound)

end

end RiemannGaussian
