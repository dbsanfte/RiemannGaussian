import RiemannGaussian.RiemannXiSuzukiSpectralStaticContourSafeAxisBoundaryAction

/-!
# Sublinear large-height escape of the complete safe-axis defect

Compact safe-axis integration identifies the complete Blaschke action on
`[a,b]` with the defect drop `M(ia) - M(ib)`.  This module begins the genuine
large-height analysis of the endpoint `M(iy)`.

After division by the observation height, every one-zero logarithmic defect
is dominated by a fixed summable inverse-square ordinate majorant.  Tannery's
theorem therefore proves the unconditional sublinear law `M(iy) / y → 0`.
Consequently the complete compact-height detector action has vanishing mean
as its upper endpoint tends to infinity.  This does not assert the still-hard
unscaled decay `M(iy) → 0` and uses no interchange of cutoff and height
limits.
-/

open Complex Filter MeasureTheory Metric Set Topology
open scoped Classical ComplexConjugate ENNReal Interval Topology

namespace RiemannGaussian

noncomputable section

/-- One upper spectral zero's logarithmic defect on the imaginary safe axis,
normalized by the observation height. -/
def zetaUpperSafeAxisNormalizedLogDefectSummand
    (y : ℝ) (rho : NontrivialZetaZero) : ℝ :=
  zetaUpperHyperbolicLogDefectSummand ((y : ℂ) * Complex.I) rho / y

/-- A height-independent summable inverse-square majorant for the normalized
safe-axis defect summands. -/
def zetaUpperSafeAxisNormalizedLogDefectMajorant
    (rho : NontrivialZetaZero) : ℝ :=
  8 * ((analyticZetaZeroMultiplicity rho : ℝ) /
    (1 + (zetaSpectralCoordinate rho.1).re ^ 2))

/-- The normalized safe-axis defect majorant is summable over the genuine
spectral divisor. -/
theorem summable_zetaUpperSafeAxisNormalizedLogDefectMajorant :
    Summable zetaUpperSafeAxisNormalizedLogDefectMajorant := by
  change Summable fun rho : NontrivialZetaZero ↦
    8 * ((analyticZetaZeroMultiplicity rho : ℝ) /
      (1 + (zetaSpectralCoordinate rho.1).re ^ 2))
  exact summable_distinct_zetaZeroInverseSquareSpectralRe.mul_left 8

/-- At every height at least `1`, each normalized logarithmic defect is
bounded by the fixed inverse-square ordinate majorant. -/
theorem norm_zetaUpperSafeAxisNormalizedLogDefectSummand_le_majorant
    {y : ℝ} (hy : 1 ≤ y) (rho : NontrivialZetaZero) :
    ‖zetaUpperSafeAxisNormalizedLogDefectSummand y rho‖ ≤
      zetaUpperSafeAxisNormalizedLogDefectMajorant rho := by
  by_cases hupper : 0 < (zetaSpectralCoordinate rho.1).im
  · let alpha : ℂ := zetaSpectralCoordinate rho.1
    let z : ℂ := (y : ℂ) * Complex.I
    let D : ℝ := Complex.normSq (z - alpha)
    let Q : ℝ := 1 + alpha.re ^ 2
    have hyPos : 0 < y := by linarith
    have habs := NontrivialZetaZero.abs_spectralCoordinate_im_lt_half rho
    have hhalf : alpha.im < 1 / 2 := by
      dsimp [alpha]
      exact (le_abs_self _).trans_lt habs
    have hheightNonneg : 0 ≤ alpha.im := hupper.le
    have hheightLe : alpha.im ≤ 1 / 2 := hhalf.le
    have hySub : 1 / 2 < y - alpha.im := by linarith
    have hne : z ≠ alpha := by
      intro heq
      have him := congrArg Complex.im heq
      dsimp [z] at him
      simp only [mul_im, ofReal_re, I_im, ofReal_im, I_re, mul_one,
        zero_mul, add_zero] at him
      linarith
    have hDPos : 0 < D := by
      dsimp [D]
      exact Complex.normSq_pos.mpr (sub_ne_zero.mpr hne)
    have hQPos : 0 < Q := by
      dsimp [Q]
      positivity
    have hDEq : D = alpha.re ^ 2 + (y - alpha.im) ^ 2 := by
      dsimp [D, z]
      unfold Complex.normSq
      simp
      ring
    have hDLower : Q / 4 ≤ D := by
      rw [hDEq]
      dsimp [Q]
      nlinarith [sq_nonneg alpha.re, sq_nonneg (y - alpha.im)]
    have hfrac :
        (4 * y * alpha.im / D) / y ≤ 8 / Q := by
      have hcancel : (4 * y * alpha.im / D) / y =
          4 * alpha.im / D := by
        field_simp [hyPos.ne', hDPos.ne']
      rw [hcancel]
      calc
        4 * alpha.im / D ≤ 2 / D := by
          exact div_le_div_of_nonneg_right (by linarith) hDPos.le
        _ ≤ 2 / (Q / 4) := by
          exact div_le_div_of_nonneg_left (by norm_num) (by positivity)
            hDLower
        _ = 8 / Q := by
          field_simp [hQPos.ne']
          norm_num
    have hz : 0 < z.im := by simpa [z] using hyPos
    have hdefectNonneg :
        0 ≤ zetaUpperHyperbolicLogDefectSummand z rho :=
      zetaUpperHyperbolicLogDefectSummand_nonneg hz rho hne
    have hraw :=
      neg_two_log_upperHalfPlanePseudoHyperbolicDistance_le_height_div_normSq
        hz hupper hne
    have hraw' :
        -2 * Real.log (upperHalfPlanePseudoHyperbolicDistance z alpha) ≤
          4 * y * alpha.im / D := by
      simpa [z, alpha, D] using hraw
    rw [zetaUpperSafeAxisNormalizedLogDefectSummand,
      Real.norm_eq_abs, abs_of_nonneg (div_nonneg hdefectNonneg hyPos.le),
      zetaUpperSafeAxisNormalizedLogDefectMajorant,
      zetaUpperHyperbolicLogDefectSummand, if_pos hupper]
    change
      ((analyticZetaZeroMultiplicity rho : ℝ) *
          (-2 * Real.log
            (upperHalfPlanePseudoHyperbolicDistance z alpha))) / y ≤
        8 * ((analyticZetaZeroMultiplicity rho : ℝ) / Q)
    calc
      ((analyticZetaZeroMultiplicity rho : ℝ) *
          (-2 * Real.log
            (upperHalfPlanePseudoHyperbolicDistance z alpha))) / y ≤
          ((analyticZetaZeroMultiplicity rho : ℝ) *
            (4 * y * alpha.im / D)) / y := by
        exact div_le_div_of_nonneg_right
          (mul_le_mul_of_nonneg_left hraw' (Nat.cast_nonneg _)) hyPos.le
      _ = (analyticZetaZeroMultiplicity rho : ℝ) *
          ((4 * y * alpha.im / D) / y) := by ring
      _ ≤ (analyticZetaZeroMultiplicity rho : ℝ) * (8 / Q) :=
        mul_le_mul_of_nonneg_left hfrac (Nat.cast_nonneg _)
      _ = 8 * ((analyticZetaZeroMultiplicity rho : ℝ) / Q) := by ring
  · rw [zetaUpperSafeAxisNormalizedLogDefectSummand,
      zetaUpperHyperbolicLogDefectSummand, if_neg hupper, zero_div,
      norm_zero]
    unfold zetaUpperSafeAxisNormalizedLogDefectMajorant
    positivity

/-- For each fixed spectral zero, its height-normalized safe-axis logarithmic
defect tends to zero at infinite observation height. -/
theorem tendsto_zetaUpperSafeAxisNormalizedLogDefectSummand_atTop_zero
    (rho : NontrivialZetaZero) :
    Tendsto (fun y : ℝ ↦
      zetaUpperSafeAxisNormalizedLogDefectSummand y rho)
      atTop (nhds 0) := by
  by_cases hupper : 0 < (zetaSpectralCoordinate rho.1).im
  · have hvertical : Tendsto
        (fun y : ℝ ↦ zetaUpperVerticalLogDefectSummand 0 y rho)
        atTop (nhds 0) := by
      unfold zetaUpperVerticalLogDefectSummand
      simpa using
        (tendsto_upperHalfPlaneVerticalLogDefect_safeAxis_atTop_zero
          (zetaSpectralCoordinate rho.1)).const_mul
            (analyticZetaZeroMultiplicity rho : ℝ)
    have hhyperbolic : Tendsto
        (fun y : ℝ ↦ zetaUpperHyperbolicLogDefectSummand
          ((y : ℂ) * Complex.I) rho) atTop (nhds 0) := by
      apply hvertical.congr'
      filter_upwards [eventually_ge_atTop (1 : ℝ)] with y hy
      simpa [upperBoundaryApproachPoint, mul_comm] using
        zetaUpperVerticalLogDefectSummand_eq_hyperbolic
          (x := 0) (y := y) rho (by linarith) hupper
            (by
              simpa [upperBoundaryApproachPoint, mul_comm] using
                imaginarySafeAxis_ne_zetaSpectralCoordinate hy rho)
    simpa [zetaUpperSafeAxisNormalizedLogDefectSummand] using
      hhyperbolic.div_atTop (tendsto_id :
        Tendsto (fun y : ℝ ↦ y) atTop atTop)
  · have hzero : ∀ y : ℝ,
        zetaUpperSafeAxisNormalizedLogDefectSummand y rho = 0 := by
      intro y
      unfold zetaUpperSafeAxisNormalizedLogDefectSummand
        zetaUpperHyperbolicLogDefectSummand
      rw [if_neg hupper, zero_div]
    simpa only [hzero] using
      (tendsto_const_nhds : Tendsto (fun _ : ℝ ↦ (0 : ℝ)) atTop (nhds 0))

/-- Tannery's theorem passes the large-height normalized limit through the
complete genuine upper spectral divisor. -/
theorem tendsto_tsum_zetaUpperSafeAxisNormalizedLogDefectSummand_atTop_zero :
    Tendsto
      (fun y : ℝ ↦ ∑' rho : NontrivialZetaZero,
        zetaUpperSafeAxisNormalizedLogDefectSummand y rho)
      atTop (nhds 0) := by
  have hlimit := tendsto_tsum_of_dominated_convergence
    summable_zetaUpperSafeAxisNormalizedLogDefectMajorant
    tendsto_zetaUpperSafeAxisNormalizedLogDefectSummand_atTop_zero
    (by
      filter_upwards [eventually_ge_atTop (1 : ℝ)] with y hy
      intro rho
      exact norm_zetaUpperSafeAxisNormalizedLogDefectSummand_le_majorant
        hy rho)
  simpa using hlimit

/-- Unconditional sublinear large-height law for the complete safe-axis
logarithmic defect: `M(iy) / y → 0`. -/
theorem
    tendsto_riemannXiUpperHyperbolicLogDefectMass_imaginary_toReal_div_atTop_zero
    :
    Tendsto
      (fun y : ℝ ↦
        (riemannXiUpperHyperbolicLogDefectMass
          ((y : ℂ) * Complex.I)).toReal / y)
      atTop (nhds 0) := by
  have hsum :=
    tendsto_tsum_zetaUpperSafeAxisNormalizedLogDefectSummand_atTop_zero
  apply hsum.congr'
  filter_upwards [eventually_ge_atTop (1 : ℝ)] with y hy
  have hz : 0 < (((y : ℂ) * Complex.I)).im := by
    simpa using (show 0 < y by linarith)
  have hxi : riemannXiSpectral ((y : ℂ) * Complex.I) ≠ 0 :=
    riemannXiSpectral_ne_zero_imaginarySafeAxis hy
  have hnonneg : 0 ≤ ∑' rho : NontrivialZetaZero,
      zetaUpperHyperbolicLogDefectSummand
        ((y : ℂ) * Complex.I) rho := by
    apply tsum_nonneg
    intro rho
    exact zetaUpperHyperbolicLogDefectSummand_nonneg hz rho
      (imaginarySafeAxis_ne_zetaSpectralCoordinate hy rho)
  unfold zetaUpperSafeAxisNormalizedLogDefectSummand
  rw [tsum_div_const,
    riemannXiUpperHyperbolicLogDefectMass_eq_ofReal_tsum hz hxi,
    ENNReal.toReal_ofReal hnonneg]

/-- The complete safe-axis Blaschke detector action has vanishing mean over
`[a,b]` as the upper endpoint tends to infinity. -/
theorem
    tendsto_intervalIntegral_neg_two_mul_re_neg_I_completeBlaschkeLogDerivative_imaginary_div_atTop_zero
    {a : ℝ} (ha : 1 < a) :
    Tendsto
      (fun b : ℝ ↦
        (∫ y : ℝ in a..b, -2 *
          (-Complex.I * riemannXiUpperBlaschkeCompleteLogDerivative
            ((y : ℂ) * Complex.I)).re) / b)
      atTop (nhds 0) := by
  have hconstant : Tendsto
      (fun b : ℝ ↦
        (riemannXiUpperHyperbolicLogDefectMass
          ((a : ℂ) * Complex.I)).toReal / b)
      atTop (nhds 0) :=
    tendsto_const_nhds.div_atTop tendsto_id
  have hendpoint :=
    tendsto_riemannXiUpperHyperbolicLogDefectMass_imaginary_toReal_div_atTop_zero
  have hdifference : Tendsto
      (fun b : ℝ ↦
        ((riemannXiUpperHyperbolicLogDefectMass
            ((a : ℂ) * Complex.I)).toReal -
          (riemannXiUpperHyperbolicLogDefectMass
            ((b : ℂ) * Complex.I)).toReal) / b)
      atTop (nhds 0) := by
    simpa [sub_div] using hconstant.sub hendpoint
  apply hdifference.congr'
  filter_upwards [eventually_ge_atTop a] with b hab
  rw [
    intervalIntegral_neg_two_mul_re_neg_I_completeBlaschkeLogDerivative_imaginary_eq_completeDefectDrop
      ha hab]

/-- Ordered large-height arithmetic bridge.  At each fixed upper height, the
actual paired static-boundary action divided by that height converges along
the quantitative contour cutoffs to the corresponding complete Blaschke
mean action.  Only after taking that cutoff limit does the complete mean
action tend to zero with the upper height. -/
theorem staticBoundarySafeAxisAction_iteratedMeanVanishes
    {a : ℝ} (ha : 1 < a) :
    (∀ b : ℝ, a ≤ b →
      Tendsto
        (fun n : ℕ ↦
          (∫ y : ℝ in a..b,
            xiSpectralBlaschkePairedBoundarySafeAxisResponseWindow
              (quantitativeSpectralBoundaryTruncation n) y) / b)
        atTop
        (nhds ((∫ y : ℝ in a..b, -2 *
          (-Complex.I * riemannXiUpperBlaschkeCompleteLogDerivative
            ((y : ℂ) * Complex.I)).re) / b))) ∧
      Tendsto
        (fun b : ℝ ↦
          (∫ y : ℝ in a..b, -2 *
            (-Complex.I * riemannXiUpperBlaschkeCompleteLogDerivative
              ((y : ℂ) * Complex.I)).re) / b)
        atTop (nhds 0) := by
  constructor
  · intro b hab
    exact
      (staticBoundarySafeAxisAction_tendsto_completeDetector_and_eq_completeDefectDrop
        ha hab).1.div_const b
  · exact
      tendsto_intervalIntegral_neg_two_mul_re_neg_I_completeBlaschkeLogDerivative_imaginary_div_atTop_zero
        ha

end

end RiemannGaussian
