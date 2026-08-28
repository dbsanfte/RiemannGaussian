import RiemannGaussian.RiemannXiSuzukiSpectralStaticContourUniformVanishing

/-!
# Uniform recovery of the finite Blaschke detector from static boundary data

The paired horizontal boundary value is exactly the finite upper Blaschke
logarithmic derivative plus the fixed arithmetic safe-line trace, up to the
zero-height signed vertical remainder.  The preceding compact-uniform
vanishing theorem therefore gives a direct, uniform recovery statement for
the actual finite RH detector.

This is the precise static-contour interface needed by a subsequent rigidity
argument: on bounded safe observation heights, the only asymptotic error in
recovering the Blaschke detector from the inner-versus-outer horizontal
boundary comparison is explicitly controlled and tends to zero.  The theorem
does not assume, or assert, that the horizontal comparison itself vanishes.
-/

open Complex Filter MeasureTheory Metric Set Topology
open scoped Classical ComplexConjugate ENNReal Interval Topology

namespace RiemannGaussian

noncomputable section

/-- The error made when the paired horizontal boundary trace, after removing
the fixed outer safe-line trace, is used to recover the finite upper Blaschke
logarithmic derivative. -/
def xiSpectralBlaschkePairedBoundaryDetectorErrorWindow
    (T v : ℝ) : ℂ :=
  xiSpectralBlaschkePairedHorizontalBoundaryValueWindow T
      ((v : ℂ) * Complex.I) -
    xiSpectralBlaschkeOuterHorizontalPairWindow T
      ((v : ℂ) * Complex.I) +
    (((2 * Real.pi : ℝ) : ℂ)) *
      riemannXiUpperBlaschkeLogDerivativeWindow
        ((v : ℂ) * Complex.I) T

/-- The paired-boundary detector-recovery error is exactly the negative
zero-height signed vertical remainder. -/
theorem xiSpectralBlaschkePairedBoundaryDetectorErrorWindow_eq_neg_vertical
    (T v : ℝ) :
    xiSpectralBlaschkePairedBoundaryDetectorErrorWindow T v =
      -xiSpectralBlaschkeSignedVerticalRemainderWindow T 0
        ((v : ℂ) * Complex.I) := by
  unfold xiSpectralBlaschkePairedBoundaryDetectorErrorWindow
    xiSpectralBlaschkePairedHorizontalBoundaryValueWindow
  ring

/-- On the safe imaginary axis, every selected Blaschke summand has a
height-uniform inverse-square ordinate majorant.  The constant `4` follows
only from the critical-strip bound `|Im alpha| < 1/2` and `v > 1`. -/
theorem norm_zetaUpperBlaschkeSelectedLogDerivativeSummand_imaginary_le_inverseSquare
    {v : ℝ} (hv : 1 < v) (rho : NontrivialZetaZero) :
    ‖zetaUpperBlaschkeSelectedLogDerivativeSummand
        ((v : ℂ) * Complex.I) rho‖ ≤
      4 * ((analyticZetaZeroMultiplicity rho : ℝ) /
        (1 + (zetaSpectralCoordinate rho.1).re ^ 2)) := by
  by_cases hupper : 0 < (zetaSpectralCoordinate rho.1).im
  · let alpha : ℂ := zetaSpectralCoordinate rho.1
    let z : ℂ := (v : ℂ) * Complex.I
    let gamma : ℝ := alpha.re
    let h : ℝ := alpha.im
    let A : ℝ := ‖z - alpha‖
    let B : ℝ := ‖z - starRingEnd ℂ alpha‖
    let Q : ℝ := 1 + gamma ^ 2
    have habs := NontrivialZetaZero.abs_spectralCoordinate_im_lt_half rho
    have hhalf : h < 1 / 2 := by
      dsimp [h, alpha]
      exact (le_abs_self _).trans_lt habs
    have hh : 0 < h := by simpa [h, alpha] using hupper
    have hvh : 1 / 2 < v - h := by linarith
    have hvph : 1 / 2 < v + h := by linarith
    have hzalpha : z - alpha ≠ 0 := by
      intro heq
      have him : v - h = 0 := by
        simpa [z, h] using congrArg Complex.im heq
      linarith
    have hzconj : z - starRingEnd ℂ alpha ≠ 0 := by
      intro heq
      have him : v + h = 0 := by
        simpa [z, h] using congrArg Complex.im heq
      linarith
    have hpair :
        1 / (z - alpha) - 1 / (z - starRingEnd ℂ alpha) =
          (alpha - starRingEnd ℂ alpha) /
            ((z - alpha) * (z - starRingEnd ℂ alpha)) := by
      field_simp [hzalpha, hzconj]
      ring
    have hdiff : alpha - starRingEnd ℂ alpha =
        (2 * h : ℝ) * Complex.I := by
      apply Complex.ext
      · simp [h]
      · simp [h]
        ring
    have hdiffNorm : ‖alpha - starRingEnd ℂ alpha‖ = 2 * h := by
      rw [hdiff, norm_mul, Complex.norm_real, norm_I, mul_one,
        Real.norm_eq_abs, abs_of_pos (mul_pos (by norm_num) hh)]
    have hA : 0 < A := by
      dsimp [A]
      exact norm_pos_iff.mpr hzalpha
    have hB : 0 < B := by
      dsimp [B]
      exact norm_pos_iff.mpr hzconj
    have hQ : 0 < Q := by
      dsimp [Q]
      positivity
    have hASq : A ^ 2 = gamma ^ 2 + (v - h) ^ 2 := by
      dsimp [A, gamma, h, z]
      rw [← Complex.normSq_eq_norm_sq]
      simp [Complex.normSq_apply]
      ring
    have hBSq : B ^ 2 = gamma ^ 2 + (v + h) ^ 2 := by
      dsimp [B, gamma, h, z]
      rw [← Complex.normSq_eq_norm_sq]
      simp [Complex.normSq_apply]
      ring
    have hAQ : Q / 4 ≤ A ^ 2 := by
      rw [hASq]
      dsimp [Q]
      nlinarith [sq_nonneg gamma, sq_nonneg (v - h)]
    have hBQ : Q / 4 ≤ B ^ 2 := by
      rw [hBSq]
      dsimp [Q]
      nlinarith [sq_nonneg gamma, sq_nonneg (v + h)]
    have hAB : Q / 4 ≤ A * B := by
      apply (sq_le_sq₀ (by positivity) (mul_nonneg hA.le hB.le)).mp
      calc
        (Q / 4) ^ 2 = (Q / 4) * (Q / 4) := by ring
        _ ≤ A ^ 2 * B ^ 2 :=
          mul_le_mul hAQ hBQ (by positivity) (sq_nonneg A)
        _ = (A * B) ^ 2 := by ring
    have hfrac : (2 * h) / (A * B) ≤ 4 / Q := by
      calc
        (2 * h) / (A * B) ≤ 1 / (A * B) := by
          exact div_le_div_of_nonneg_right (by linarith) (by positivity)
        _ ≤ 1 / (Q / 4) :=
          one_div_le_one_div_of_le (by positivity) hAB
        _ = 4 / Q := by field_simp [hQ.ne']
    rw [zetaUpperBlaschkeSelectedLogDerivativeSummand, if_pos hupper,
      zetaUpperBlaschkeLogDerivativeSummand]
    change ‖(analyticZetaZeroMultiplicity rho : ℂ) *
        (1 / (z - alpha) - 1 / (z - starRingEnd ℂ alpha))‖ ≤ _
    rw [hpair, norm_mul, Complex.norm_natCast, norm_div, norm_mul,
      hdiffNorm]
    change (analyticZetaZeroMultiplicity rho : ℝ) *
        ((2 * h) / (A * B)) ≤
      4 * ((analyticZetaZeroMultiplicity rho : ℝ) / Q)
    calc
      (analyticZetaZeroMultiplicity rho : ℝ) *
          ((2 * h) / (A * B)) ≤
        (analyticZetaZeroMultiplicity rho : ℝ) * (4 / Q) :=
          mul_le_mul_of_nonneg_left hfrac (Nat.cast_nonneg _)
      _ = 4 * ((analyticZetaZeroMultiplicity rho : ℝ) / Q) := by ring
  · rw [zetaUpperBlaschkeSelectedLogDerivativeSummand, if_neg hupper,
      norm_zero]
    positivity

/-- The genuine finite Blaschke windows converge uniformly to the complete
absolutely convergent logarithmic derivative on every compact interval of
safe imaginary-axis observation heights. -/
theorem tendstoUniformlyOn_riemannXiUpperBlaschkeLogDerivativeWindow_imaginary_quantitative_complete
    {a b : ℝ} (ha : 1 < a) :
    TendstoUniformlyOn
      (fun n : ℕ ↦ fun v : ℝ ↦
        riemannXiUpperBlaschkeLogDerivativeWindow
          ((v : ℂ) * Complex.I)
          (quantitativeSpectralBoundaryTruncation n))
      (fun v : ℝ ↦ riemannXiUpperBlaschkeCompleteLogDerivative
        ((v : ℂ) * Complex.I)) atTop (Icc a b) := by
  let f : NontrivialZetaZero → ℝ → ℂ := fun rho v ↦
    zetaUpperBlaschkeSelectedLogDerivativeSummand
      ((v : ℂ) * Complex.I) rho
  let u : NontrivialZetaZero → ℝ := fun rho ↦
    4 * ((analyticZetaZeroMultiplicity rho : ℝ) /
      (1 + (zetaSpectralCoordinate rho.1).re ^ 2))
  have hu : Summable u := by
    simpa [u] using
      summable_distinct_zetaZeroInverseSquareSpectralRe.mul_left 4
  have hbound : ∀ rho v, v ∈ Icc a b → ‖f rho v‖ ≤ u rho := by
    intro rho v hv
    simpa [f, u] using
      norm_zetaUpperBlaschkeSelectedLogDerivativeSummand_imaginary_le_inverseSquare
        (ha.trans_le hv.1) rho
  have hfinite := tendstoUniformlyOn_tsum hu hbound
  have hindex : Tendsto
      (fun n : ℕ ↦ spectralZetaZeroWindow
        (quantitativeSpectralBoundaryTruncation n))
      atTop atTop :=
    tendsto_spectralZetaZeroWindow_atTop.comp
      tendsto_quantitativeSpectralBoundaryTruncation_atTop
  rw [Metric.tendstoUniformlyOn_iff] at hfinite ⊢
  intro epsilon hepsilon
  filter_upwards [hindex.eventually (hfinite epsilon hepsilon)] with n hn
  intro v hv
  have hnv := hn v hv
  simpa [f, riemannXiUpperBlaschkeCompleteLogDerivative,
    sum_zetaUpperBlaschkeSelectedLogDerivativeSummand_eq_window] using hnv

/-- The quantitative vertical-remainder estimate is therefore an explicit
uniform majorant for the actual detector-recovery error. -/
theorem norm_xiSpectralBlaschkePairedBoundaryDetectorErrorWindow_quantitative_le
    {v b : ℝ} (hv : 1 < v) (hvb : v ≤ b) (n : ℕ) :
    ‖xiSpectralBlaschkePairedBoundaryDetectorErrorWindow
        (quantitativeSpectralBoundaryTruncation n) v‖ ≤
      4 * b *
          ((1 / quantitativeSpectralBoundaryTruncation n ^ 2) *
            (∫ y : ℝ in (0 : ℝ)..1,
              ‖xiSpectralNegativeLogDerivative
                ((quantitativeSpectralBoundaryTruncation n : ℂ) +
                  (y : ℂ) * Complex.I)‖)) +
        |(4 / quantitativeSpectralBoundaryTruncation n) *
          (∫ y : ℝ in (0 : ℝ)..1,
            (xiSpectralNegativeLogDerivative
              ((quantitativeSpectralBoundaryTruncation n : ℂ) +
                (y : ℂ) * Complex.I)).re)| := by
  rw [xiSpectralBlaschkePairedBoundaryDetectorErrorWindow_eq_neg_vertical,
    norm_neg]
  have hbound :=
    norm_neg_I_mul_xiSpectralBlaschkeSignedVerticalRemainderWindow_zero_imaginary_quantitative_le
      hv hvb n
  simpa only [norm_mul, norm_neg, norm_I, one_mul] using hbound

/-- On every compact safe-height interval, the paired-boundary
detector-recovery error tends uniformly to zero. -/
theorem tendstoUniformlyOn_xiSpectralBlaschkePairedBoundaryDetectorErrorWindow_quantitative_zero
    {a b : ℝ} (ha : 1 < a) :
    TendstoUniformlyOn
      (fun n : ℕ ↦ fun v : ℝ ↦
        xiSpectralBlaschkePairedBoundaryDetectorErrorWindow
          (quantitativeSpectralBoundaryTruncation n) v)
      (fun _ : ℝ ↦ (0 : ℂ)) atTop (Icc a b) := by
  have hvertical :=
    tendstoUniformlyOn_xiSpectralBlaschkeSignedVerticalRemainderWindow_zero_imaginary_quantitative_zero
      (b := b) ha
  rw [Metric.tendstoUniformlyOn_iff] at hvertical ⊢
  intro epsilon hepsilon
  filter_upwards [hvertical epsilon hepsilon] with n hn
  intro v hv
  simpa [dist_eq,
    xiSpectralBlaschkePairedBoundaryDetectorErrorWindow_eq_neg_vertical]
    using hn v hv

/-- Direct uniform recovery form: on a compact safe-height interval, the
paired horizontal boundary trace minus the outer arithmetic trace approaches
`-2π` times the finite Blaschke logarithmic derivative, uniformly in the
observation height. -/
theorem eventually_uniform_dist_xiSpectralBlaschkePairedBoundary_sub_outer_to_detector
    {a b : ℝ} (ha : 1 < a) (epsilon : ℝ) (hepsilon : 0 < epsilon) :
    ∀ᶠ n : ℕ in atTop, ∀ v ∈ Icc a b,
      dist
        (xiSpectralBlaschkePairedHorizontalBoundaryValueWindow
            (quantitativeSpectralBoundaryTruncation n)
            ((v : ℂ) * Complex.I) -
          xiSpectralBlaschkeOuterHorizontalPairWindow
            (quantitativeSpectralBoundaryTruncation n)
            ((v : ℂ) * Complex.I))
        (-(((2 * Real.pi : ℝ) : ℂ)) *
          riemannXiUpperBlaschkeLogDerivativeWindow
            ((v : ℂ) * Complex.I)
            (quantitativeSpectralBoundaryTruncation n)) < epsilon := by
  have huniform :=
    tendstoUniformlyOn_xiSpectralBlaschkePairedBoundaryDetectorErrorWindow_quantitative_zero
      (b := b) ha
  rw [Metric.tendstoUniformlyOn_iff] at huniform
  filter_upwards [huniform epsilon hepsilon] with n hn
  intro v hv
  have herror := hn v hv
  rw [dist_zero_left] at herror
  rw [dist_eq]
  simpa [xiSpectralBlaschkePairedBoundaryDetectorErrorWindow] using herror

/-- The complete static boundary-recovery theorem.  Along the quantitative
zero-free cutoffs, the paired horizontal boundary trace minus the arithmetic
outer trace converges locally uniformly to `-2π` times the complete upper
Blaschke logarithmic derivative. -/
theorem tendstoUniformlyOn_xiSpectralBlaschkePairedBoundary_sub_outer_quantitative_completeDetector
    {a b : ℝ} (ha : 1 < a) :
    TendstoUniformlyOn
      (fun n : ℕ ↦ fun v : ℝ ↦
        xiSpectralBlaschkePairedHorizontalBoundaryValueWindow
            (quantitativeSpectralBoundaryTruncation n)
            ((v : ℂ) * Complex.I) -
          xiSpectralBlaschkeOuterHorizontalPairWindow
            (quantitativeSpectralBoundaryTruncation n)
            ((v : ℂ) * Complex.I))
      (fun v : ℝ ↦
        -(((2 * Real.pi : ℝ) : ℂ)) *
          riemannXiUpperBlaschkeCompleteLogDerivative
            ((v : ℂ) * Complex.I))
      atTop (Icc a b) := by
  let c : ℂ := ((2 * Real.pi : ℝ) : ℂ)
  have herror :=
    tendstoUniformlyOn_xiSpectralBlaschkePairedBoundaryDetectorErrorWindow_quantitative_zero
      (b := b) ha
  have hdetector :=
    tendstoUniformlyOn_riemannXiUpperBlaschkeLogDerivativeWindow_imaginary_quantitative_complete
      (b := b) ha
  have hscaled :=
    (uniformContinuous_const_smul c).comp_tendstoUniformlyOn hdetector
  have hcombined : TendstoUniformlyOn
      (fun n : ℕ ↦ fun v : ℝ ↦
        xiSpectralBlaschkePairedBoundaryDetectorErrorWindow
            (quantitativeSpectralBoundaryTruncation n) v -
          c * riemannXiUpperBlaschkeLogDerivativeWindow
            ((v : ℂ) * Complex.I)
            (quantitativeSpectralBoundaryTruncation n))
      (fun v : ℝ ↦
        -c * riemannXiUpperBlaschkeCompleteLogDerivative
          ((v : ℂ) * Complex.I))
      atTop (Icc a b) := by
    have hraw := herror.sub hscaled
    change TendstoUniformlyOn
      (fun n : ℕ ↦ fun v : ℝ ↦
        xiSpectralBlaschkePairedBoundaryDetectorErrorWindow
            (quantitativeSpectralBoundaryTruncation n) v -
          c * riemannXiUpperBlaschkeLogDerivativeWindow
            ((v : ℂ) * Complex.I)
            (quantitativeSpectralBoundaryTruncation n))
      (fun v : ℝ ↦
        (0 : ℂ) - c * riemannXiUpperBlaschkeCompleteLogDerivative
          ((v : ℂ) * Complex.I))
      atTop (Icc a b) at hraw
    convert hraw using 1
    funext v
    ring
  refine hcombined.congr (Eventually.of_forall fun n ↦ ?_)
  intro v _hv
  unfold xiSpectralBlaschkePairedBoundaryDetectorErrorWindow
  dsimp [c]
  ring

end

end RiemannGaussian
