import RiemannGaussian.RiemannXiSuzukiSpectralStaticContourSafeAxisTransport

/-!
# Integrated static-boundary action on the safe axis

The static paired-boundary comparison recovers the Blaschke detector locally
uniformly, while safe-axis transport integrates each finite detector window
to a positive logarithmic defect.  This module connects those statements at
the level of interval integrals.

The paired horizontal comparison is normalized by the real functional
`z ↦ π⁻¹ Re(-i z)`.  On every compact height segment strictly above the
safe contour, its finite action is exactly the drop in vertical log defect
plus the integrated vertical-remainder error.  The error vanishes with the
quantitative spectral cutoff, so the boundary action converges to the drop
in the finite complete RH-equivalent defect between the two endpoint
heights.  No infinite-height limit or exchange of limits is used.
-/

open Complex Filter MeasureTheory Metric Set Topology
open scoped Classical ComplexConjugate ENNReal Interval Topology

namespace RiemannGaussian

noncomputable section

/-- The normalized real safe-axis response of the paired horizontal boundary
comparison after subtracting its arithmetic outer trace. -/
def xiSpectralBlaschkePairedBoundarySafeAxisResponseWindow
    (T v : ℝ) : ℝ :=
  (1 / Real.pi) *
    (-Complex.I *
      (xiSpectralBlaschkePairedHorizontalBoundaryValueWindow T
          ((v : ℂ) * Complex.I) -
        xiSpectralBlaschkeOuterHorizontalPairWindow T
          ((v : ℂ) * Complex.I))).re

/-- The normalized real safe-axis response of the finite detector-recovery
error. -/
def xiSpectralBlaschkePairedBoundaryErrorSafeAxisResponseWindow
    (T v : ℝ) : ℝ :=
  (1 / Real.pi) *
    (-Complex.I *
      xiSpectralBlaschkePairedBoundaryDetectorErrorWindow T v).re

/-- Pointwise, the normalized paired-boundary response is the finite
Blaschke transport response plus its explicitly retained recovery error. -/
theorem xiSpectralBlaschkePairedBoundarySafeAxisResponseWindow_eq
    (T v : ℝ) :
    xiSpectralBlaschkePairedBoundarySafeAxisResponseWindow T v =
      -2 * (-Complex.I * riemannXiUpperBlaschkeLogDerivativeWindow
        ((v : ℂ) * Complex.I) T).re +
      xiSpectralBlaschkePairedBoundaryErrorSafeAxisResponseWindow T v := by
  let C : ℂ :=
    xiSpectralBlaschkePairedHorizontalBoundaryValueWindow T
        ((v : ℂ) * Complex.I) -
      xiSpectralBlaschkeOuterHorizontalPairWindow T
        ((v : ℂ) * Complex.I)
  let B : ℂ := riemannXiUpperBlaschkeLogDerivativeWindow
    ((v : ℂ) * Complex.I) T
  let E : ℂ := xiSpectralBlaschkePairedBoundaryDetectorErrorWindow T v
  have hE : E = C + (((2 * Real.pi : ℝ) : ℂ)) * B := by
    rfl
  have hC : C = E - (((2 * Real.pi : ℝ) : ℂ)) * B := by
    rw [hE]
    ring
  have hscale :
      (-Complex.I * ((((2 * Real.pi : ℝ) : ℂ)) * B)).re =
        (2 * Real.pi) * (-Complex.I * B).re := by
    calc
      (-Complex.I * ((((2 * Real.pi : ℝ) : ℂ)) * B)).re =
          ((((2 * Real.pi : ℝ) : ℂ)) *
            (-Complex.I * B)).re := by
        congr 1
        ring
      _ = (2 * Real.pi) * (-Complex.I * B).re := by simp
  unfold xiSpectralBlaschkePairedBoundarySafeAxisResponseWindow
    xiSpectralBlaschkePairedBoundaryErrorSafeAxisResponseWindow
  change (1 / Real.pi) * (-Complex.I * C).re =
    -2 * (-Complex.I * B).re + (1 / Real.pi) * (-Complex.I * E).re
  rw [hC, mul_sub, sub_re, hscale]
  field_simp [Real.pi_ne_zero]
  ring

/-- On any finite safe-axis segment, integrating the negative finite
Blaschke response gives the exact drop in the finite vertical log defect. -/
theorem
    intervalIntegral_neg_two_mul_re_neg_I_blaschkeLogDerivativeWindow_safeAxis_segment
    {a b : ℝ} (ha : 1 ≤ a) (hab : a ≤ b) (T : ℝ) :
    (∫ y : ℝ in a..b, -2 *
      (-Complex.I * riemannXiUpperBlaschkeLogDerivativeWindow
        (upperBoundaryApproachPoint 0 y) T).re) =
      riemannXiUpperVerticalLogDefectWindow 0 a T -
        riemannXiUpperVerticalLogDefectWindow 0 b T := by
  let g : ℝ → ℝ := fun y ↦ 2 *
    (-Complex.I * riemannXiUpperBlaschkeLogDerivativeWindow
      (upperBoundaryApproachPoint 0 y) T).re
  have hderiv : ∀ y ∈ uIcc a b,
      HasDerivAt
        (fun v : ℝ ↦ riemannXiUpperVerticalLogDefectWindow 0 v T)
        (g y) y := by
    intro y hy
    rw [uIcc_of_le hab] at hy
    exact hasDerivAt_riemannXiUpperVerticalLogDefectWindow_safeAxis
      (ha.trans hy.1) T
  have hcontinuous : ContinuousOn g (uIcc a b) := by
    intro y hy
    rw [uIcc_of_le hab] at hy
    exact
      (continuousAt_two_mul_re_neg_I_blaschkeLogDerivativeWindow_safeAxis
        (ha.trans hy.1) T).continuousWithinAt
  have hbase := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv
    hcontinuous.intervalIntegrable
  calc
    (∫ y : ℝ in a..b, -2 *
        (-Complex.I * riemannXiUpperBlaschkeLogDerivativeWindow
          (upperBoundaryApproachPoint 0 y) T).re) =
        -(∫ y : ℝ in a..b, g y) := by
      rw [← intervalIntegral.integral_neg]
      apply intervalIntegral.integral_congr
      intro y _hy
      dsimp [g]
      ring
    _ = _ := by rw [hbase]; ring

/-- A purely imaginary observation point of height at least `1` cannot
collide with a genuine spectral zeta zero. -/
theorem imaginarySafeAxis_ne_zetaSpectralCoordinate
    {v : ℝ} (hv : 1 ≤ v) (rho : NontrivialZetaZero) :
    ((v : ℂ) * Complex.I) ≠ zetaSpectralCoordinate rho.1 := by
  intro heq
  have habs := NontrivialZetaZero.abs_spectralCoordinate_im_lt_half rho
  rw [← heq] at habs
  simp only [mul_im, ofReal_re, I_im, ofReal_im, I_re, mul_one,
    zero_mul, add_zero] at habs
  rw [abs_of_nonneg (by linarith)] at habs
  linarith

/-- At every safe imaginary height, a finite vertical defect is the existing
real pseudo-hyperbolic log-defect window at that observation point. -/
theorem
    riemannXiUpperVerticalLogDefectWindow_zero_eq_hyperbolicRealWindow_imaginarySafeAxis
    {v : ℝ} (hv : 1 ≤ v) (T : ℝ) :
    riemannXiUpperVerticalLogDefectWindow 0 v T =
      riemannXiUpperHyperbolicLogDefectRealWindow
        ((v : ℂ) * Complex.I) T := by
  have hbase :=
    riemannXiUpperVerticalLogDefectWindow_eq_hyperbolicRealWindow
      (x := 0) (y := v) (T := T) (by linarith)
      (fun rho _hrho ↦ by
        simpa [upperBoundaryApproachPoint, mul_comm] using
          imaginarySafeAxis_ne_zetaSpectralCoordinate hv rho)
  simpa [upperBoundaryApproachPoint, mul_comm] using hbase

/-- Every finite vertical defect at safe imaginary height is nonnegative. -/
theorem riemannXiUpperVerticalLogDefectWindow_zero_nonneg_imaginarySafeAxis
    {v : ℝ} (hv : 1 ≤ v) (T : ℝ) :
    0 ≤ riemannXiUpperVerticalLogDefectWindow 0 v T := by
  rw [
    riemannXiUpperVerticalLogDefectWindow_zero_eq_hyperbolicRealWindow_imaginarySafeAxis
      hv]
  unfold riemannXiUpperHyperbolicLogDefectRealWindow
  apply Finset.sum_nonneg
  intro rho _hrho
  exact zetaUpperHyperbolicLogDefectSummand_nonneg
    (by simpa using (show 0 < v by linarith)) rho
    (imaginarySafeAxis_ne_zetaSpectralCoordinate hv rho)

/-- Taking `ofReal` of a finite safe-axis vertical defect gives exactly its
extended-nonnegative hyperbolic log-defect window. -/
theorem ofReal_riemannXiUpperVerticalLogDefectWindow_zero_eq_imaginarySafeAxis
    {v : ℝ} (hv : 1 ≤ v) (T : ℝ) :
    ENNReal.ofReal (riemannXiUpperVerticalLogDefectWindow 0 v T) =
      riemannXiUpperHyperbolicLogDefectWindow
        ((v : ℂ) * Complex.I) T := by
  rw [
    riemannXiUpperVerticalLogDefectWindow_zero_eq_hyperbolicRealWindow_imaginarySafeAxis
      hv]
  exact ofReal_riemannXiUpperHyperbolicLogDefectRealWindow_eq
    (by simpa using (show 0 < v by linarith))
    (fun rho _hrho ↦ imaginarySafeAxis_ne_zetaSpectralCoordinate hv rho)

/-- Spectral xi is nonzero at every purely imaginary safe-axis point of
height at least `1`. -/
theorem riemannXiSpectral_ne_zero_imaginarySafeAxis
    {v : ℝ} (hv : 1 ≤ v) :
    riemannXiSpectral ((v : ℂ) * Complex.I) ≠ 0 := by
  apply riemannXiSpectral_ne_zero_of_half_le_abs_im
  simp only [mul_im, ofReal_re, I_im, ofReal_im, I_re, mul_one,
    zero_mul, add_zero]
  rw [abs_of_nonneg (by linarith)]
  linarith

/-- The complete hyperbolic log-defect mass is finite at every safe-axis
height at least `1`. -/
theorem riemannXiUpperHyperbolicLogDefectMass_ne_top_imaginarySafeAxis
    {v : ℝ} (hv : 1 ≤ v) :
    riemannXiUpperHyperbolicLogDefectMass
      ((v : ℂ) * Complex.I) ≠ ∞ := by
  exact riemannXiUpperHyperbolicLogDefectMass_ne_top
    (by simpa using (show 0 < v by linarith))
    (riemannXiSpectral_ne_zero_imaginarySafeAxis hv)

/-- Along the quantitative cutoffs, finite real vertical defects at any
fixed safe height converge to the real value of the complete defect mass. -/
theorem
    tendsto_riemannXiUpperVerticalLogDefectWindow_zero_quantitative_complete_toReal_imaginarySafeAxis
    {v : ℝ} (hv : 1 ≤ v) :
    Tendsto
      (fun n : ℕ ↦ riemannXiUpperVerticalLogDefectWindow 0 v
        (quantitativeSpectralBoundaryTruncation n))
      atTop
      (nhds (riemannXiUpperHyperbolicLogDefectMass
        ((v : ℂ) * Complex.I)).toReal) := by
  have hwindow :=
    (tendsto_riemannXiUpperHyperbolicLogDefectWindow
      ((v : ℂ) * Complex.I)).comp
        tendsto_quantitativeSpectralBoundaryTruncation_atTop
  have hofReal : Tendsto
      (fun n : ℕ ↦ ENNReal.ofReal
        (riemannXiUpperVerticalLogDefectWindow 0 v
          (quantitativeSpectralBoundaryTruncation n)))
      atTop
      (nhds (riemannXiUpperHyperbolicLogDefectMass
        ((v : ℂ) * Complex.I))) := by
    apply hwindow.congr'
    exact Eventually.of_forall fun n ↦
      (ofReal_riemannXiUpperVerticalLogDefectWindow_zero_eq_imaginarySafeAxis
        hv (quantitativeSpectralBoundaryTruncation n)).symm
  have htoReal :=
    (ENNReal.tendsto_toReal
      (riemannXiUpperHyperbolicLogDefectMass_ne_top_imaginarySafeAxis hv)).comp
        hofReal
  apply htoReal.congr'
  exact Eventually.of_forall fun n ↦
    ENNReal.toReal_ofReal
      (riemannXiUpperVerticalLogDefectWindow_zero_nonneg_imaginarySafeAxis
        hv (quantitativeSpectralBoundaryTruncation n))

/-- The folded right-line kernel is jointly continuous in safe-axis
observation height and vertical contour height at every quantitative cutoff. -/
theorem continuous_uncurry_xiSpectralBlaschkeRightFoldedVerticalKernel_quantitative
    (n : ℕ) :
    Continuous
      (Function.uncurry (fun v y : ℝ ↦
        xiSpectralBlaschkeRightFoldedVerticalKernel
          (quantitativeSpectralBoundaryTruncation n)
          ((v : ℂ) * Complex.I) y)) := by
  let T : ℝ := quantitativeSpectralBoundaryTruncation n
  let z : ℝ → ℂ := fun v ↦ (v : ℂ) * Complex.I
  let w : ℝ → ℂ := fun y ↦ (T : ℂ) + (y : ℂ) * Complex.I
  have hT : 0 < T := by
    dsimp [T]
    exact (Nat.cast_nonneg n).trans_lt
      (quantitativeSpectralBoundaryTruncation_spec n).1
  have hz : Continuous z := by
    dsimp [z]
    fun_prop
  have hw : Continuous w := by
    dsimp [w]
    fun_prop
  have hlog : Continuous
      (fun y : ℝ ↦ xiSpectralNegativeLogDerivative (w y)) := by
    apply continuous_comp_of_forall_analyticAt
      xiSpectralNegativeLogDerivative w hw
    intro y
    apply analyticAt_xiSpectralNegativeLogDerivative_of_ne
    simpa [riemannXiSpectral, w, T] using
      riemannXi_quantitativeCompletedCoordinate_ne_zero n y
  have hzp : Continuous (fun p : ℝ × ℝ ↦ z p.1) :=
    hz.comp continuous_fst
  have hwp : Continuous (fun p : ℝ × ℝ ↦ w p.2) :=
    hw.comp continuous_snd
  have hlogp : Continuous (fun p : ℝ × ℝ ↦
      xiSpectralNegativeLogDerivative (w p.2)) :=
    hlog.comp continuous_snd
  have hminus : ∀ p : ℝ × ℝ, z p.1 - w p.2 ≠ 0 := by
    intro p heq
    have hre := congrArg Complex.re heq
    dsimp [z, w] at hre
    simp only [mul_re, ofReal_re, I_re, ofReal_im, I_im, mul_one,
      sub_zero] at hre
    linarith
  have hplus : ∀ p : ℝ × ℝ, z p.1 + w p.2 ≠ 0 := by
    intro p heq
    have hre := congrArg Complex.re heq
    dsimp [z, w] at hre
    simp only [mul_re, ofReal_re, I_re, ofReal_im, I_im, mul_one] at hre
    linarith
  have hinvMinus : Continuous (fun p : ℝ × ℝ ↦
      (1 : ℂ) / (z p.1 - w p.2)) :=
    continuous_const.div (hzp.sub hwp) hminus
  have hinvPlus : Continuous (fun p : ℝ × ℝ ↦
      (1 : ℂ) / (z p.1 + w p.2)) :=
    continuous_const.div (hzp.add hwp) hplus
  have hproduct := hlogp.mul (hinvMinus.sub hinvPlus)
  change Continuous (fun p : ℝ × ℝ ↦
    xiSpectralNegativeLogDerivative (w p.2) *
      (1 / (z p.1 - w p.2) - 1 / (z p.1 + w p.2)))
  convert hproduct using 1
  ext p
  rfl

/-- The real folded vertical integral is continuous in the safe-axis
observation height at every quantitative cutoff. -/
theorem
    continuous_intervalIntegral_re_xiSpectralBlaschkeRightFoldedVerticalKernel_quantitative
    (n : ℕ) :
    Continuous (fun v : ℝ ↦ ∫ y : ℝ in (0 : ℝ)..1,
      (xiSpectralBlaschkeRightFoldedVerticalKernel
        (quantitativeSpectralBoundaryTruncation n)
        ((v : ℂ) * Complex.I) y).re) := by
  have hkernel :=
    continuous_uncurry_xiSpectralBlaschkeRightFoldedVerticalKernel_quantitative
      n
  have hreal : Continuous
      (Function.uncurry (fun v y : ℝ ↦
        (xiSpectralBlaschkeRightFoldedVerticalKernel
          (quantitativeSpectralBoundaryTruncation n)
          ((v : ℂ) * Complex.I) y).re)) := by
    exact Complex.continuous_re.comp hkernel
  exact
    intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
      hreal 0 1

/-- Above the safe contour, the normalized detector-recovery error is the
negative folded right-line action. -/
theorem
    xiSpectralBlaschkePairedBoundaryErrorSafeAxisResponseWindow_quantitative_eq_folded
    {v : ℝ} (hv : 1 < v) (n : ℕ) :
    xiSpectralBlaschkePairedBoundaryErrorSafeAxisResponseWindow
        (quantitativeSpectralBoundaryTruncation n) v =
      -(2 / Real.pi) *
        (∫ y : ℝ in (0 : ℝ)..1,
          (xiSpectralBlaschkeRightFoldedVerticalKernel
            (quantitativeSpectralBoundaryTruncation n)
            ((v : ℂ) * Complex.I) y).re) := by
  let T : ℝ := quantitativeSpectralBoundaryTruncation n
  let R : ℂ := xiSpectralBlaschkeSignedVerticalRemainderWindow T 0
    ((v : ℂ) * Complex.I)
  let J : ℝ := ∫ y : ℝ in (0 : ℝ)..1,
    (xiSpectralBlaschkeRightFoldedVerticalKernel T
      ((v : ℂ) * Complex.I) y).re
  have hT : 0 ≤ T := by
    exact (Nat.cast_nonneg n).trans
      (quantitativeSpectralBoundaryTruncation_spec n).1.le
  have hboundary : ∀ rho : NontrivialZetaZero,
      |(zetaSpectralCoordinate rho.1).re| ≠ T := by
    simpa [T] using quantitativeSpectralBoundaryTruncation_zeroFree n
  have hfold : -Complex.I * R = ((2 * J : ℝ) : ℂ) := by
    simpa [R, J] using
      neg_I_mul_xiSpectralBlaschkeSignedVerticalRemainderWindow_zero_imaginary
        hv hT hboundary
  unfold xiSpectralBlaschkePairedBoundaryErrorSafeAxisResponseWindow
  rw [xiSpectralBlaschkePairedBoundaryDetectorErrorWindow_eq_neg_vertical]
  change (1 / Real.pi) * (-Complex.I * -R).re = -(2 / Real.pi) * J
  have hneg : -Complex.I * -R = -(-Complex.I * R) := by ring
  rw [hneg, hfold]
  simp
  ring

/-- At every quantitative cutoff, the real safe-axis recovery error is
continuous throughout the open region above the safe contour. -/
theorem
    continuousOn_xiSpectralBlaschkePairedBoundaryErrorSafeAxisResponseWindow_quantitative
    (n : ℕ) :
    ContinuousOn
      (xiSpectralBlaschkePairedBoundaryErrorSafeAxisResponseWindow
        (quantitativeSpectralBoundaryTruncation n)) (Ioi 1) := by
  let G : ℝ → ℝ := fun v ↦
    -(2 / Real.pi) *
      (∫ y : ℝ in (0 : ℝ)..1,
        (xiSpectralBlaschkeRightFoldedVerticalKernel
          (quantitativeSpectralBoundaryTruncation n)
          ((v : ℂ) * Complex.I) y).re)
  have hG : Continuous G := by
    dsimp [G]
    exact continuous_const.mul
      (continuous_intervalIntegral_re_xiSpectralBlaschkeRightFoldedVerticalKernel_quantitative
        n)
  apply hG.continuousOn.congr
  intro v hv
  simpa [G] using
    xiSpectralBlaschkePairedBoundaryErrorSafeAxisResponseWindow_quantitative_eq_folded
      hv n

/-- The normalized recovery error is interval integrable on every compact
height segment strictly above the safe contour. -/
theorem
    intervalIntegrable_xiSpectralBlaschkePairedBoundaryErrorSafeAxisResponseWindow_quantitative
    {a b : ℝ} (ha : 1 < a) (hab : a ≤ b) (n : ℕ) :
    IntervalIntegrable
      (xiSpectralBlaschkePairedBoundaryErrorSafeAxisResponseWindow
        (quantitativeSpectralBoundaryTruncation n)) volume a b := by
  apply ContinuousOn.intervalIntegrable_of_Icc hab
  exact
    (continuousOn_xiSpectralBlaschkePairedBoundaryErrorSafeAxisResponseWindow_quantitative
      n).mono (fun v hv ↦ ha.trans_le hv.1)

/-- The negative finite Blaschke transport response is interval integrable
on every finite safe-axis segment. -/
theorem
    intervalIntegrable_neg_two_mul_re_neg_I_blaschkeLogDerivativeWindow_safeAxis_segment
    {a b : ℝ} (ha : 1 ≤ a) (hab : a ≤ b) (T : ℝ) :
    IntervalIntegrable
      (fun y : ℝ ↦ -2 *
        (-Complex.I * riemannXiUpperBlaschkeLogDerivativeWindow
          (upperBoundaryApproachPoint 0 y) T).re) volume a b := by
  let g : ℝ → ℝ := fun y ↦ 2 *
    (-Complex.I * riemannXiUpperBlaschkeLogDerivativeWindow
      (upperBoundaryApproachPoint 0 y) T).re
  have hg : ContinuousOn g (uIcc a b) := by
    intro y hy
    rw [uIcc_of_le hab] at hy
    exact
      (continuousAt_two_mul_re_neg_I_blaschkeLogDerivativeWindow_safeAxis
        (ha.trans hy.1) T).continuousWithinAt
  have hneg : IntervalIntegrable (fun y ↦ -g y) volume a b :=
    hg.neg.intervalIntegrable
  apply hneg.congr
  intro y _hy
  dsimp [g]
  ring

/-- Exact finite static-boundary action identity.  The normalized paired
horizontal comparison equals the drop in finite vertical log defect plus the
integrated, still-visible vertical-remainder error. -/
theorem
    intervalIntegral_xiSpectralBlaschkePairedBoundarySafeAxisResponseWindow_eq_defectDrop_add_error
    {a b : ℝ} (ha : 1 < a) (hab : a ≤ b) (n : ℕ) :
    (∫ y : ℝ in a..b,
      xiSpectralBlaschkePairedBoundarySafeAxisResponseWindow
        (quantitativeSpectralBoundaryTruncation n) y) =
      riemannXiUpperVerticalLogDefectWindow 0 a
          (quantitativeSpectralBoundaryTruncation n) -
        riemannXiUpperVerticalLogDefectWindow 0 b
          (quantitativeSpectralBoundaryTruncation n) +
        ∫ y : ℝ in a..b,
          xiSpectralBlaschkePairedBoundaryErrorSafeAxisResponseWindow
            (quantitativeSpectralBoundaryTruncation n) y := by
  let T : ℝ := quantitativeSpectralBoundaryTruncation n
  let f : ℝ → ℝ := fun y ↦ -2 *
    (-Complex.I * riemannXiUpperBlaschkeLogDerivativeWindow
      (upperBoundaryApproachPoint 0 y) T).re
  let e : ℝ → ℝ :=
    xiSpectralBlaschkePairedBoundaryErrorSafeAxisResponseWindow T
  have hf : IntervalIntegrable f volume a b := by
    simpa [f] using
      intervalIntegrable_neg_two_mul_re_neg_I_blaschkeLogDerivativeWindow_safeAxis_segment
        ha.le hab T
  have he : IntervalIntegrable e volume a b := by
    simpa [e, T] using
      intervalIntegrable_xiSpectralBlaschkePairedBoundaryErrorSafeAxisResponseWindow_quantitative
        ha hab n
  calc
    (∫ y : ℝ in a..b,
        xiSpectralBlaschkePairedBoundarySafeAxisResponseWindow T y) =
        ∫ y : ℝ in a..b, f y + e y := by
      apply intervalIntegral.integral_congr
      intro y _hy
      simpa [f, e, upperBoundaryApproachPoint, mul_comm] using
        xiSpectralBlaschkePairedBoundarySafeAxisResponseWindow_eq T y
    _ = (∫ y : ℝ in a..b, f y) + ∫ y : ℝ in a..b, e y := by
      exact intervalIntegral.integral_add hf he
    _ = _ := by
      rw [show (∫ y : ℝ in a..b, f y) =
          riemannXiUpperVerticalLogDefectWindow 0 a T -
            riemannXiUpperVerticalLogDefectWindow 0 b T by
        simpa [f] using
          intervalIntegral_neg_two_mul_re_neg_I_blaschkeLogDerivativeWindow_safeAxis_segment
            ha.le hab T]

/-- The normalized real recovery response tends uniformly to zero on every
compact safe-axis height interval strictly above `1`. -/
theorem
    tendstoUniformlyOn_xiSpectralBlaschkePairedBoundaryErrorSafeAxisResponseWindow_quantitative_zero
    {a b : ℝ} (ha : 1 < a) :
    TendstoUniformlyOn
      (fun n : ℕ ↦
        xiSpectralBlaschkePairedBoundaryErrorSafeAxisResponseWindow
          (quantitativeSpectralBoundaryTruncation n))
      (fun _v : ℝ ↦ 0) atTop (Icc a b) := by
  have hcomplex :=
    tendstoUniformlyOn_xiSpectralBlaschkePairedBoundaryDetectorErrorWindow_quantitative_zero
      (b := b) ha
  have hscaled :=
    (uniformContinuous_const_smul (-Complex.I)).comp_tendstoUniformlyOn
      hcomplex
  have hre := hscaled.re
  have hnormalized :=
    (uniformContinuous_const_smul (1 / Real.pi : ℝ)).comp_tendstoUniformlyOn
      hre
  have heq :
      (fun n : ℕ ↦
        xiSpectralBlaschkePairedBoundaryErrorSafeAxisResponseWindow
          (quantitativeSpectralBoundaryTruncation n)) =
        fun n v ↦ Real.pi⁻¹ *
          (xiSpectralBlaschkePairedBoundaryDetectorErrorWindow
            (quantitativeSpectralBoundaryTruncation n) v).im := by
    funext n v
    unfold xiSpectralBlaschkePairedBoundaryErrorSafeAxisResponseWindow
    simp [mul_re]
  rw [heq]
  simpa [Function.comp_def, smul_eq_mul] using hnormalized

/-- The integrated normalized recovery error vanishes on every fixed compact
safe-axis height segment as the quantitative cutoff grows. -/
theorem
    tendsto_intervalIntegral_xiSpectralBlaschkePairedBoundaryErrorSafeAxisResponseWindow_quantitative_zero
    {a b : ℝ} (ha : 1 < a) (hab : a ≤ b) :
    Tendsto
      (fun n : ℕ ↦ ∫ y : ℝ in a..b,
        xiSpectralBlaschkePairedBoundaryErrorSafeAxisResponseWindow
          (quantitativeSpectralBoundaryTruncation n) y)
      atTop (nhds 0) := by
  have huniform :=
    tendstoUniformlyOn_xiSpectralBlaschkePairedBoundaryErrorSafeAxisResponseWindow_quantitative_zero
      (b := b) ha
  have huniform' : TendstoUniformlyOn
      (fun n : ℕ ↦
        xiSpectralBlaschkePairedBoundaryErrorSafeAxisResponseWindow
          (quantitativeSpectralBoundaryTruncation n))
      (fun _v : ℝ ↦ 0) atTop (uIcc a b) := by
    simpa [uIcc_of_le hab] using huniform
  have hcontinuous : ∀ᶠ n : ℕ in atTop,
      ContinuousOn
        (xiSpectralBlaschkePairedBoundaryErrorSafeAxisResponseWindow
          (quantitativeSpectralBoundaryTruncation n)) (uIcc a b) := by
    exact Eventually.of_forall fun n ↦
      (continuousOn_xiSpectralBlaschkePairedBoundaryErrorSafeAxisResponseWindow_quantitative
        n).mono (by
          intro v hv
          rw [uIcc_of_le hab] at hv
          exact ha.trans_le hv.1)
  have hlimit :=
    huniform'.tendsto_intervalIntegral_of_continuousOn
      (μ := volume) hcontinuous
  simpa using hlimit

/-- Integrated static-boundary recovery.  On every fixed compact safe-axis
segment, the normalized paired horizontal comparison converges to the drop
in the finite complete RH-equivalent hyperbolic log-defect mass between the
two endpoint heights. -/
theorem
    tendsto_intervalIntegral_xiSpectralBlaschkePairedBoundarySafeAxisResponseWindow_quantitative_completeDefectDrop
    {a b : ℝ} (ha : 1 < a) (hab : a ≤ b) :
    Tendsto
      (fun n : ℕ ↦ ∫ y : ℝ in a..b,
        xiSpectralBlaschkePairedBoundarySafeAxisResponseWindow
          (quantitativeSpectralBoundaryTruncation n) y)
      atTop
      (nhds
        ((riemannXiUpperHyperbolicLogDefectMass
            ((a : ℂ) * Complex.I)).toReal -
          (riemannXiUpperHyperbolicLogDefectMass
            ((b : ℂ) * Complex.I)).toReal)) := by
  have haLimit :=
    tendsto_riemannXiUpperVerticalLogDefectWindow_zero_quantitative_complete_toReal_imaginarySafeAxis
      ha.le
  have hbLimit :=
    tendsto_riemannXiUpperVerticalLogDefectWindow_zero_quantitative_complete_toReal_imaginarySafeAxis
      (ha.le.trans hab)
  have herror :=
    tendsto_intervalIntegral_xiSpectralBlaschkePairedBoundaryErrorSafeAxisResponseWindow_quantitative_zero
      ha hab
  have hcombined : Tendsto
      (fun n : ℕ ↦
        riemannXiUpperVerticalLogDefectWindow 0 a
            (quantitativeSpectralBoundaryTruncation n) -
          riemannXiUpperVerticalLogDefectWindow 0 b
            (quantitativeSpectralBoundaryTruncation n) +
          ∫ y : ℝ in a..b,
            xiSpectralBlaschkePairedBoundaryErrorSafeAxisResponseWindow
              (quantitativeSpectralBoundaryTruncation n) y)
      atTop
      (nhds
        ((riemannXiUpperHyperbolicLogDefectMass
            ((a : ℂ) * Complex.I)).toReal -
          (riemannXiUpperHyperbolicLogDefectMass
            ((b : ℂ) * Complex.I)).toReal)) := by
    simpa using (haLimit.sub hbLimit).add herror
  apply hcombined.congr'
  exact Eventually.of_forall fun n ↦
    (intervalIntegral_xiSpectralBlaschkePairedBoundarySafeAxisResponseWindow_eq_defectDrop_add_error
      ha hab n).symm

/-- The finite negative Blaschke transport responses converge uniformly on
every compact safe-axis segment to the complete response. -/
theorem
    tendstoUniformlyOn_neg_two_mul_re_neg_I_blaschkeLogDerivativeWindow_imaginary_quantitative_complete
    {a b : ℝ} (ha : 1 < a) :
    TendstoUniformlyOn
      (fun n : ℕ ↦ fun v : ℝ ↦ -2 *
        (-Complex.I * riemannXiUpperBlaschkeLogDerivativeWindow
          ((v : ℂ) * Complex.I)
          (quantitativeSpectralBoundaryTruncation n)).re)
      (fun v : ℝ ↦ -2 *
        (-Complex.I * riemannXiUpperBlaschkeCompleteLogDerivative
          ((v : ℂ) * Complex.I)).re)
      atTop (Icc a b) := by
  have hlog :=
    tendstoUniformlyOn_riemannXiUpperBlaschkeLogDerivativeWindow_imaginary_quantitative_complete
      (b := b) ha
  have hscaled :=
    (uniformContinuous_const_smul (-Complex.I)).comp_tendstoUniformlyOn
      hlog
  have hre := hscaled.re
  have hreal :=
    (uniformContinuous_const_smul (-2 : ℝ)).comp_tendstoUniformlyOn hre
  simpa [Function.comp_def, smul_eq_mul] using hreal

/-- On a compact safe-axis segment, the complete Blaschke transport action
is exactly the drop in the finite complete hyperbolic log-defect mass between
the endpoint heights. -/
theorem
    intervalIntegral_neg_two_mul_re_neg_I_completeBlaschkeLogDerivative_imaginary_eq_completeDefectDrop
    {a b : ℝ} (ha : 1 < a) (hab : a ≤ b) :
    (∫ y : ℝ in a..b, -2 *
      (-Complex.I * riemannXiUpperBlaschkeCompleteLogDerivative
        ((y : ℂ) * Complex.I)).re) =
      (riemannXiUpperHyperbolicLogDefectMass
          ((a : ℂ) * Complex.I)).toReal -
        (riemannXiUpperHyperbolicLogDefectMass
          ((b : ℂ) * Complex.I)).toReal := by
  let F : ℕ → ℝ → ℝ := fun n v ↦ -2 *
    (-Complex.I * riemannXiUpperBlaschkeLogDerivativeWindow
      ((v : ℂ) * Complex.I)
      (quantitativeSpectralBoundaryTruncation n)).re
  let f : ℝ → ℝ := fun v ↦ -2 *
    (-Complex.I * riemannXiUpperBlaschkeCompleteLogDerivative
      ((v : ℂ) * Complex.I)).re
  have huniform : TendstoUniformlyOn F f atTop (uIcc a b) := by
    simpa [F, f, uIcc_of_le hab] using
      tendstoUniformlyOn_neg_two_mul_re_neg_I_blaschkeLogDerivativeWindow_imaginary_quantitative_complete
        (b := b) ha
  have hcontinuous : ∀ᶠ n : ℕ in atTop, ContinuousOn (F n) (uIcc a b) := by
    exact Eventually.of_forall fun n ↦ by
      intro v hv
      rw [uIcc_of_le hab] at hv
      have hpos :=
        continuousAt_two_mul_re_neg_I_blaschkeLogDerivativeWindow_safeAxis
          (ha.le.trans hv.1)
          (quantitativeSpectralBoundaryTruncation n)
      have hfun : F n = -(fun u : ℝ ↦ 2 *
          (-Complex.I * riemannXiUpperBlaschkeLogDerivativeWindow
            (upperBoundaryApproachPoint 0 u)
            (quantitativeSpectralBoundaryTruncation n)).re) := by
        funext u
        simp [F, upperBoundaryApproachPoint, mul_comm]
      rw [hfun]
      exact hpos.neg.continuousWithinAt
  have hintegral : Tendsto
      (fun n : ℕ ↦ ∫ y : ℝ in a..b, F n y)
      atTop (nhds (∫ y : ℝ in a..b, f y)) :=
    huniform.tendsto_intervalIntegral_of_continuousOn
      (μ := volume) hcontinuous
  have haLimit :=
    tendsto_riemannXiUpperVerticalLogDefectWindow_zero_quantitative_complete_toReal_imaginarySafeAxis
      ha.le
  have hbLimit :=
    tendsto_riemannXiUpperVerticalLogDefectWindow_zero_quantitative_complete_toReal_imaginarySafeAxis
      (ha.le.trans hab)
  have hdefect : Tendsto
      (fun n : ℕ ↦ ∫ y : ℝ in a..b, F n y)
      atTop
      (nhds
        ((riemannXiUpperHyperbolicLogDefectMass
            ((a : ℂ) * Complex.I)).toReal -
          (riemannXiUpperHyperbolicLogDefectMass
            ((b : ℂ) * Complex.I)).toReal)) := by
    apply (haLimit.sub hbLimit).congr'
    exact Eventually.of_forall fun n ↦ by
      dsimp [F]
      simpa [upperBoundaryApproachPoint, mul_comm] using
        (intervalIntegral_neg_two_mul_re_neg_I_blaschkeLogDerivativeWindow_safeAxis_segment
          ha.le hab (quantitativeSpectralBoundaryTruncation n)).symm
  change (∫ y : ℝ in a..b, f y) = _
  exact tendsto_nhds_unique hintegral hdefect

/-- Terminal compact-height bridge.  The actual normalized arithmetic
paired-boundary action converges to the complete Blaschke detector action,
and that complete action is exactly the drop in the finite complete
RH-equivalent log defect between the endpoint heights. -/
theorem
    staticBoundarySafeAxisAction_tendsto_completeDetector_and_eq_completeDefectDrop
    {a b : ℝ} (ha : 1 < a) (hab : a ≤ b) :
    Tendsto
      (fun n : ℕ ↦ ∫ y : ℝ in a..b,
        xiSpectralBlaschkePairedBoundarySafeAxisResponseWindow
          (quantitativeSpectralBoundaryTruncation n) y)
      atTop
      (nhds (∫ y : ℝ in a..b, -2 *
        (-Complex.I * riemannXiUpperBlaschkeCompleteLogDerivative
          ((y : ℂ) * Complex.I)).re)) ∧
      (∫ y : ℝ in a..b, -2 *
        (-Complex.I * riemannXiUpperBlaschkeCompleteLogDerivative
          ((y : ℂ) * Complex.I)).re) =
        (riemannXiUpperHyperbolicLogDefectMass
            ((a : ℂ) * Complex.I)).toReal -
          (riemannXiUpperHyperbolicLogDefectMass
            ((b : ℂ) * Complex.I)).toReal := by
  have hdrop :=
    intervalIntegral_neg_two_mul_re_neg_I_completeBlaschkeLogDerivative_imaginary_eq_completeDefectDrop
      ha hab
  constructor
  · rw [hdrop]
    exact
      tendsto_intervalIntegral_xiSpectralBlaschkePairedBoundarySafeAxisResponseWindow_quantitative_completeDefectDrop
        ha hab
  · exact hdrop

end

end RiemannGaussian
