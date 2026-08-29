import RiemannGaussian.RiemannXiSuzukiPointwiseChebyshevLogAverageLaplaceBoundaryHeatSelectedHalfStripXiLogNormReflection

/-!
# Reflect the complete xi log-norm gradient frontier

The xi log-norm potential is even and the real boundary-heat kernel is odd in
the shifted real coordinate. This module differentiates those symmetries and
proves that the full gradient pairing is odd. A checked iterated-integral
change of variables then reflects the bulk together with both vertical sides.

At every finite stage, the live detector scalar is thereby rewritten wholly
on positive shifted coordinates. Its actual completed-xi rectangle lies
strictly in `1 / 2 < Re s < 1`; the inner edge tends to `1 / 2` from above and
the outer edge tends to `1` from below. The reflected functional keeps the
same unnormalized detector limit.

This is a symmetry and domain reduction only. It gives no decay estimate in
the open critical half-strip and does not enter the absolute Dirichlet-series
region.
-/

namespace RiemannGaussian

noncomputable section

open Complex Filter MeasureTheory Set
open scoped Interval Topology

/-- The horizontal derivative of the odd real heat kernel is even in the
shifted real coordinate. -/
theorem deriv_suzukiChebyshevLaplaceBoundaryHeatRealKernel_neg_realCoordinate
    (x tau a y : ℝ) :
    deriv (fun u : ℝ =>
      suzukiChebyshevLaplaceBoundaryHeatRealKernel x tau u y) (-a) =
      deriv (fun u : ℝ =>
        suzukiChebyshevLaplaceBoundaryHeatRealKernel x tau u y) a := by
  have hfun :
      (fun u : ℝ =>
        suzukiChebyshevLaplaceBoundaryHeatRealKernel x tau (-u) y) =
        -(fun u : ℝ =>
          suzukiChebyshevLaplaceBoundaryHeatRealKernel x tau u y) := by
    funext u
    exact
      suzukiChebyshevLaplaceBoundaryHeatRealKernel_neg_realCoordinate
        x tau u y
  have hder := congrArg (fun f : ℝ → ℝ => deriv f a) hfun
  have hneg := deriv_comp_neg
    (f := fun u : ℝ =>
      suzukiChebyshevLaplaceBoundaryHeatRealKernel x tau u y) (x := a)
  rw [hneg, deriv.neg] at hder
  linarith

/-- The vertical derivative of the real heat kernel remains odd in the
shifted real coordinate. -/
theorem deriv_suzukiChebyshevLaplaceBoundaryHeatRealKernel_neg_realCoordinate_imaginaryCoordinate
    (x tau a y : ℝ) :
    deriv (fun v : ℝ =>
      suzukiChebyshevLaplaceBoundaryHeatRealKernel x tau (-a) v) y =
      -deriv (fun v : ℝ =>
        suzukiChebyshevLaplaceBoundaryHeatRealKernel x tau a v) y := by
  have hfun :
      (fun v : ℝ =>
        suzukiChebyshevLaplaceBoundaryHeatRealKernel x tau (-a) v) =
        -(fun v : ℝ =>
          suzukiChebyshevLaplaceBoundaryHeatRealKernel x tau a v) := by
    funext v
    exact
      suzukiChebyshevLaplaceBoundaryHeatRealKernel_neg_realCoordinate
        x tau a v
  have hder := congrArg (fun f : ℝ → ℝ => deriv f y) hfun
  simpa only [deriv.neg] using hder

/-- The vertical derivative of the even xi log-norm potential is even in the
shifted real coordinate. -/
theorem deriv_shiftedRiemannXiLogNorm_neg_realCoordinate_imaginaryCoordinate
    (a y : ℝ) :
    deriv (shiftedRiemannXiLogNorm (-a)) y =
      deriv (shiftedRiemannXiLogNorm a) y := by
  have hfun : shiftedRiemannXiLogNorm (-a) = shiftedRiemannXiLogNorm a := by
    funext v
    exact shiftedRiemannXiLogNorm_neg_realCoordinate a v
  exact congrArg (fun f : ℝ → ℝ => deriv f y) hfun

/-- The Euclidean heat-gradient--xi-log-norm-gradient pairing is odd in the
shifted real coordinate. -/
theorem suzukiChebyshevLaplaceBoundaryHeatXiLogNormGradientIntegrand_neg_realCoordinate
    (x tau a y : ℝ) :
    suzukiChebyshevLaplaceBoundaryHeatXiLogNormGradientIntegrand
        x tau (-a) y =
      -suzukiChebyshevLaplaceBoundaryHeatXiLogNormGradientIntegrand
        x tau a y := by
  unfold suzukiChebyshevLaplaceBoundaryHeatXiLogNormGradientIntegrand
  rw [deriv_suzukiChebyshevLaplaceBoundaryHeatRealKernel_neg_realCoordinate,
    deriv_shiftedRiemannXiLogNorm_neg_realCoordinate,
    deriv_suzukiChebyshevLaplaceBoundaryHeatRealKernel_neg_realCoordinate_imaginaryCoordinate,
    deriv_shiftedRiemannXiLogNorm_neg_realCoordinate_imaginaryCoordinate]
  ring

/-- Reflecting the real coordinate reverses the sign of the complexified
iterated rectangular integral of the odd gradient pairing. -/
theorem rectangularAreaIntegral_suzukiChebyshevLaplaceBoundaryHeatXiLogNormGradient_ofReal_reflect
    (x tau l r b u : ℝ) :
    rectangularAreaIntegral (-r) (-l) b u (fun p : ℂ =>
      (suzukiChebyshevLaplaceBoundaryHeatXiLogNormGradientIntegrand
        x tau p.re p.im : ℂ)) =
      -rectangularAreaIntegral l r b u (fun p : ℂ =>
        (suzukiChebyshevLaplaceBoundaryHeatXiLogNormGradientIntegrand
          x tau p.re p.im : ℂ)) := by
  unfold rectangularAreaIntegral
  simp only [Complex.add_re, Complex.add_im, Complex.ofReal_re,
    Complex.ofReal_im, Complex.mul_re, Complex.mul_im, Complex.I_re,
    Complex.I_im, mul_zero, sub_zero, zero_add, add_zero, mul_one]
  let F : ℝ → ℂ := fun a =>
    ∫ y : ℝ in b..u,
      (suzukiChebyshevLaplaceBoundaryHeatXiLogNormGradientIntegrand
        x tau a y : ℂ)
  have hchange := intervalIntegral.integral_comp_neg
    (f := F) (a := l) (b := r)
  change (∫ a : ℝ in -r..-l, F a) = -(∫ a : ℝ in l..r, F a)
  rw [← hchange]
  rw [← intervalIntegral.integral_neg]
  apply intervalIntegral.integral_congr
  intro a ha
  dsimp only [F]
  rw [← intervalIntegral.integral_neg]
  apply intervalIntegral.integral_congr
  intro y hy
  simpa using congrArg (fun q : ℝ => (q : ℂ))
    (suzukiChebyshevLaplaceBoundaryHeatXiLogNormGradientIntegrand_neg_realCoordinate
      x tau a y)

/-- The real part of the complexified iterated gradient integral is the
ordinary through-divisor planar integral on a selected rectangle. -/
theorem rectangularAreaIntegral_suzukiChebyshevLaplaceBoundaryHeatXiLogNormGradient_selected_re
    (x tau : ℝ) (n : ℕ) :
    (rectangularAreaIntegral
      (selectedLaplaceSeparatedLeftBoundary n)
      (selectedLaplaceSeparatedRightBoundary n)
      (-quantitativeSpectralBoundaryTruncation n)
      (quantitativeSpectralBoundaryTruncation n)
      (fun p : ℂ =>
        (suzukiChebyshevLaplaceBoundaryHeatXiLogNormGradientIntegrand
          x tau p.re p.im : ℂ))).re =
      ∫ p : ℂ in
        ([[selectedLaplaceSeparatedLeftBoundary n,
            selectedLaplaceSeparatedRightBoundary n]] ×ℂ
          [[-quantitativeSpectralBoundaryTruncation n,
            quantitativeSpectralBoundaryTruncation n]]),
        suzukiChebyshevLaplaceBoundaryHeatXiLogNormGradientIntegrand
          x tau p.re p.im := by
  let l : ℝ := selectedLaplaceSeparatedLeftBoundary n
  let r : ℝ := selectedLaplaceSeparatedRightBoundary n
  let T : ℝ := quantitativeSpectralBoundaryTruncation n
  let R : Set ℂ := [[l, r]] ×ℂ [[-T, T]]
  let G : ℂ → ℝ := fun p =>
    suzukiChebyshevLaplaceBoundaryHeatXiLogNormGradientIntegrand
      x tau p.re p.im
  have hlr : l ≤ r :=
    (selectedLaplaceSeparatedLeftBoundary_lt_rightBoundary n).le
  have hbu : -T ≤ T := by
    linarith [quantitativeSpectralBoundaryTruncation_nonneg n]
  have hreal : IntegrableOn G R volume := by
    simpa [G, R, l, r, T] using
      integrableOn_suzukiChebyshevLaplaceBoundaryHeatXiLogNormGradient_selected
        x tau n
  have hcomplex : IntegrableOn (fun p : ℂ => (G p : ℂ)) R volume :=
    hreal.ofReal
  have hrect := rectangularAreaIntegral_eq_setIntegral
    hlr hbu (fun p : ℂ => (G p : ℂ)) hcomplex
  change
    (rectangularAreaIntegral l r (-T) T
      (fun p : ℂ => (G p : ℂ))).re =
      ∫ p : ℂ in R, G p
  rw [hrect]
  exact (integral_re hcomplex).symm

/-- The xi log-norm gradient pairing is genuinely planar integrable on every
reflected positive-half-strip rectangle, including through its finite xi
divisor. -/
theorem integrableOn_suzukiChebyshevLaplaceBoundaryHeatXiLogNormGradient_positiveHalfStrip
    (x tau : ℝ) (n : ℕ) :
    IntegrableOn (fun p : ℂ =>
      suzukiChebyshevLaplaceBoundaryHeatXiLogNormGradientIntegrand
        x tau p.re p.im)
      ([[-selectedLaplaceSeparatedRightBoundary n,
          -selectedLaplaceSeparatedLeftBoundary n]] ×ℂ
        [[-quantitativeSpectralBoundaryTruncation n,
          quantitativeSpectralBoundaryTruncation n]]) volume := by
  let l : ℝ := -selectedLaplaceSeparatedRightBoundary n
  let r : ℝ := -selectedLaplaceSeparatedLeftBoundary n
  let T : ℝ := quantitativeSpectralBoundaryTruncation n
  let R : Set ℂ := [[l, r]] ×ℂ [[-T, T]]
  have hT0 : 0 ≤ T := quantitativeSpectralBoundaryTruncation_nonneg n
  have hlr : l ≤ r := by
    dsimp only [l, r]
    linarith [selectedLaplaceSeparatedLeftBoundary_lt_rightBoundary n]
  have hbu : -T ≤ T := by linarith
  have hrectangle : R ⊆ suzukiChebyshevLaplaceFiniteSlab T := by
    intro p hp
    dsimp only [R] at hp
    rw [uIcc_of_le hlr, uIcc_of_le hbu] at hp
    have hlpos : 0 < l := by
      dsimp only [l]
      linarith [(selectedLaplaceSeparatedRightBoundary_spec n).2.1]
    have hpre : 0 < p.re := hlpos.trans_le hp.1.1
    change 0 < (p + 1 / 2).re ∧ |p.im| ≤ T
    constructor
    · rw [Complex.add_re]
      norm_num
      linarith
    · exact abs_le.mpr hp.2
  have hfull : IntegrableOn
      (suzukiChebyshevLaplaceBoundaryHeatWeightedResponseSource x tau)
      R volume := by
    exact
      integrableOn_suzukiChebyshevLaplaceBoundaryHeatWeightedResponseSource_finiteRectangle
        x tau l r (-T) T hT0 hrectangle
  have hregularAnalytic : ∀ p ∈ R,
      AnalyticAt ℂ suzukiChebyshevLogAverageLaplaceRegularCorrection p := by
    intro p hp
    apply
      analyticAt_suzukiChebyshevLogAverageLaplaceRegularCorrection_of_re_gt_neg_half
    have hpSlab := hrectangle hp
    change 0 < (p + 1 / 2).re ∧ |p.im| ≤ T at hpSlab
    rw [Complex.add_re] at hpSlab
    norm_num at hpSlab
    linarith
  have hregular : IntegrableOn
      (suzukiChebyshevLaplaceBoundaryHeatWeightedRegularCorrectionSource
        x tau) R volume := by
    have hcontinuous : ContinuousOn
        (suzukiChebyshevLaplaceBoundaryHeatWeightedRegularCorrectionSource
          x tau) R := by
      unfold
        suzukiChebyshevLaplaceBoundaryHeatWeightedRegularCorrectionSource
      exact
        (continuous_suzukiChebyshevLaplaceBoundaryHeatCauchyGreenSource
            x tau).continuousOn.mul
          (show AnalyticOnNhd ℂ
              suzukiChebyshevLogAverageLaplaceRegularCorrection R from
            hregularAnalytic).continuousOn
    exact hcontinuous.integrableOn_compact
      (isCompact_uIcc.reProdIm isCompact_uIcc)
  have hxi : IntegrableOn
      (suzukiChebyshevLaplaceBoundaryHeatWeightedXiLogDerivativeSource
        x tau) R volume := by
    have hsub := hfull.sub hregular
    apply hsub.congr_fun _
      (isCompact_uIcc.reProdIm isCompact_uIcc).measurableSet
    intro p hp
    change
      suzukiChebyshevLaplaceBoundaryHeatWeightedResponseSource x tau p -
          suzukiChebyshevLaplaceBoundaryHeatWeightedRegularCorrectionSource
            x tau p =
        suzukiChebyshevLaplaceBoundaryHeatWeightedXiLogDerivativeSource
          x tau p
    rw [suzukiChebyshevLaplaceBoundaryHeatWeightedResponseSource_eq_xiLogDerivative_add_regularCorrection]
    ring
  have hbulk : IntegrableOn
      (fun p : ℂ =>
        suzukiChebyshevLaplaceBoundaryHeatXiBulkScalarIntegrand
          x tau p.re p.im) R volume := by
    have him := hxi.im
    apply him.congr
    exact Filter.Eventually.of_forall fun p =>
      suzukiChebyshevLaplaceBoundaryHeatWeightedXiLogDerivativeSource_im
        x tau p
  let W : Finset ℂ := suzukiChebyshevLaplaceZeroWindow T
  have hRmeas : MeasurableSet R :=
    (isCompact_uIcc.reProdIm isCompact_uIcc).measurableSet
  have hWnull : (volume.restrict R) (W : Set ℂ) = 0 :=
    W.measure_zero (volume.restrict R)
  have havoid : ∀ᵐ p : ℂ ∂volume.restrict R, p ∉ (W : Set ℂ) :=
    measure_eq_zero_iff_ae_notMem.mp hWnull
  have hae :
      ∀ᵐ p : ℂ ∂volume.restrict R,
        suzukiChebyshevLaplaceBoundaryHeatXiBulkScalarIntegrand
            x tau p.re p.im =
          suzukiChebyshevLaplaceBoundaryHeatXiLogNormGradientIntegrand
            x tau p.re p.im := by
    filter_upwards [ae_restrict_mem hRmeas, havoid] with p hpR hpW
    have hpR' : p.re ∈ [[l, r]] ∧ p.im ∈ [[-T, T]] := hpR
    rw [uIcc_of_le hlr, uIcc_of_le hbu] at hpR'
    have him : |p.im| ≤ T := abs_le.mpr hpR'.2
    have hpzero : riemannXi (p + 1 / 2) ≠ 0 := by
      intro hzero
      apply hpW
      exact (mem_suzukiChebyshevLaplaceZeroWindow_iff hT0 p).mpr
        ⟨hzero, him⟩
    have hpcoord :
        (((p.re + 1 / 2 : ℝ) : ℂ) + (p.im : ℂ) * Complex.I) =
          p + 1 / 2 := by
      apply Complex.ext <;> simp
    apply
      suzukiChebyshevLaplaceBoundaryHeatXiBulkScalarIntegrand_eq_logNorm_gradient
    rw [hpcoord]
    exact hpzero
  apply hbulk.congr
  exact hae

/-- On the reflected positive rectangle, the real part of the complexified
iterated gradient integral is its genuine ordinary planar set integral. -/
theorem rectangularAreaIntegral_suzukiChebyshevLaplaceBoundaryHeatXiLogNormGradient_positiveHalfStrip_re
    (x tau : ℝ) (n : ℕ) :
    (rectangularAreaIntegral
      (-selectedLaplaceSeparatedRightBoundary n)
      (-selectedLaplaceSeparatedLeftBoundary n)
      (-quantitativeSpectralBoundaryTruncation n)
      (quantitativeSpectralBoundaryTruncation n)
      (fun p : ℂ =>
        (suzukiChebyshevLaplaceBoundaryHeatXiLogNormGradientIntegrand
          x tau p.re p.im : ℂ))).re =
      ∫ p : ℂ in
        ([[-selectedLaplaceSeparatedRightBoundary n,
            -selectedLaplaceSeparatedLeftBoundary n]] ×ℂ
          [[-quantitativeSpectralBoundaryTruncation n,
            quantitativeSpectralBoundaryTruncation n]]),
        suzukiChebyshevLaplaceBoundaryHeatXiLogNormGradientIntegrand
          x tau p.re p.im := by
  let l : ℝ := -selectedLaplaceSeparatedRightBoundary n
  let r : ℝ := -selectedLaplaceSeparatedLeftBoundary n
  let T : ℝ := quantitativeSpectralBoundaryTruncation n
  let R : Set ℂ := [[l, r]] ×ℂ [[-T, T]]
  let G : ℂ → ℝ := fun p =>
    suzukiChebyshevLaplaceBoundaryHeatXiLogNormGradientIntegrand
      x tau p.re p.im
  have hlr : l ≤ r := by
    dsimp only [l, r]
    linarith [selectedLaplaceSeparatedLeftBoundary_lt_rightBoundary n]
  have hbu : -T ≤ T := by
    linarith [quantitativeSpectralBoundaryTruncation_nonneg n]
  have hreal : IntegrableOn G R volume := by
    simpa [G, R, l, r, T] using
      integrableOn_suzukiChebyshevLaplaceBoundaryHeatXiLogNormGradient_positiveHalfStrip
        x tau n
  have hcomplex : IntegrableOn (fun p : ℂ => (G p : ℂ)) R volume :=
    hreal.ofReal
  have hrect := rectangularAreaIntegral_eq_setIntegral
    hlr hbu (fun p : ℂ => (G p : ℂ)) hcomplex
  change
    (rectangularAreaIntegral l r (-T) T
      (fun p : ℂ => (G p : ℂ))).re =
      ∫ p : ℂ in R, G p
  rw [hrect]
  exact (integral_re hcomplex).symm

/-- The actual completed-xi coordinate of the reflected near-critical
selected boundary. -/
def selectedLaplaceReflectedRightXiRealCoordinate (n : ℕ) : ℝ :=
  1 / 2 - selectedLaplaceSeparatedRightBoundary n

/-- The reflected near-critical boundary lies in the positive shifted
interval `(0, 1 / 4)`. -/
theorem selectedLaplaceReflectedRightBoundary_spec (n : ℕ) :
    0 < -selectedLaplaceSeparatedRightBoundary n ∧
      -selectedLaplaceSeparatedRightBoundary n < 1 / 4 := by
  have hs := selectedLaplaceSeparatedRightBoundary_spec n
  have hw := selectedLaplaceEdgeWidth_le_quarter n
  constructor <;> linarith

/-- The corresponding actual completed-xi coordinate lies strictly between
`1 / 2` and `3 / 4`. -/
theorem selectedLaplaceReflectedRightXiRealCoordinate_spec (n : ℕ) :
    1 / 2 < selectedLaplaceReflectedRightXiRealCoordinate n ∧
      selectedLaplaceReflectedRightXiRealCoordinate n < 3 / 4 := by
  have hs := selectedLaplaceReflectedRightBoundary_spec n
  unfold selectedLaplaceReflectedRightXiRealCoordinate
  constructor <;> linarith

/-- The actual completed-xi coordinates of the reflected near-critical edge
tend to `1 / 2` from above. -/
theorem tendsto_selectedLaplaceReflectedRightXiRealCoordinate :
    Tendsto selectedLaplaceReflectedRightXiRealCoordinate atTop
      (𝓝 (1 / 2 : ℝ)) := by
  have hc : Tendsto (fun _ : ℕ => (1 / 2 : ℝ)) atTop
      (𝓝 (1 / 2 : ℝ)) := tendsto_const_nhds
  have h := hc.sub
    tendsto_selectedLaplaceSeparatedRightBoundary_zero
  convert h using 1
  · rfl
  · norm_num

/-- The complete boundary-plus-gradient representation on the positive
shifted half-strip, with both vertical sides and the bulk reflected. -/
def separatedSelectedLaplaceXiLogNormPositiveHalfStripGradientScalarHeat
    (x tau : ℝ) (n : ℕ) : ℝ :=
  (∫ y : ℝ in -quantitativeSpectralBoundaryTruncation n..
      quantitativeSpectralBoundaryTruncation n,
    suzukiChebyshevLaplaceBoundaryHeatXiLogNormBoundaryIntegrand x tau
      (-selectedLaplaceSeparatedRightBoundary n) y) -
  (∫ y : ℝ in -quantitativeSpectralBoundaryTruncation n..
      quantitativeSpectralBoundaryTruncation n,
    suzukiChebyshevLaplaceBoundaryHeatXiLogNormBoundaryIntegrand x tau
      (-selectedLaplaceSeparatedLeftBoundary n) y) +
  ∫ p : ℂ in
    ([[-selectedLaplaceSeparatedRightBoundary n,
        -selectedLaplaceSeparatedLeftBoundary n]] ×ℂ
      [[-quantitativeSpectralBoundaryTruncation n,
        quantitativeSpectralBoundaryTruncation n]]),
    suzukiChebyshevLaplaceBoundaryHeatXiLogNormGradientIntegrand
      x tau p.re p.im

/-- At every finite stage, reflection of both boundaries and the entire bulk
leaves the live detector scalar exactly unchanged. -/
theorem separatedSelectedLaplaceXiLogNormGradientScalarHeat_eq_positiveHalfStrip
    (x tau : ℝ) (n : ℕ) :
    separatedSelectedLaplaceXiLogNormGradientScalarHeat x tau n =
      separatedSelectedLaplaceXiLogNormPositiveHalfStripGradientScalarHeat
        x tau n := by
  let l : ℝ := selectedLaplaceSeparatedLeftBoundary n
  let r : ℝ := selectedLaplaceSeparatedRightBoundary n
  let T : ℝ := quantitativeSpectralBoundaryTruncation n
  have hright :
      (∫ y : ℝ in -T..T,
        suzukiChebyshevLaplaceBoundaryHeatXiLogNormBoundaryIntegrand
          x tau r y) =
        ∫ y : ℝ in -T..T,
          suzukiChebyshevLaplaceBoundaryHeatXiLogNormBoundaryIntegrand
            x tau (-r) y := by
    apply intervalIntegral.integral_congr
    intro y hy
    exact
      (suzukiChebyshevLaplaceBoundaryHeatXiLogNormBoundaryIntegrand_neg_realCoordinate
        x tau r y).symm
  have hleft :
      (∫ y : ℝ in -T..T,
        suzukiChebyshevLaplaceBoundaryHeatXiLogNormBoundaryIntegrand
          x tau l y) =
        ∫ y : ℝ in -T..T,
          suzukiChebyshevLaplaceBoundaryHeatXiLogNormBoundaryIntegrand
            x tau (-l) y := by
    apply intervalIntegral.integral_congr
    intro y hy
    exact
      (suzukiChebyshevLaplaceBoundaryHeatXiLogNormBoundaryIntegrand_neg_realCoordinate
        x tau l y).symm
  have hreflect :=
    rectangularAreaIntegral_suzukiChebyshevLaplaceBoundaryHeatXiLogNormGradient_ofReal_reflect
      x tau l r (-T) T
  have hbulk :
      (∫ p : ℂ in
        ([[-r, -l]] ×ℂ [[-T, T]]),
        suzukiChebyshevLaplaceBoundaryHeatXiLogNormGradientIntegrand
          x tau p.re p.im) =
        -(∫ p : ℂ in
          ([[l, r]] ×ℂ [[-T, T]]),
          suzukiChebyshevLaplaceBoundaryHeatXiLogNormGradientIntegrand
            x tau p.re p.im) := by
    have hre := congrArg Complex.re hreflect
    rw [Complex.neg_re] at hre
    have hpositive :=
      rectangularAreaIntegral_suzukiChebyshevLaplaceBoundaryHeatXiLogNormGradient_positiveHalfStrip_re
        x tau n
    change
      (rectangularAreaIntegral (-r) (-l) (-T) T (fun p : ℂ =>
        (suzukiChebyshevLaplaceBoundaryHeatXiLogNormGradientIntegrand
          x tau p.re p.im : ℂ))).re =
        ∫ p : ℂ in ([[-r, -l]] ×ℂ [[-T, T]]),
          suzukiChebyshevLaplaceBoundaryHeatXiLogNormGradientIntegrand
            x tau p.re p.im at hpositive
    have hnegative :=
      rectangularAreaIntegral_suzukiChebyshevLaplaceBoundaryHeatXiLogNormGradient_selected_re
        x tau n
    change
      (rectangularAreaIntegral l r (-T) T (fun p : ℂ =>
        (suzukiChebyshevLaplaceBoundaryHeatXiLogNormGradientIntegrand
          x tau p.re p.im : ℂ))).re =
        ∫ p : ℂ in ([[l, r]] ×ℂ [[-T, T]]),
          suzukiChebyshevLaplaceBoundaryHeatXiLogNormGradientIntegrand
            x tau p.re p.im at hnegative
    rw [hpositive, hnegative] at hre
    exact hre
  unfold separatedSelectedLaplaceXiLogNormGradientScalarHeat
    separatedSelectedLaplaceXiLogNormPositiveHalfStripGradientScalarHeat
  change
    (∫ y : ℝ in -T..T,
      suzukiChebyshevLaplaceBoundaryHeatXiLogNormBoundaryIntegrand
        x tau r y) -
      (∫ y : ℝ in -T..T,
        suzukiChebyshevLaplaceBoundaryHeatXiLogNormBoundaryIntegrand
          x tau l y) -
      (∫ p : ℂ in ([[l, r]] ×ℂ [[-T, T]]),
        suzukiChebyshevLaplaceBoundaryHeatXiLogNormGradientIntegrand
          x tau p.re p.im) =
    (∫ y : ℝ in -T..T,
      suzukiChebyshevLaplaceBoundaryHeatXiLogNormBoundaryIntegrand
        x tau (-r) y) -
      (∫ y : ℝ in -T..T,
        suzukiChebyshevLaplaceBoundaryHeatXiLogNormBoundaryIntegrand
          x tau (-l) y) +
      (∫ p : ℂ in ([[-r, -l]] ×ℂ [[-T, T]]),
        suzukiChebyshevLaplaceBoundaryHeatXiLogNormGradientIntegrand
          x tau p.re p.im)
  rw [hright, hleft, hbulk]
  ring

/-- The positive-half-strip representation retains the unnormalized limit to
`2 * pi` times the complete nonnegative detector. -/
theorem tendsto_separatedSelectedLaplaceXiLogNormPositiveHalfStripGradientScalarHeat
    (x : ℝ) {tau : ℝ} (htau : 0 < tau) :
    Tendsto
      (separatedSelectedLaplaceXiLogNormPositiveHalfStripGradientScalarHeat
        x tau) atTop
      (𝓝 (2 * Real.pi *
        riemannXiUpperHyperbolicBoundaryHeatTotal x tau)) := by
  have hlimit :=
    tendsto_separatedSelectedLaplaceXiLogNormGradientScalarHeat x htau
  apply hlimit.congr'
  exact Eventually.of_forall fun n =>
    separatedSelectedLaplaceXiLogNormGradientScalarHeat_eq_positiveHalfStrip
      x tau n

end

end RiemannGaussian
