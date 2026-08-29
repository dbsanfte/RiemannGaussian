import RiemannGaussian.RiemannXiSuzukiPointwiseChebyshevLogAverageLaplaceBoundaryHeatSelectedHalfStripRegularCorrection

/-!
# Exact xi-logarithmic-derivative form of the selected heat frontier

After removing the holomorphic regular correction, this module identifies the
remaining contour functional with literal integrals formed from
`logDeriv riemannXi`.  The chosen near-critical and near-`Re p = -1 / 2`
vertical lines are first proved to lie in the zero-free pole-cleared domain.
This supplies the interval integrability required to split both vertical
integrals.  Genuine planar integrability through the finite xi divisor and a
set-integral argument supply the corresponding bulk split.

The resulting theorem is an exact finite-stage equality, not merely a naming
convention: the regular-subtracted functional is the two explicit xi
logarithmic-derivative vertical sides minus the explicit xi source bulk.  This
three-term functional retains the complete unnormalized detector limit.
-/

namespace RiemannGaussian

noncomputable section

open Complex Filter MeasureTheory Set
open scoped Interval Topology

/-- The degenerate rectangle supported on the selected near-critical vertical
line lies entirely in the zero-free pole-cleared domain. -/
theorem separatedSelectedLaplaceRightVerticalRectangle_subset_poleClearedDomain
    (n : ℕ) :
    [[selectedLaplaceSeparatedRightBoundary n,
        selectedLaplaceSeparatedRightBoundary n]] ×ℂ
        [[-quantitativeSpectralBoundaryTruncation n,
          quantitativeSpectralBoundaryTruncation n]] ⊆
      suzukiChebyshevLogAverageLaplacePoleClearedDomain := by
  let r : ℝ := selectedLaplaceSeparatedRightBoundary n
  let T : ℝ := quantitativeSpectralBoundaryTruncation n
  have hT0 : 0 ≤ T := quantitativeSpectralBoundaryTruncation_nonneg n
  intro z hz
  rw [uIcc_of_le le_rfl, uIcc_of_le (by linarith : -T ≤ T)] at hz
  have hzre : z.re = r := le_antisymm hz.1.2 hz.1.1
  have hzim : |z.im| ≤ T := abs_le.mpr hz.2
  constructor
  · change 0 < (z + 1 / 2).re
    rw [Complex.add_re, hzre]
    norm_num
    have hr := (selectedLaplaceSeparatedRightBoundary_spec n).1
    have hw := selectedLaplaceEdgeWidth_le_quarter n
    dsimp [r] at hr ⊢
    linarith
  · intro hzero
    have hmem : z ∈ suzukiChebyshevLaplaceZeroWindow T :=
      (mem_suzukiChebyshevLaplaceZeroWindow_iff hT0 z).mpr
        ⟨hzero, hzim⟩
    rcases Finset.mem_image.mp hmem with ⟨rho, hrho, hcoord⟩
    have hre := congrArg Complex.re hcoord
    apply selectedLaplaceSeparatedRightBoundary_ne_coordinate_of_mem n
      (by simpa [T] using hrho)
    exact hzre.symm.trans hre.symm

/-- The degenerate rectangle supported on the selected near-`-1 / 2` vertical
line lies entirely in the zero-free pole-cleared domain. -/
theorem separatedSelectedLaplaceLeftVerticalRectangle_subset_poleClearedDomain
    (n : ℕ) :
    [[selectedLaplaceSeparatedLeftBoundary n,
        selectedLaplaceSeparatedLeftBoundary n]] ×ℂ
        [[-quantitativeSpectralBoundaryTruncation n,
          quantitativeSpectralBoundaryTruncation n]] ⊆
      suzukiChebyshevLogAverageLaplacePoleClearedDomain := by
  let l : ℝ := selectedLaplaceSeparatedLeftBoundary n
  let T : ℝ := quantitativeSpectralBoundaryTruncation n
  have hT0 : 0 ≤ T := quantitativeSpectralBoundaryTruncation_nonneg n
  intro z hz
  rw [uIcc_of_le le_rfl, uIcc_of_le (by linarith : -T ≤ T)] at hz
  have hzre : z.re = l := le_antisymm hz.1.2 hz.1.1
  have hzim : |z.im| ≤ T := abs_le.mpr hz.2
  constructor
  · change 0 < (z + 1 / 2).re
    rw [Complex.add_re, hzre]
    norm_num
    dsimp [l]
    linarith [(selectedLaplaceSeparatedLeftBoundary_spec n).1]
  · intro hzero
    have hmem : z ∈ suzukiChebyshevLaplaceZeroWindow T :=
      (mem_suzukiChebyshevLaplaceZeroWindow_iff hT0 z).mpr
        ⟨hzero, hzim⟩
    rcases Finset.mem_image.mp hmem with ⟨rho, hrho, hcoord⟩
    have hre := congrArg Complex.re hcoord
    apply selectedLaplaceSeparatedLeftBoundary_ne_coordinate_of_mem n
      (by simpa [T] using hrho)
    exact hzre.symm.trans hre.symm

/-- The oriented near-critical vertical integral of the heat-weighted genuine
xi logarithmic derivative. -/
def separatedSelectedLaplaceXiLogDerivativeRightBoundaryHeat
    (x tau : ℝ) (n : ℕ) : ℂ :=
  rectangularRightBoundaryIntegral
    (selectedLaplaceSeparatedRightBoundary n)
    (-quantitativeSpectralBoundaryTruncation n)
    (quantitativeSpectralBoundaryTruncation n)
    (suzukiChebyshevLaplaceBoundaryHeatWeightedXiLogDerivative x tau)

/-- The oriented near-`Re p = -1 / 2` vertical integral of the heat-weighted
genuine xi logarithmic derivative. -/
def separatedSelectedLaplaceXiLogDerivativeLeftBoundaryHeat
    (x tau : ℝ) (n : ℕ) : ℂ :=
  rectangularLeftBoundaryIntegral
    (selectedLaplaceSeparatedLeftBoundary n)
    (-quantitativeSpectralBoundaryTruncation n)
    (quantitativeSpectralBoundaryTruncation n)
    (suzukiChebyshevLaplaceBoundaryHeatWeightedXiLogDerivative x tau)

/-- The rectangular Cauchy--Green bulk formed from the heat source times the
genuine xi logarithmic derivative. -/
def separatedSelectedLaplaceXiLogDerivativeBulkHeat
    (x tau : ℝ) (n : ℕ) : ℂ :=
  rectangularAreaIntegral
    (selectedLaplaceSeparatedLeftBoundary n)
    (selectedLaplaceSeparatedRightBoundary n)
    (-quantitativeSpectralBoundaryTruncation n)
    (quantitativeSpectralBoundaryTruncation n)
    (suzukiChebyshevLaplaceBoundaryHeatWeightedXiLogDerivativeSource x tau)

/-- The two explicit xi logarithmic-derivative vertical integrals minus their
explicit xi source bulk. -/
def separatedSelectedLaplaceXiLogDerivativeVerticalSubBulkHeat
    (x tau : ℝ) (n : ℕ) : ℂ :=
  separatedSelectedLaplaceXiLogDerivativeRightBoundaryHeat x tau n +
    separatedSelectedLaplaceXiLogDerivativeLeftBoundaryHeat x tau n -
    separatedSelectedLaplaceXiLogDerivativeBulkHeat x tau n

/-- The full selected right vertical integral splits exactly into its xi
logarithmic-derivative and regular-correction integrals. -/
theorem separatedSelectedLaplaceRightBoundaryHeat_eq_xiLogDerivative_add_regularCorrection
    (x tau : ℝ) (n : ℕ) :
    separatedSelectedLaplaceRightBoundaryHeat x tau n =
      separatedSelectedLaplaceXiLogDerivativeRightBoundaryHeat x tau n +
        separatedSelectedLaplaceRegularCorrectionRightBoundaryHeat
          x tau n := by
  let r : ℝ := selectedLaplaceSeparatedRightBoundary n
  let T : ℝ := quantitativeSpectralBoundaryTruncation n
  have hdomain : [[r, r]] ×ℂ [[-T, T]] ⊆
      suzukiChebyshevLogAverageLaplacePoleClearedDomain := by
    simpa [r, T] using
      separatedSelectedLaplaceRightVerticalRectangle_subset_poleClearedDomain n
  have hfullRect :=
    rectangularBoundaryIntegrable_suzukiChebyshevLaplaceBoundaryHeatWeightedResponse
      x tau r r (-T) T hdomain
  have hfull : IntervalIntegrable
      (fun y : ℝ =>
        suzukiChebyshevLaplaceBoundaryHeatWeightedResponse x tau
          ((r : ℂ) + (y : ℂ) * Complex.I)) volume (-T) T :=
    hfullRect.2.2.1
  have hregularAnalytic : ∀ p ∈ [[r, r]] ×ℂ [[-T, T]],
      AnalyticAt ℂ
        suzukiChebyshevLogAverageLaplaceRegularCorrection p := by
    intro p hp
    have hpDomain := hdomain hp
    apply
      analyticAt_suzukiChebyshevLogAverageLaplaceRegularCorrection_of_re_gt_neg_half
    change 0 < (p + 1 / 2).re ∧ riemannXi (p + 1 / 2) ≠ 0 at hpDomain
    simp at hpDomain
    linarith [hpDomain.1]
  have hregularRect :=
    rectangularBoundaryIntegrable_suzukiChebyshevLaplaceBoundaryHeatWeightedAnalyticRemainder
      x tau r r (-T) T
        suzukiChebyshevLogAverageLaplaceRegularCorrection hregularAnalytic
  have hregular : IntervalIntegrable
      (fun y : ℝ =>
        suzukiChebyshevLaplaceBoundaryHeatWeightedRegularCorrection x tau
          ((r : ℂ) + (y : ℂ) * Complex.I)) volume (-T) T := by
    change IntervalIntegrable
      (fun y : ℝ =>
        suzukiChebyshevLaplaceBoundaryHeatWeightedAnalyticRemainder
          x tau suzukiChebyshevLogAverageLaplaceRegularCorrection
          ((r : ℂ) + (y : ℂ) * Complex.I)) volume (-T) T
    exact hregularRect.2.2.1
  have hxi : IntervalIntegrable
      (fun y : ℝ =>
        suzukiChebyshevLaplaceBoundaryHeatWeightedXiLogDerivative x tau
          ((r : ℂ) + (y : ℂ) * Complex.I)) volume (-T) T := by
    have hsub := hfull.sub hregular
    apply hsub.congr
    intro y hy
    change
      suzukiChebyshevLaplaceBoundaryHeatWeightedResponse x tau
          ((r : ℂ) + (y : ℂ) * Complex.I) -
        suzukiChebyshevLaplaceBoundaryHeatWeightedRegularCorrection x tau
          ((r : ℂ) + (y : ℂ) * Complex.I) =
      suzukiChebyshevLaplaceBoundaryHeatWeightedXiLogDerivative x tau
        ((r : ℂ) + (y : ℂ) * Complex.I)
    rw [suzukiChebyshevLaplaceBoundaryHeatWeightedResponse_eq_xiLogDerivative_add_regularCorrection]
    ring
  have hintegral :
      (∫ y : ℝ in -T..T,
        suzukiChebyshevLaplaceBoundaryHeatWeightedResponse x tau
          ((r : ℂ) + (y : ℂ) * Complex.I)) =
        (∫ y : ℝ in -T..T,
          suzukiChebyshevLaplaceBoundaryHeatWeightedXiLogDerivative x tau
            ((r : ℂ) + (y : ℂ) * Complex.I)) +
        ∫ y : ℝ in -T..T,
          suzukiChebyshevLaplaceBoundaryHeatWeightedRegularCorrection x tau
            ((r : ℂ) + (y : ℂ) * Complex.I) := by
    rw [← intervalIntegral.integral_add hxi hregular]
    apply intervalIntegral.integral_congr
    intro y hy
    exact
      suzukiChebyshevLaplaceBoundaryHeatWeightedResponse_eq_xiLogDerivative_add_regularCorrection
        x tau _
  unfold separatedSelectedLaplaceRightBoundaryHeat
    separatedSelectedLaplaceXiLogDerivativeRightBoundaryHeat
    separatedSelectedLaplaceRegularCorrectionRightBoundaryHeat
    rectangularRightBoundaryIntegral
  simpa only [r, T, mul_add] using
    congrArg (fun q : ℂ => Complex.I * q) hintegral

/-- The full selected left vertical integral splits exactly into its xi
logarithmic-derivative and regular-correction integrals. -/
theorem separatedSelectedLaplaceLeftBoundaryHeat_eq_xiLogDerivative_add_regularCorrection
    (x tau : ℝ) (n : ℕ) :
    separatedSelectedLaplaceLeftBoundaryHeat x tau n =
      separatedSelectedLaplaceXiLogDerivativeLeftBoundaryHeat x tau n +
        separatedSelectedLaplaceRegularCorrectionLeftBoundaryHeat
          x tau n := by
  let l : ℝ := selectedLaplaceSeparatedLeftBoundary n
  let T : ℝ := quantitativeSpectralBoundaryTruncation n
  have hdomain : [[l, l]] ×ℂ [[-T, T]] ⊆
      suzukiChebyshevLogAverageLaplacePoleClearedDomain := by
    simpa [l, T] using
      separatedSelectedLaplaceLeftVerticalRectangle_subset_poleClearedDomain n
  have hfullRect :=
    rectangularBoundaryIntegrable_suzukiChebyshevLaplaceBoundaryHeatWeightedResponse
      x tau l l (-T) T hdomain
  have hfull : IntervalIntegrable
      (fun y : ℝ =>
        suzukiChebyshevLaplaceBoundaryHeatWeightedResponse x tau
          ((l : ℂ) + (y : ℂ) * Complex.I)) volume (-T) T :=
    hfullRect.2.2.1
  have hregularAnalytic : ∀ p ∈ [[l, l]] ×ℂ [[-T, T]],
      AnalyticAt ℂ
        suzukiChebyshevLogAverageLaplaceRegularCorrection p := by
    intro p hp
    have hpDomain := hdomain hp
    apply
      analyticAt_suzukiChebyshevLogAverageLaplaceRegularCorrection_of_re_gt_neg_half
    change 0 < (p + 1 / 2).re ∧ riemannXi (p + 1 / 2) ≠ 0 at hpDomain
    simp at hpDomain
    linarith [hpDomain.1]
  have hregularRect :=
    rectangularBoundaryIntegrable_suzukiChebyshevLaplaceBoundaryHeatWeightedAnalyticRemainder
      x tau l l (-T) T
        suzukiChebyshevLogAverageLaplaceRegularCorrection hregularAnalytic
  have hregular : IntervalIntegrable
      (fun y : ℝ =>
        suzukiChebyshevLaplaceBoundaryHeatWeightedRegularCorrection x tau
          ((l : ℂ) + (y : ℂ) * Complex.I)) volume (-T) T := by
    change IntervalIntegrable
      (fun y : ℝ =>
        suzukiChebyshevLaplaceBoundaryHeatWeightedAnalyticRemainder
          x tau suzukiChebyshevLogAverageLaplaceRegularCorrection
          ((l : ℂ) + (y : ℂ) * Complex.I)) volume (-T) T
    exact hregularRect.2.2.1
  have hxi : IntervalIntegrable
      (fun y : ℝ =>
        suzukiChebyshevLaplaceBoundaryHeatWeightedXiLogDerivative x tau
          ((l : ℂ) + (y : ℂ) * Complex.I)) volume (-T) T := by
    have hsub := hfull.sub hregular
    apply hsub.congr
    intro y hy
    change
      suzukiChebyshevLaplaceBoundaryHeatWeightedResponse x tau
          ((l : ℂ) + (y : ℂ) * Complex.I) -
        suzukiChebyshevLaplaceBoundaryHeatWeightedRegularCorrection x tau
          ((l : ℂ) + (y : ℂ) * Complex.I) =
      suzukiChebyshevLaplaceBoundaryHeatWeightedXiLogDerivative x tau
        ((l : ℂ) + (y : ℂ) * Complex.I)
    rw [suzukiChebyshevLaplaceBoundaryHeatWeightedResponse_eq_xiLogDerivative_add_regularCorrection]
    ring
  have hintegral :
      (∫ y : ℝ in -T..T,
        suzukiChebyshevLaplaceBoundaryHeatWeightedResponse x tau
          ((l : ℂ) + (y : ℂ) * Complex.I)) =
        (∫ y : ℝ in -T..T,
          suzukiChebyshevLaplaceBoundaryHeatWeightedXiLogDerivative x tau
            ((l : ℂ) + (y : ℂ) * Complex.I)) +
        ∫ y : ℝ in -T..T,
          suzukiChebyshevLaplaceBoundaryHeatWeightedRegularCorrection x tau
            ((l : ℂ) + (y : ℂ) * Complex.I) := by
    rw [← intervalIntegral.integral_add hxi hregular]
    apply intervalIntegral.integral_congr
    intro y hy
    exact
      suzukiChebyshevLaplaceBoundaryHeatWeightedResponse_eq_xiLogDerivative_add_regularCorrection
        x tau _
  unfold separatedSelectedLaplaceLeftBoundaryHeat
    separatedSelectedLaplaceXiLogDerivativeLeftBoundaryHeat
    separatedSelectedLaplaceRegularCorrectionLeftBoundaryHeat
    rectangularLeftBoundaryIntegral
  have hscaled := congrArg (fun q : ℂ => -Complex.I * q) hintegral
  simpa only [l, T, mul_add] using hscaled

/-- An iterated rectangular area integral is additive when both summands are
genuinely integrable on the corresponding planar rectangle. -/
theorem rectangularAreaIntegral_add_of_integrableOn
    {l r b u : ℝ} {f g : ℂ → ℂ}
    (hlr : l ≤ r) (hbu : b ≤ u)
    (hf : IntegrableOn f ([[l, r]] ×ℂ [[b, u]]) volume)
    (hg : IntegrableOn g ([[l, r]] ×ℂ [[b, u]]) volume) :
    rectangularAreaIntegral l r b u (fun p => f p + g p) =
      rectangularAreaIntegral l r b u f +
        rectangularAreaIntegral l r b u g := by
  change rectangularAreaIntegral l r b u (f + g) =
    rectangularAreaIntegral l r b u f +
      rectangularAreaIntegral l r b u g
  rw [rectangularAreaIntegral_eq_setIntegral hlr hbu _ (hf.add hg),
    rectangularAreaIntegral_eq_setIntegral hlr hbu _ hf,
    rectangularAreaIntegral_eq_setIntegral hlr hbu _ hg]
  simpa only [Pi.add_apply] using integral_add hf hg

/-- The actual selected Cauchy--Green bulk splits exactly into its xi
logarithmic-derivative and regular-correction bulks. -/
theorem separatedSelectedLaplaceBoundaryHeatBulk_eq_xiLogDerivative_add_regularCorrection
    (x tau : ℝ) (n : ℕ) :
    separatedSelectedLaplaceBoundaryHeatBulk x tau n =
      separatedSelectedLaplaceXiLogDerivativeBulkHeat x tau n +
        separatedSelectedLaplaceRegularCorrectionBulkHeat x tau n := by
  let l : ℝ := selectedLaplaceSeparatedLeftBoundary n
  let r : ℝ := selectedLaplaceSeparatedRightBoundary n
  let T : ℝ := quantitativeSpectralBoundaryTruncation n
  let R : Set ℂ := [[l, r]] ×ℂ [[-T, T]]
  have hT0 : 0 ≤ T := quantitativeSpectralBoundaryTruncation_nonneg n
  have hlr : l ≤ r :=
    (selectedLaplaceSeparatedLeftBoundary_lt_rightBoundary n).le
  have hbu : -T ≤ T := by linarith
  have hrectangle : R ⊆ suzukiChebyshevLaplaceFiniteSlab T := by
    simpa [R, l, r, T] using
      separatedSelectedLaplaceRectangle_subset_finiteSlab n
  have hfull : IntegrableOn
      (suzukiChebyshevLaplaceBoundaryHeatWeightedResponseSource x tau)
      R volume := by
    simpa [R] using
      integrableOn_suzukiChebyshevLaplaceBoundaryHeatWeightedResponseSource_finiteRectangle
        x tau l r (-T) T hT0 hrectangle
  have hregularAnalytic : ∀ p ∈ R,
      AnalyticAt ℂ
        suzukiChebyshevLogAverageLaplaceRegularCorrection p := by
    intro p hp
    apply
      analyticAt_suzukiChebyshevLogAverageLaplaceRegularCorrection_of_re_gt_neg_half
    dsimp only [R] at hp
    rw [uIcc_of_le hlr, uIcc_of_le hbu] at hp
    exact (selectedLaplaceSeparatedLeftBoundary_spec n).1.trans_le hp.1.1
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
  have hadd : rectangularAreaIntegral l r (-T) T
      (fun p =>
        suzukiChebyshevLaplaceBoundaryHeatWeightedXiLogDerivativeSource
            x tau p +
          suzukiChebyshevLaplaceBoundaryHeatWeightedRegularCorrectionSource
            x tau p) =
      rectangularAreaIntegral l r (-T) T
          (suzukiChebyshevLaplaceBoundaryHeatWeightedXiLogDerivativeSource
            x tau) +
        rectangularAreaIntegral l r (-T) T
          (suzukiChebyshevLaplaceBoundaryHeatWeightedRegularCorrectionSource
            x tau) := by
    exact rectangularAreaIntegral_add_of_integrableOn hlr hbu hxi hregular
  have hfullEq : rectangularAreaIntegral l r (-T) T
      (suzukiChebyshevLaplaceBoundaryHeatWeightedResponseSource x tau) =
    rectangularAreaIntegral l r (-T) T
      (fun p =>
        suzukiChebyshevLaplaceBoundaryHeatWeightedXiLogDerivativeSource
            x tau p +
          suzukiChebyshevLaplaceBoundaryHeatWeightedRegularCorrectionSource
            x tau p) := by
    unfold rectangularAreaIntegral
    apply intervalIntegral.integral_congr
    intro a ha
    apply intervalIntegral.integral_congr
    intro y hy
    exact
      suzukiChebyshevLaplaceBoundaryHeatWeightedResponseSource_eq_xiLogDerivative_add_regularCorrection
        x tau _
  unfold separatedSelectedLaplaceBoundaryHeatBulk
    separatedSelectedLaplaceXiLogDerivativeBulkHeat
    separatedSelectedLaplaceRegularCorrectionBulkHeat
  simpa only [l, r, T] using hfullEq.trans hadd

/-- At every finite stage, subtracting the regular-correction
vertical-minus-bulk term leaves exactly the explicit xi-logarithmic-derivative
vertical-minus-bulk functional. -/
theorem separatedSelectedLaplaceVerticalSubBulkHeatSubRegularCorrection_eq_xiLogDerivative
    (x tau : ℝ) (n : ℕ) :
    separatedSelectedLaplaceVerticalSubBulkHeatSubRegularCorrection
        x tau n =
      separatedSelectedLaplaceXiLogDerivativeVerticalSubBulkHeat
        x tau n := by
  unfold separatedSelectedLaplaceVerticalSubBulkHeatSubRegularCorrection
    separatedSelectedLaplaceVerticalSubBulkHeat
    separatedSelectedLaplaceRegularCorrectionVerticalSubBulkHeat
    separatedSelectedLaplaceXiLogDerivativeVerticalSubBulkHeat
  rw [separatedSelectedLaplaceRightBoundaryHeat_eq_xiLogDerivative_add_regularCorrection,
    separatedSelectedLaplaceLeftBoundaryHeat_eq_xiLogDerivative_add_regularCorrection,
    separatedSelectedLaplaceBoundaryHeatBulk_eq_xiLogDerivative_add_regularCorrection]
  ring

/-- The explicit xi-logarithmic-derivative vertical-minus-bulk functional
converges without normalization to `2*pi*I` times the complete detector. -/
theorem tendsto_separatedSelectedLaplaceXiLogDerivativeVerticalSubBulkHeat
    (x : ℝ) {tau : ℝ} (htau : 0 < tau) :
    Tendsto
      (separatedSelectedLaplaceXiLogDerivativeVerticalSubBulkHeat x tau)
      atTop
      (𝓝 ((2 * Real.pi * Complex.I) *
        (riemannXiUpperHyperbolicBoundaryHeatTotal x tau : ℂ))) := by
  have hlimit :=
    tendsto_separatedSelectedLaplaceVerticalSubBulkHeat_sub_regularCorrection
      x htau
  apply hlimit.congr'
  exact Eventually.of_forall fun n =>
    separatedSelectedLaplaceVerticalSubBulkHeatSubRegularCorrection_eq_xiLogDerivative
      x tau n

/-- The imaginary part of the explicit xi-logarithmic-derivative three-term
functional converges to `2*pi` times the complete nonnegative detector. -/
theorem tendsto_separatedSelectedLaplaceXiLogDerivativeVerticalSubBulkHeat_im
    (x : ℝ) {tau : ℝ} (htau : 0 < tau) :
    Tendsto
      (fun n : ℕ =>
        (separatedSelectedLaplaceXiLogDerivativeVerticalSubBulkHeat
          x tau n).im)
      atTop
      (𝓝 (2 * Real.pi *
        riemannXiUpperHyperbolicBoundaryHeatTotal x tau)) := by
  have hlimit :=
    tendsto_separatedSelectedLaplaceXiLogDerivativeVerticalSubBulkHeat x htau
  have him := Complex.continuous_im.continuousAt.tendsto.comp hlimit
  convert him using 1
  · rfl
  · norm_num

end

end RiemannGaussian
