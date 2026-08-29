import RiemannGaussian.RiemannXiSuzukiPointwiseChebyshevLogAverageLaplaceBoundaryHeatSelectedHalfStripHorizontal

/-!
# Remove the holomorphic regular correction from the selected heat frontier

The pole-cleared arithmetic response is the sum of the genuine xi logarithmic
derivative and an explicit Archimedean regular correction.  This module proves
that the latter is asymptotically inert in the selected near-edge contour.

Pointwise, both the weighted response and its Cauchy--Green source split into
xi-logarithmic-derivative and regular-correction pieces.  Because the regular
correction is holomorphic throughout the selected strip, its complete
boundary equals its bulk at every finite stage.  Its horizontal sides vanish
under the fixed-time Gaussian, so its vertical-minus-bulk contribution tends
to zero.  Subtracting it therefore leaves the detector limit unchanged.
-/

namespace RiemannGaussian

noncomputable section

open Complex Filter MeasureTheory Set
open scoped Interval Topology

/-- The boundary heat kernel multiplied by the explicit holomorphic regular
correction. -/
def suzukiChebyshevLaplaceBoundaryHeatWeightedRegularCorrection
    (x tau : ℝ) (p : ℂ) : ℂ :=
  suzukiChebyshevLaplaceBoundaryHeatKernel x tau p *
    suzukiChebyshevLogAverageLaplaceRegularCorrection p

/-- The Cauchy--Green heat source multiplied by the regular correction. -/
def suzukiChebyshevLaplaceBoundaryHeatWeightedRegularCorrectionSource
    (x tau : ℝ) (p : ℂ) : ℂ :=
  suzukiChebyshevLaplaceBoundaryHeatCauchyGreenSource x tau p *
    suzukiChebyshevLogAverageLaplaceRegularCorrection p

/-- The boundary heat kernel multiplied by the genuine completed-xi
logarithmic derivative in the shifted coordinate. -/
def suzukiChebyshevLaplaceBoundaryHeatWeightedXiLogDerivative
    (x tau : ℝ) (p : ℂ) : ℂ :=
  suzukiChebyshevLaplaceBoundaryHeatKernel x tau p *
    logDeriv riemannXi (p + 1 / 2)

/-- The Cauchy--Green heat source multiplied by the genuine completed-xi
logarithmic derivative. -/
def suzukiChebyshevLaplaceBoundaryHeatWeightedXiLogDerivativeSource
    (x tau : ℝ) (p : ℂ) : ℂ :=
  suzukiChebyshevLaplaceBoundaryHeatCauchyGreenSource x tau p *
    logDeriv riemannXi (p + 1 / 2)

/-- Pointwise, the full weighted pole-cleared response is its xi logarithmic
derivative piece plus its regular-correction piece. -/
theorem suzukiChebyshevLaplaceBoundaryHeatWeightedResponse_eq_xiLogDerivative_add_regularCorrection
    (x tau : ℝ) (p : ℂ) :
    suzukiChebyshevLaplaceBoundaryHeatWeightedResponse x tau p =
      suzukiChebyshevLaplaceBoundaryHeatWeightedXiLogDerivative x tau p +
        suzukiChebyshevLaplaceBoundaryHeatWeightedRegularCorrection
          x tau p := by
  unfold suzukiChebyshevLaplaceBoundaryHeatWeightedResponse
    suzukiChebyshevLogAverageLaplacePoleClearedContinuation
    suzukiChebyshevLaplaceBoundaryHeatWeightedXiLogDerivative
    suzukiChebyshevLaplaceBoundaryHeatWeightedRegularCorrection
  ring

/-- Pointwise, the full arithmetic Cauchy--Green source is its xi logarithmic
derivative source plus its regular-correction source. -/
theorem suzukiChebyshevLaplaceBoundaryHeatWeightedResponseSource_eq_xiLogDerivative_add_regularCorrection
    (x tau : ℝ) (p : ℂ) :
    suzukiChebyshevLaplaceBoundaryHeatWeightedResponseSource x tau p =
      suzukiChebyshevLaplaceBoundaryHeatWeightedXiLogDerivativeSource
          x tau p +
        suzukiChebyshevLaplaceBoundaryHeatWeightedRegularCorrectionSource
          x tau p := by
  unfold suzukiChebyshevLaplaceBoundaryHeatWeightedResponseSource
    suzukiChebyshevLogAverageLaplacePoleClearedContinuation
    suzukiChebyshevLaplaceBoundaryHeatWeightedXiLogDerivativeSource
    suzukiChebyshevLaplaceBoundaryHeatWeightedRegularCorrectionSource
  ring

/-- The regular correction is analytic everywhere to the right of the left
edge `Re p = -1 / 2`. -/
theorem analyticAt_suzukiChebyshevLogAverageLaplaceRegularCorrection_of_re_gt_neg_half
    {p : ℂ} (hp : -(1 / 2 : ℝ) < p.re) :
    AnalyticAt ℂ suzukiChebyshevLogAverageLaplaceRegularCorrection p := by
  exact
    analyticOnNhd_suzukiChebyshevLogAverageLaplaceRegularCorrection p (by
      change 0 < (p + 1 / 2).re
      simp
      linarith)

/-- At every selected finite stage, ordinary Cauchy--Green makes the complete
regular-correction boundary exactly equal to its bulk. -/
theorem separatedSelectedLaplaceRegularCorrection_boundary_eq_bulk
    (x tau : ℝ) (n : ℕ) :
    rectangularBoundaryIntegral
        (selectedLaplaceSeparatedLeftBoundary n)
        (selectedLaplaceSeparatedRightBoundary n)
        (-quantitativeSpectralBoundaryTruncation n)
        (quantitativeSpectralBoundaryTruncation n)
        (suzukiChebyshevLaplaceBoundaryHeatWeightedRegularCorrection
          x tau) =
      rectangularAreaIntegral
        (selectedLaplaceSeparatedLeftBoundary n)
        (selectedLaplaceSeparatedRightBoundary n)
        (-quantitativeSpectralBoundaryTruncation n)
        (quantitativeSpectralBoundaryTruncation n)
        (suzukiChebyshevLaplaceBoundaryHeatWeightedRegularCorrectionSource
          x tau) := by
  let l : ℝ := selectedLaplaceSeparatedLeftBoundary n
  let r : ℝ := selectedLaplaceSeparatedRightBoundary n
  let T : ℝ := quantitativeSpectralBoundaryTruncation n
  have hlr : l ≤ r :=
    (selectedLaplaceSeparatedLeftBoundary_lt_rightBoundary n).le
  have hT : 0 ≤ T := quantitativeSpectralBoundaryTruncation_nonneg n
  have hanalytic : ∀ p ∈ [[l, r]] ×ℂ [[-T, T]],
      AnalyticAt ℂ suzukiChebyshevLogAverageLaplaceRegularCorrection p := by
    intro p hp
    rw [uIcc_of_le hlr, uIcc_of_le (by linarith : -T ≤ T)] at hp
    apply
      analyticAt_suzukiChebyshevLogAverageLaplaceRegularCorrection_of_re_gt_neg_half
    exact (selectedLaplaceSeparatedLeftBoundary_spec n).1.trans_le hp.1.1
  change rectangularBoundaryIntegral l r (-T) T
      (suzukiChebyshevLaplaceBoundaryHeatWeightedAnalyticRemainder
        x tau suzukiChebyshevLogAverageLaplaceRegularCorrection) =
    rectangularAreaIntegral l r (-T) T
      (suzukiChebyshevLaplaceBoundaryHeatWeightedAnalyticRemainderSource
        x tau suzukiChebyshevLogAverageLaplaceRegularCorrection)
  exact
    suzukiChebyshevLaplaceBoundaryHeatWeightedAnalyticRemainder_rectangularCauchyGreen
      x tau l r (-T) T
        suzukiChebyshevLogAverageLaplaceRegularCorrection hanalytic

/-- The oriented bottom regular-correction heat integral. -/
def separatedSelectedLaplaceRegularCorrectionBottomBoundaryHeat
    (x tau : ℝ) (n : ℕ) : ℂ :=
  rectangularBottomBoundaryIntegral
    (selectedLaplaceSeparatedLeftBoundary n)
    (selectedLaplaceSeparatedRightBoundary n)
    (-quantitativeSpectralBoundaryTruncation n)
    (suzukiChebyshevLaplaceBoundaryHeatWeightedRegularCorrection x tau)

/-- The oriented top regular-correction heat integral. -/
def separatedSelectedLaplaceRegularCorrectionTopBoundaryHeat
    (x tau : ℝ) (n : ℕ) : ℂ :=
  rectangularTopBoundaryIntegral
    (selectedLaplaceSeparatedLeftBoundary n)
    (selectedLaplaceSeparatedRightBoundary n)
    (quantitativeSpectralBoundaryTruncation n)
    (suzukiChebyshevLaplaceBoundaryHeatWeightedRegularCorrection x tau)

/-- The oriented near-critical regular-correction heat integral. -/
def separatedSelectedLaplaceRegularCorrectionRightBoundaryHeat
    (x tau : ℝ) (n : ℕ) : ℂ :=
  rectangularRightBoundaryIntegral
    (selectedLaplaceSeparatedRightBoundary n)
    (-quantitativeSpectralBoundaryTruncation n)
    (quantitativeSpectralBoundaryTruncation n)
    (suzukiChebyshevLaplaceBoundaryHeatWeightedRegularCorrection x tau)

/-- The oriented near-`Re p = -1 / 2` regular-correction heat integral. -/
def separatedSelectedLaplaceRegularCorrectionLeftBoundaryHeat
    (x tau : ℝ) (n : ℕ) : ℂ :=
  rectangularLeftBoundaryIntegral
    (selectedLaplaceSeparatedLeftBoundary n)
    (-quantitativeSpectralBoundaryTruncation n)
    (quantitativeSpectralBoundaryTruncation n)
    (suzukiChebyshevLaplaceBoundaryHeatWeightedRegularCorrection x tau)

/-- The rectangular regular-correction Cauchy--Green bulk. -/
def separatedSelectedLaplaceRegularCorrectionBulkHeat
    (x tau : ℝ) (n : ℕ) : ℂ :=
  rectangularAreaIntegral
    (selectedLaplaceSeparatedLeftBoundary n)
    (selectedLaplaceSeparatedRightBoundary n)
    (-quantitativeSpectralBoundaryTruncation n)
    (quantitativeSpectralBoundaryTruncation n)
    (suzukiChebyshevLaplaceBoundaryHeatWeightedRegularCorrectionSource
      x tau)

/-- The sum of the bottom and top regular-correction sides. -/
def separatedSelectedLaplaceRegularCorrectionHorizontalBoundaryHeat
    (x tau : ℝ) (n : ℕ) : ℂ :=
  separatedSelectedLaplaceRegularCorrectionBottomBoundaryHeat x tau n +
    separatedSelectedLaplaceRegularCorrectionTopBoundaryHeat x tau n

/-- The two regular-correction vertical sides minus their bulk. -/
def separatedSelectedLaplaceRegularCorrectionVerticalSubBulkHeat
    (x tau : ℝ) (n : ℕ) : ℂ :=
  separatedSelectedLaplaceRegularCorrectionRightBoundaryHeat x tau n +
    separatedSelectedLaplaceRegularCorrectionLeftBoundaryHeat x tau n -
    separatedSelectedLaplaceRegularCorrectionBulkHeat x tau n

/-- The regular-correction horizontal and vertical-minus-bulk pieces sum to
zero exactly at every finite stage. -/
theorem separatedSelectedLaplaceRegularCorrectionHorizontal_add_verticalSubBulk_eq_zero
    (x tau : ℝ) (n : ℕ) :
    separatedSelectedLaplaceRegularCorrectionHorizontalBoundaryHeat
        x tau n +
      separatedSelectedLaplaceRegularCorrectionVerticalSubBulkHeat
        x tau n = 0 := by
  have hcg :=
    separatedSelectedLaplaceRegularCorrection_boundary_eq_bulk x tau n
  rw [rectangularBoundaryIntegral_eq_four_oriented_sides] at hcg
  unfold separatedSelectedLaplaceRegularCorrectionHorizontalBoundaryHeat
    separatedSelectedLaplaceRegularCorrectionVerticalSubBulkHeat
    separatedSelectedLaplaceRegularCorrectionBottomBoundaryHeat
    separatedSelectedLaplaceRegularCorrectionTopBoundaryHeat
    separatedSelectedLaplaceRegularCorrectionRightBoundaryHeat
    separatedSelectedLaplaceRegularCorrectionLeftBoundaryHeat
    separatedSelectedLaplaceRegularCorrectionBulkHeat
  linear_combination hcg

/-- The Gaussian-times-exponential majorant on the top regular-correction
side tends to zero. -/
theorem tendsto_selectedHalfStripTopRegularCorrectionMajorant_zero
    (x : ℝ) {tau : ℝ} (htau : 0 < tau) :
    Tendsto
      (fun n : ℕ =>
        Real.exp (-tau *
            (x - quantitativeSpectralBoundaryTruncation n) ^ 2) *
          (selectedHalfStripRegularCorrectionExponentialConstant *
            Real.exp (4 * quantitativeSpectralBoundaryTruncation n)))
      atTop (𝓝 0) := by
  let C : ℝ := selectedHalfStripRegularCorrectionExponentialConstant
  let M : ℝ → ℝ := fun T =>
    Real.exp (-tau * (x - T) ^ 2) * (C * Real.exp (4 * T))
  have hbase :=
    tendsto_exp_neg_quadratic_add_linear_atTop htau x 4 0
  have hscaled : Tendsto
      (fun T : ℝ => C *
        Real.exp (-tau * (T - x) ^ 2 + 4 * T + 0))
      atTop (𝓝 0) := by
    simpa using hbase.const_mul C
  have hM : Tendsto M atTop (𝓝 0) := by
    apply hscaled.congr'
    filter_upwards with T
    dsimp [M]
    rw [show -tau * (T - x) ^ 2 + 4 * T + 0 =
      -tau * (x - T) ^ 2 + 4 * T by ring,
      Real.exp_add]
    ring
  simpa [M, C, Function.comp_def] using
    hM.comp tendsto_quantitativeSpectralBoundaryTruncation_atTop

/-- The Gaussian-times-exponential majorant on the bottom regular-correction
side tends to zero. -/
theorem tendsto_selectedHalfStripBottomRegularCorrectionMajorant_zero
    (x : ℝ) {tau : ℝ} (htau : 0 < tau) :
    Tendsto
      (fun n : ℕ =>
        Real.exp (-tau *
            (x + quantitativeSpectralBoundaryTruncation n) ^ 2) *
          (selectedHalfStripRegularCorrectionExponentialConstant *
            Real.exp (4 * quantitativeSpectralBoundaryTruncation n)))
      atTop (𝓝 0) := by
  let C : ℝ := selectedHalfStripRegularCorrectionExponentialConstant
  let M : ℝ → ℝ := fun T =>
    Real.exp (-tau * (x + T) ^ 2) * (C * Real.exp (4 * T))
  have hbase :=
    tendsto_exp_neg_quadratic_add_linear_atTop htau (-x) 4 0
  have hscaled : Tendsto
      (fun T : ℝ => C *
        Real.exp (-tau * (T - (-x)) ^ 2 + 4 * T + 0))
      atTop (𝓝 0) := by
    simpa using hbase.const_mul C
  have hM : Tendsto M atTop (𝓝 0) := by
    apply hscaled.congr'
    filter_upwards with T
    dsimp [M]
    rw [show -tau * (T - (-x)) ^ 2 + 4 * T + 0 =
      -tau * (x + T) ^ 2 + 4 * T by ring,
      Real.exp_add]
    ring
  simpa [M, C, Function.comp_def] using
    hM.comp tendsto_quantitativeSpectralBoundaryTruncation_atTop

/-- A pointwise majorant for the heat-weighted regular correction on the top
selected side. -/
theorem norm_suzukiChebyshevLaplaceBoundaryHeatWeightedRegularCorrection_top_le
    (x : ℝ) {tau : ℝ} (htau : 0 < tau)
    (n : ℕ) (hn : 1 ≤ n) {a : ℝ}
    (ha : -(1 / 2 : ℝ) < a) (ha0 : a ≤ 0) :
    ‖suzukiChebyshevLaplaceBoundaryHeatWeightedRegularCorrection x tau
        ((a : ℂ) +
          (quantitativeSpectralBoundaryTruncation n : ℂ) * Complex.I)‖ ≤
      Real.exp (-tau *
          (x - quantitativeSpectralBoundaryTruncation n) ^ 2) *
        (selectedHalfStripRegularCorrectionExponentialConstant *
          Real.exp (4 * quantitativeSpectralBoundaryTruncation n)) := by
  let T : ℝ := quantitativeSpectralBoundaryTruncation n
  have hT : 1 ≤ T := by
    have hncast : (1 : ℝ) ≤ n := by exact_mod_cast hn
    exact hncast.trans (quantitativeSpectralBoundaryTruncation_spec n).1.le
  have hT0 : 0 ≤ T := by linarith
  unfold suzukiChebyshevLaplaceBoundaryHeatWeightedRegularCorrection
  rw [norm_mul]
  exact mul_le_mul
    (norm_suzukiChebyshevLaplaceBoundaryHeatKernel_horizontal_le
      x htau ha.le ha0)
    (by
      simpa only [T] using
        norm_suzukiChebyshevLaplaceRegularCorrection_horizontal_le_exp
          ha ha0 (abs_of_nonneg hT0) hT)
    (norm_nonneg _)
    (Real.exp_pos _).le

/-- A pointwise majorant for the heat-weighted regular correction on the
bottom selected side. -/
theorem norm_suzukiChebyshevLaplaceBoundaryHeatWeightedRegularCorrection_bottom_le
    (x : ℝ) {tau : ℝ} (htau : 0 < tau)
    (n : ℕ) (hn : 1 ≤ n) {a : ℝ}
    (ha : -(1 / 2 : ℝ) < a) (ha0 : a ≤ 0) :
    ‖suzukiChebyshevLaplaceBoundaryHeatWeightedRegularCorrection x tau
        ((a : ℂ) +
          ((-quantitativeSpectralBoundaryTruncation n : ℝ) : ℂ) *
            Complex.I)‖ ≤
      Real.exp (-tau *
          (x + quantitativeSpectralBoundaryTruncation n) ^ 2) *
        (selectedHalfStripRegularCorrectionExponentialConstant *
          Real.exp (4 * quantitativeSpectralBoundaryTruncation n)) := by
  let T : ℝ := quantitativeSpectralBoundaryTruncation n
  have hT : 1 ≤ T := by
    have hncast : (1 : ℝ) ≤ n := by exact_mod_cast hn
    exact hncast.trans (quantitativeSpectralBoundaryTruncation_spec n).1.le
  have hT0 : 0 ≤ T := by linarith
  unfold suzukiChebyshevLaplaceBoundaryHeatWeightedRegularCorrection
  rw [norm_mul]
  exact mul_le_mul
    (by
      have hk :=
        norm_suzukiChebyshevLaplaceBoundaryHeatKernel_horizontal_le
          x (r := -T) htau ha.le ha0
      simpa only [T, sub_neg_eq_add] using hk)
    (by
      simpa only [T] using
        norm_suzukiChebyshevLaplaceRegularCorrection_horizontal_le_exp
          ha ha0
          (show |-T| = T by rw [abs_neg, abs_of_nonneg hT0]) hT
          (r := -T))
    (norm_nonneg _)
    (Real.exp_pos _).le

/-- The top regular-correction integral is bounded by its vanishing Gaussian
majorant. -/
theorem norm_separatedSelectedLaplaceRegularCorrectionTopBoundaryHeat_le_majorant
    (x : ℝ) {tau : ℝ} (htau : 0 < tau)
    (n : ℕ) (hn : 1 ≤ n) :
    ‖separatedSelectedLaplaceRegularCorrectionTopBoundaryHeat x tau n‖ ≤
      Real.exp (-tau *
          (x - quantitativeSpectralBoundaryTruncation n) ^ 2) *
        (selectedHalfStripRegularCorrectionExponentialConstant *
          Real.exp (4 * quantitativeSpectralBoundaryTruncation n)) := by
  let l : ℝ := selectedLaplaceSeparatedLeftBoundary n
  let r : ℝ := selectedLaplaceSeparatedRightBoundary n
  let T : ℝ := quantitativeSpectralBoundaryTruncation n
  let C : ℝ := selectedHalfStripRegularCorrectionExponentialConstant
  let M : ℝ := Real.exp (-tau * (x - T) ^ 2) *
    (C * Real.exp (4 * T))
  have hC0 : 0 ≤ C := by
    dsimp [C]
    exact selectedHalfStripRegularCorrectionExponentialConstant_nonneg
  have hlr : l < r :=
    selectedLaplaceSeparatedLeftBoundary_lt_rightBoundary n
  have hlEdge : -(1 / 2 : ℝ) < l :=
    (selectedLaplaceSeparatedLeftBoundary_spec n).1
  have hrEdge : r < 0 :=
    (selectedLaplaceSeparatedRightBoundary_spec n).2.1
  have hwidth : |r - l| ≤ 1 := by
    rw [abs_of_pos (sub_pos.mpr hlr)]
    linarith
  have hM0 : 0 ≤ M := by
    dsimp [M]
    exact mul_nonneg (Real.exp_pos _).le
      (mul_nonneg hC0 (Real.exp_pos _).le)
  have hIntegral := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := l) (b := r) (C := M)
    (f := fun a : ℝ =>
      suzukiChebyshevLaplaceBoundaryHeatWeightedRegularCorrection x tau
        ((a : ℂ) + (T : ℂ) * Complex.I)) (by
      intro a haInt
      rw [uIoc_of_le hlr.le] at haInt
      have haLeft : -(1 / 2 : ℝ) < a := hlEdge.trans haInt.1
      have haRight : a ≤ 0 := haInt.2.trans hrEdge.le
      simpa only [C, T, M] using
        norm_suzukiChebyshevLaplaceBoundaryHeatWeightedRegularCorrection_top_le
          x htau n hn haLeft haRight)
  unfold separatedSelectedLaplaceRegularCorrectionTopBoundaryHeat
    rectangularTopBoundaryIntegral
  dsimp only [l, r, T, C, M] at hIntegral ⊢
  rw [norm_neg]
  calc
    ‖∫ a : ℝ in
        selectedLaplaceSeparatedLeftBoundary n..
          selectedLaplaceSeparatedRightBoundary n,
        suzukiChebyshevLaplaceBoundaryHeatWeightedRegularCorrection x tau
          ((a : ℂ) +
            (quantitativeSpectralBoundaryTruncation n : ℂ) *
              Complex.I)‖ ≤
        (Real.exp (-tau *
            (x - quantitativeSpectralBoundaryTruncation n) ^ 2) *
          (selectedHalfStripRegularCorrectionExponentialConstant *
            Real.exp (4 * quantitativeSpectralBoundaryTruncation n))) *
          |selectedLaplaceSeparatedRightBoundary n -
            selectedLaplaceSeparatedLeftBoundary n| := hIntegral
    _ ≤ (Real.exp (-tau *
            (x - quantitativeSpectralBoundaryTruncation n) ^ 2) *
          (selectedHalfStripRegularCorrectionExponentialConstant *
            Real.exp (4 * quantitativeSpectralBoundaryTruncation n))) * 1 :=
      mul_le_mul_of_nonneg_left hwidth hM0
    _ = Real.exp (-tau *
          (x - quantitativeSpectralBoundaryTruncation n) ^ 2) *
        (selectedHalfStripRegularCorrectionExponentialConstant *
          Real.exp (4 * quantitativeSpectralBoundaryTruncation n)) := by ring

/-- The bottom regular-correction integral is bounded by its vanishing
Gaussian majorant. -/
theorem norm_separatedSelectedLaplaceRegularCorrectionBottomBoundaryHeat_le_majorant
    (x : ℝ) {tau : ℝ} (htau : 0 < tau)
    (n : ℕ) (hn : 1 ≤ n) :
    ‖separatedSelectedLaplaceRegularCorrectionBottomBoundaryHeat x tau n‖ ≤
      Real.exp (-tau *
          (x + quantitativeSpectralBoundaryTruncation n) ^ 2) *
        (selectedHalfStripRegularCorrectionExponentialConstant *
          Real.exp (4 * quantitativeSpectralBoundaryTruncation n)) := by
  let l : ℝ := selectedLaplaceSeparatedLeftBoundary n
  let r : ℝ := selectedLaplaceSeparatedRightBoundary n
  let T : ℝ := quantitativeSpectralBoundaryTruncation n
  let C : ℝ := selectedHalfStripRegularCorrectionExponentialConstant
  let M : ℝ := Real.exp (-tau * (x + T) ^ 2) *
    (C * Real.exp (4 * T))
  have hC0 : 0 ≤ C := by
    dsimp [C]
    exact selectedHalfStripRegularCorrectionExponentialConstant_nonneg
  have hlr : l < r :=
    selectedLaplaceSeparatedLeftBoundary_lt_rightBoundary n
  have hlEdge : -(1 / 2 : ℝ) < l :=
    (selectedLaplaceSeparatedLeftBoundary_spec n).1
  have hrEdge : r < 0 :=
    (selectedLaplaceSeparatedRightBoundary_spec n).2.1
  have hwidth : |r - l| ≤ 1 := by
    rw [abs_of_pos (sub_pos.mpr hlr)]
    linarith
  have hM0 : 0 ≤ M := by
    dsimp [M]
    exact mul_nonneg (Real.exp_pos _).le
      (mul_nonneg hC0 (Real.exp_pos _).le)
  have hIntegral := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := l) (b := r) (C := M)
    (f := fun a : ℝ =>
      suzukiChebyshevLaplaceBoundaryHeatWeightedRegularCorrection x tau
        ((a : ℂ) + ((-T : ℝ) : ℂ) * Complex.I)) (by
      intro a haInt
      rw [uIoc_of_le hlr.le] at haInt
      have haLeft : -(1 / 2 : ℝ) < a := hlEdge.trans haInt.1
      have haRight : a ≤ 0 := haInt.2.trans hrEdge.le
      simpa only [C, T, M] using
        norm_suzukiChebyshevLaplaceBoundaryHeatWeightedRegularCorrection_bottom_le
          x htau n hn haLeft haRight)
  unfold separatedSelectedLaplaceRegularCorrectionBottomBoundaryHeat
    rectangularBottomBoundaryIntegral
  dsimp only [l, r, T, C, M] at hIntegral ⊢
  calc
    ‖∫ a : ℝ in
        selectedLaplaceSeparatedLeftBoundary n..
          selectedLaplaceSeparatedRightBoundary n,
        suzukiChebyshevLaplaceBoundaryHeatWeightedRegularCorrection x tau
          ((a : ℂ) +
            ((-quantitativeSpectralBoundaryTruncation n : ℝ) : ℂ) *
              Complex.I)‖ ≤
        (Real.exp (-tau *
            (x + quantitativeSpectralBoundaryTruncation n) ^ 2) *
          (selectedHalfStripRegularCorrectionExponentialConstant *
            Real.exp (4 * quantitativeSpectralBoundaryTruncation n))) *
          |selectedLaplaceSeparatedRightBoundary n -
            selectedLaplaceSeparatedLeftBoundary n| := hIntegral
    _ ≤ (Real.exp (-tau *
            (x + quantitativeSpectralBoundaryTruncation n) ^ 2) *
          (selectedHalfStripRegularCorrectionExponentialConstant *
            Real.exp (4 * quantitativeSpectralBoundaryTruncation n))) * 1 :=
      mul_le_mul_of_nonneg_left hwidth hM0
    _ = Real.exp (-tau *
          (x + quantitativeSpectralBoundaryTruncation n) ^ 2) *
        (selectedHalfStripRegularCorrectionExponentialConstant *
          Real.exp (4 * quantitativeSpectralBoundaryTruncation n)) := by ring

/-- The top regular-correction horizontal integral tends to zero. -/
theorem tendsto_separatedSelectedLaplaceRegularCorrectionTopBoundaryHeat_zero
    (x : ℝ) {tau : ℝ} (htau : 0 < tau) :
    Tendsto
      (separatedSelectedLaplaceRegularCorrectionTopBoundaryHeat x tau)
      atTop (𝓝 0) := by
  apply squeeze_zero_norm'
    (show ∀ᶠ n : ℕ in atTop,
      ‖separatedSelectedLaplaceRegularCorrectionTopBoundaryHeat x tau n‖ ≤
        Real.exp (-tau *
            (x - quantitativeSpectralBoundaryTruncation n) ^ 2) *
          (selectedHalfStripRegularCorrectionExponentialConstant *
            Real.exp (4 * quantitativeSpectralBoundaryTruncation n)) by
      filter_upwards [eventually_ge_atTop (1 : ℕ)] with n hn
      exact
        norm_separatedSelectedLaplaceRegularCorrectionTopBoundaryHeat_le_majorant
          x htau n hn)
  exact tendsto_selectedHalfStripTopRegularCorrectionMajorant_zero x htau

/-- The bottom regular-correction horizontal integral tends to zero. -/
theorem tendsto_separatedSelectedLaplaceRegularCorrectionBottomBoundaryHeat_zero
    (x : ℝ) {tau : ℝ} (htau : 0 < tau) :
    Tendsto
      (separatedSelectedLaplaceRegularCorrectionBottomBoundaryHeat x tau)
      atTop (𝓝 0) := by
  apply squeeze_zero_norm'
    (show ∀ᶠ n : ℕ in atTop,
      ‖separatedSelectedLaplaceRegularCorrectionBottomBoundaryHeat x tau n‖ ≤
        Real.exp (-tau *
            (x + quantitativeSpectralBoundaryTruncation n) ^ 2) *
          (selectedHalfStripRegularCorrectionExponentialConstant *
            Real.exp (4 * quantitativeSpectralBoundaryTruncation n)) by
      filter_upwards [eventually_ge_atTop (1 : ℕ)] with n hn
      exact
        norm_separatedSelectedLaplaceRegularCorrectionBottomBoundaryHeat_le_majorant
          x htau n hn)
  exact tendsto_selectedHalfStripBottomRegularCorrectionMajorant_zero x htau

/-- The combined regular-correction horizontal contribution tends to zero. -/
theorem tendsto_separatedSelectedLaplaceRegularCorrectionHorizontalBoundaryHeat_zero
    (x : ℝ) {tau : ℝ} (htau : 0 < tau) :
    Tendsto
      (separatedSelectedLaplaceRegularCorrectionHorizontalBoundaryHeat x tau)
      atTop (𝓝 0) := by
  change Tendsto
    (fun n : ℕ =>
      separatedSelectedLaplaceRegularCorrectionBottomBoundaryHeat x tau n +
        separatedSelectedLaplaceRegularCorrectionTopBoundaryHeat x tau n)
    atTop (𝓝 0)
  simpa using
    (tendsto_separatedSelectedLaplaceRegularCorrectionBottomBoundaryHeat_zero
      x htau).add
      (tendsto_separatedSelectedLaplaceRegularCorrectionTopBoundaryHeat_zero
        x htau)

/-- At each finite stage, the regular-correction vertical-minus-bulk term is
the negative of its horizontal contribution. -/
theorem separatedSelectedLaplaceRegularCorrectionVerticalSubBulkHeat_eq_neg_horizontal
    (x tau : ℝ) (n : ℕ) :
    separatedSelectedLaplaceRegularCorrectionVerticalSubBulkHeat x tau n =
      -separatedSelectedLaplaceRegularCorrectionHorizontalBoundaryHeat
        x tau n := by
  have h :=
    separatedSelectedLaplaceRegularCorrectionHorizontal_add_verticalSubBulk_eq_zero
      x tau n
  linear_combination h

/-- The regular-correction vertical-minus-bulk term tends to zero. -/
theorem tendsto_separatedSelectedLaplaceRegularCorrectionVerticalSubBulkHeat_zero
    (x : ℝ) {tau : ℝ} (htau : 0 < tau) :
    Tendsto
      (separatedSelectedLaplaceRegularCorrectionVerticalSubBulkHeat x tau)
      atTop (𝓝 0) := by
  have h :=
    (tendsto_separatedSelectedLaplaceRegularCorrectionHorizontalBoundaryHeat_zero
      x htau).neg
  simpa only [neg_zero] using
    h.congr' (Eventually.of_forall fun n =>
      (separatedSelectedLaplaceRegularCorrectionVerticalSubBulkHeat_eq_neg_horizontal
        x tau n).symm)

/-- The live vertical-minus-bulk functional after exact subtraction of its
regular-correction component. -/
def separatedSelectedLaplaceVerticalSubBulkHeatSubRegularCorrection
    (x tau : ℝ) (n : ℕ) : ℂ :=
  separatedSelectedLaplaceVerticalSubBulkHeat x tau n -
    separatedSelectedLaplaceRegularCorrectionVerticalSubBulkHeat x tau n

/-- Subtracting the asymptotically inert regular correction leaves the full
unnormalized xi heat-detector limit unchanged. -/
theorem tendsto_separatedSelectedLaplaceVerticalSubBulkHeat_sub_regularCorrection
    (x : ℝ) {tau : ℝ} (htau : 0 < tau) :
    Tendsto
      (separatedSelectedLaplaceVerticalSubBulkHeatSubRegularCorrection x tau)
      atTop
      (𝓝 ((2 * Real.pi * Complex.I) *
        (riemannXiUpperHyperbolicBoundaryHeatTotal x tau : ℂ))) := by
  change Tendsto
    (fun n : ℕ =>
      separatedSelectedLaplaceVerticalSubBulkHeat x tau n -
        separatedSelectedLaplaceRegularCorrectionVerticalSubBulkHeat
          x tau n)
    atTop
    (𝓝 ((2 * Real.pi * Complex.I) *
      (riemannXiUpperHyperbolicBoundaryHeatTotal x tau : ℂ)))
  simpa only [sub_zero] using
    (tendsto_separatedSelectedLaplaceVerticalSubBulkHeat x htau).sub
      (tendsto_separatedSelectedLaplaceRegularCorrectionVerticalSubBulkHeat_zero
        x htau)

/-- The imaginary part after regular-correction subtraction still converges
to `2*pi` times the complete nonnegative xi heat detector. -/
theorem tendsto_separatedSelectedLaplaceVerticalSubBulkHeat_sub_regularCorrection_im
    (x : ℝ) {tau : ℝ} (htau : 0 < tau) :
    Tendsto
      (fun n : ℕ =>
        (separatedSelectedLaplaceVerticalSubBulkHeatSubRegularCorrection
          x tau n).im)
      atTop
      (𝓝 (2 * Real.pi *
        riemannXiUpperHyperbolicBoundaryHeatTotal x tau)) := by
  have hlimit :=
    tendsto_separatedSelectedLaplaceVerticalSubBulkHeat_sub_regularCorrection
      x htau
  have him := Complex.continuous_im.continuousAt.tendsto.comp hlimit
  convert him using 1
  · rfl
  · norm_num

end

end RiemannGaussian
