import RiemannGaussian.RiemannXiSuzukiUpperHalfPlane
import Mathlib.Topology.Algebra.InfiniteSum.TsumUniformlyOn

/-!
# Holomorphy of Suzuki's infinite spectral series

The preceding pointwise construction of Suzuki's spectral `P_t(z)` is
upgraded here to a normally convergent holomorphic series on the safe domain
`Im z > 1/2`.  On every compact subset of that domain, continuity bounds the
upper-evaluation comparison constant.  The arithmetic--geometric mean
inequality then combines the square bounds for the evaluation and coefficient
features into one summable inverse-square majorant.

Consequently:

* the zero summands are summable locally uniformly;
* genuine symmetric spectral windows converge locally uniformly to `P_t`;
* the infinite `P_t` is holomorphic throughout the safe half-plane; and
* spatial differentiation passes through the complete zero series.

This is the analytic spectral side of Suzuki's formula.  It does not identify
the resulting function with the arithmetic prime/gamma expression, continue
it to the real-axis `L²` class, or assert off-RH control of the zero-function
Gram operator.  Those remain separate theorems to be proved.
-/

open Complex Filter MeasureTheory Metric Polynomial Set Topology
open scoped Classical ENNReal Interval Topology lp

namespace RiemannGaussian

noncomputable section

/-- The open half-plane strictly above the complete spectral-xi zero strip. -/
def suzukiXiSafeUpperHalfPlane : Set ℂ :=
  {z | (1 / 2 : ℝ) < z.im}

/-- Suzuki's safe upper half-plane is open. -/
theorem isOpen_suzukiXiSafeUpperHalfPlane :
    IsOpen suzukiXiSafeUpperHalfPlane := by
  exact Complex.isOpen_im_gt (1 / 2)

/-- The explicit evaluation comparison constant varies continuously throughout
the safe half-plane. -/
theorem continuousOn_suzukiXiUpperEvaluationConstant :
    ContinuousOn suzukiXiUpperEvaluationConstant
      suzukiXiSafeUpperHalfPlane := by
  intro z hz
  apply ContinuousAt.continuousWithinAt
  unfold suzukiXiUpperEvaluationConstant suzukiXiUpperEvaluationGap
  apply ContinuousAt.div
  · fun_prop
  · fun_prop
  · have hgap : 0 < z.im - 1 / 2 := by
      change (1 / 2 : ℝ) < z.im at hz
      linarith
    positivity

/-- Each individual spectral `P_t` summand is holomorphic on the safe upper
half-plane. -/
theorem differentiableOn_zetaSuzukiSpectralPSummand
    (t : ℝ) (rho : NontrivialZetaZero) :
    DifferentiableOn ℂ
      (fun z ↦ zetaSuzukiSpectralPSummand t z rho)
      suzukiXiSafeUpperHalfPlane := by
  intro z hz
  apply DifferentiableAt.differentiableWithinAt
  have hden : suzukiXiUpperEvaluationDenominator z
      (zetaSpectralCoordinate rho.1) ≠ 0 := by
    exact Complex.normSq_pos.mp
      (normSq_suzukiXiUpperEvaluationDenominator_pos hz rho)
  unfold zetaSuzukiSpectralPSummand
    suzukiXiUpperEvaluationDenominator
  apply DifferentiableAt.div
  · fun_prop
  · fun_prop
  · simpa [suzukiXiUpperEvaluationDenominator] using hden

/-- Arithmetic--geometric mean combines the two Hilbert-coordinate square
bounds into a direct inverse-square majorant for one `P_t` summand. -/
theorem norm_zetaSuzukiSpectralPSummand_le_inverseSquare_average
    (t : ℝ) {z : ℂ} (hz : z ∈ suzukiXiSafeUpperHalfPlane)
    (rho : NontrivialZetaZero) :
    ‖zetaSuzukiSpectralPSummand t z rho‖ ≤
      ((suzukiSpectralCoefficientInverseSquareConstant t +
          suzukiXiUpperEvaluationConstant z) / 2) *
        ((analyticZetaZeroMultiplicity rho : ℝ) /
          (1 + (zetaSpectralCoordinate rho.1).re ^ 2)) := by
  let a : ℝ := ‖zetaSuzukiUpperEvaluationFeature z rho‖
  let b : ℝ := ‖zetaSuzukiSpectralCoefficientFeature t rho‖
  let w : ℝ := (analyticZetaZeroMultiplicity rho : ℝ) /
    (1 + (zetaSpectralCoordinate rho.1).re ^ 2)
  let C : ℝ := suzukiXiUpperEvaluationConstant z
  let D : ℝ := suzukiSpectralCoefficientInverseSquareConstant t
  have ha0 : 0 ≤ a := norm_nonneg _
  have hb0 : 0 ≤ b := norm_nonneg _
  have hw0 : 0 ≤ w := by
    dsimp [w]
    positivity
  have ha : a ^ 2 ≤ C * w := by
    dsimp [a, C, w]
    rw [Complex.sq_norm, normSq_zetaSuzukiUpperEvaluationFeature]
    exact zetaSuzukiUpperEvaluationEnergy_le_inverseSquare hz rho
  have hb : b ^ 2 ≤ D * w := by
    dsimp [b, D, w]
    rw [Complex.sq_norm, normSq_zetaSuzukiSpectralCoefficientFeature]
    exact zetaSuzukiSpectralCoefficientEnergy_le_inverseSquare t rho
  have hterm : ‖zetaSuzukiSpectralPSummand t z rho‖ ≤ a * b := by
    rw [zetaSuzukiSpectralPSummand_eq_inner]
    exact norm_inner_le_norm _ _
  have hcross : 2 * a * b ≤ a ^ 2 + b ^ 2 := by
    nlinarith [sq_nonneg (a - b)]
  have hsum : a ^ 2 + b ^ 2 ≤ (C + D) * w := by
    calc
      a ^ 2 + b ^ 2 ≤ C * w + D * w := add_le_add ha hb
      _ = (C + D) * w := by ring
  change ‖zetaSuzukiSpectralPSummand t z rho‖ ≤ ((D + C) / 2) * w
  calc
    ‖zetaSuzukiSpectralPSummand t z rho‖ ≤ a * b := hterm
    _ ≤ ((D + C) / 2) * w := by nlinarith

/-- The full spectral `P_t` family is summable locally uniformly on Suzuki's
safe upper half-plane. -/
theorem summableLocallyUniformlyOn_zetaSuzukiSpectralPSummand (t : ℝ) :
    SummableLocallyUniformlyOn
      (fun rho : NontrivialZetaZero ↦
        fun z : ℂ ↦ zetaSuzukiSpectralPSummand t z rho)
      suzukiXiSafeUpperHalfPlane := by
  apply SummableLocallyUniformlyOn_of_locally_bounded
    isOpen_suzukiXiSafeUpperHalfPlane
  intro K hKsafe hK
  have hcontinuous : ContinuousOn suzukiXiUpperEvaluationConstant K :=
    continuousOn_suzukiXiUpperEvaluationConstant.mono hKsafe
  obtain ⟨C, hC⟩ :=
    bddAbove_def.mp (hK.bddAbove_image hcontinuous)
  let C' : ℝ := max C 0
  let M : ℝ :=
    (suzukiSpectralCoefficientInverseSquareConstant t + C') / 2
  let u : NontrivialZetaZero → ℝ := fun rho ↦
    M * ((analyticZetaZeroMultiplicity rho : ℝ) /
      (1 + (zetaSpectralCoordinate rho.1).re ^ 2))
  refine ⟨u, ?_, ?_⟩
  · exact summable_distinct_zetaZeroInverseSquareSpectralRe.mul_left M
  · intro rho z hzK
    have hz : z ∈ suzukiXiSafeUpperHalfPlane := hKsafe hzK
    have hconstant : suzukiXiUpperEvaluationConstant z ≤ C' := by
      apply (hC (suzukiXiUpperEvaluationConstant z) ?_).trans
        (le_max_left C 0)
      exact ⟨z, hzK, rfl⟩
    have hweight : 0 ≤
        (analyticZetaZeroMultiplicity rho : ℝ) /
          (1 + (zetaSpectralCoordinate rho.1).re ^ 2) := by
      positivity
    refine
      (norm_zetaSuzukiSpectralPSummand_le_inverseSquare_average
        t hz rho).trans ?_
    dsimp [u, M]
    apply mul_le_mul_of_nonneg_right _ hweight
    linarith

/-- The locally uniform sum is exactly the previously defined infinite
spectral `P_t`. -/
theorem hasSumLocallyUniformlyOn_zetaSuzukiSpectralPSummand (t : ℝ) :
    HasSumLocallyUniformlyOn
      (fun rho : NontrivialZetaZero ↦
        fun z : ℂ ↦ zetaSuzukiSpectralPSummand t z rho)
      (riemannXiSuzukiSpectralP t) suzukiXiSafeUpperHalfPlane := by
  change HasSumLocallyUniformlyOn
    (fun rho : NontrivialZetaZero ↦
      fun z : ℂ ↦ zetaSuzukiSpectralPSummand t z rho)
    (fun z : ℂ ↦ ∑' rho : NontrivialZetaZero,
      zetaSuzukiSpectralPSummand t z rho)
    suzukiXiSafeUpperHalfPlane
  exact
    (summableLocallyUniformlyOn_zetaSuzukiSpectralPSummand t).hasSumLocallyUniformlyOn

/-- Genuine symmetric spectral windows converge locally uniformly, not merely
pointwise, to the complete spectral `P_t` on the safe half-plane. -/
theorem tendstoLocallyUniformlyOn_suzukiXiSpectralPWindow (t : ℝ) :
    TendstoLocallyUniformlyOn
      (fun T : ℝ ↦ suzukiXiSpectralPWindow t T)
      (riemannXiSuzukiSpectralP t) atTop
      suzukiXiSafeUpperHalfPlane := by
  intro V hV z hz
  obtain ⟨K, hK, hsum⟩ :=
    hasSumLocallyUniformlyOn_zetaSuzukiSpectralPSummand t V hV z hz
  refine ⟨K, hK, ?_⟩
  filter_upwards
    [tendsto_spectralZetaZeroWindow_atTop.eventually hsum] with T hT
  intro w hw
  simpa [suzukiXiSpectralPWindow,
    zetaSuzukiSpectralPSummand,
    suzukiXiUpperEvaluationDenominator] using hT w hw

/-- Suzuki's infinite spectral `P_t` is holomorphic throughout the safe upper
half-plane. -/
theorem differentiableOn_riemannXiSuzukiSpectralP (t : ℝ) :
    DifferentiableOn ℂ (riemannXiSuzukiSpectralP t)
      suzukiXiSafeUpperHalfPlane := by
  apply
    (hasSumLocallyUniformlyOn_zetaSuzukiSpectralPSummand t).differentiableOn
  · exact Eventually.of_forall fun S ↦
      DifferentiableOn.fun_sum fun rho _ ↦
        differentiableOn_zetaSuzukiSpectralPSummand t rho
  · exact isOpen_suzukiXiSafeUpperHalfPlane

/-- The spatial derivative summand of the spectral `P_t` series.  This is
distinct from the already formalized derivative in screw time. -/
def zetaSuzukiSpectralPSpatialDerivativeSummand
    (t : ℝ) (z : ℂ) (rho : NontrivialZetaZero) : ℂ :=
  -((analyticZetaZeroMultiplicity rho : ℂ) *
      suzukiSpectralScrewCoefficient t
        (zetaSpectralCoordinate rho.1)) /
    (z - zetaSpectralCoordinate rho.1) ^ 2

/-- Exact spatial derivative of one spectral `P_t` summand in the safe upper
half-plane. -/
theorem hasDerivAt_zetaSuzukiSpectralPSummand
    (t : ℝ) {z : ℂ} (hz : z ∈ suzukiXiSafeUpperHalfPlane)
    (rho : NontrivialZetaZero) :
    HasDerivAt (fun w : ℂ ↦ zetaSuzukiSpectralPSummand t w rho)
      (zetaSuzukiSpectralPSpatialDerivativeSummand t z rho) z := by
  have hden : z - zetaSpectralCoordinate rho.1 ≠ 0 := by
    exact Complex.normSq_pos.mp
      (normSq_suzukiXiUpperEvaluationDenominator_pos hz rho)
  have h :=
    (hasDerivAt_const z
      ((analyticZetaZeroMultiplicity rho : ℂ) *
        suzukiSpectralScrewCoefficient t
          (zetaSpectralCoordinate rho.1))).div
      ((hasDerivAt_id z).sub_const (zetaSpectralCoordinate rho.1))
      hden
  unfold zetaSuzukiSpectralPSummand
    suzukiXiUpperEvaluationDenominator
    zetaSuzukiSpectralPSpatialDerivativeSummand
  simpa [Pi.div_def, id] using h

/-- Spatial differentiation passes through the complete spectral zero series
at every point in the safe upper half-plane. -/
theorem hasSum_zetaSuzukiSpectralPSpatialDerivativeSummand
    (t : ℝ) {z : ℂ} (hz : z ∈ suzukiXiSafeUpperHalfPlane) :
    HasSum (zetaSuzukiSpectralPSpatialDerivativeSummand t z)
      (deriv (riemannXiSuzukiSpectralP t) z) := by
  have hpartials : ∀ S : Finset NontrivialZetaZero,
      DifferentiableOn ℂ
        (fun w : ℂ ↦ ∑ rho ∈ S,
          zetaSuzukiSpectralPSummand t w rho)
        suzukiXiSafeUpperHalfPlane :=
    fun _ ↦ DifferentiableOn.fun_sum fun rho _ ↦
      differentiableOn_zetaSuzukiSpectralPSummand t rho
  have hraw : HasSum
      (fun rho : NontrivialZetaZero ↦
        deriv (fun w : ℂ ↦ zetaSuzukiSpectralPSummand t w rho) z)
      (deriv (riemannXiSuzukiSpectralP t) z) := by
    rw [HasSum]
    have hderiv :=
      (hasSumLocallyUniformlyOn_zetaSuzukiSpectralPSummand t).deriv
        (Eventually.of_forall hpartials)
        isOpen_suzukiXiSafeUpperHalfPlane
    convert! hderiv.tendsto_at hz using 1
    ext S
    exact (deriv_fun_sum fun rho _ ↦
      (differentiableOn_zetaSuzukiSpectralPSummand t rho).differentiableAt
        (isOpen_suzukiXiSafeUpperHalfPlane.mem_nhds hz)).symm
  rw [HasSum] at hraw ⊢
  convert hraw using 1
  ext S
  apply Finset.sum_congr rfl
  intro rho _hrho
  exact (hasDerivAt_zetaSuzukiSpectralPSummand t hz rho).deriv.symm

/-- The derivative of the complete spectral `P_t` is the corresponding
unconditional sum of double-pole summands. -/
theorem deriv_riemannXiSuzukiSpectralP_eq_tsum
    (t : ℝ) {z : ℂ} (hz : z ∈ suzukiXiSafeUpperHalfPlane) :
    deriv (riemannXiSuzukiSpectralP t) z =
      ∑' rho : NontrivialZetaZero,
        zetaSuzukiSpectralPSpatialDerivativeSummand t z rho := by
  exact
    (hasSum_zetaSuzukiSpectralPSpatialDerivativeSummand t hz).tsum_eq.symm

end

end RiemannGaussian
