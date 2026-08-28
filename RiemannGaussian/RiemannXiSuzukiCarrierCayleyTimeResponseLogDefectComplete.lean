import RiemannGaussian.RiemannXiSuzukiCarrierCayleyTimeResponseLogDefect
import RiemannGaussian.GaussianXiCompleteMassFiniteness
import Mathlib.Analysis.Calculus.SmoothSeries
import Mathlib.Analysis.Calculus.Deriv.MeanValue

/-!
# Complete height derivative of the Gaussian/Suzuki action

The finite height-antiderivative identity extends to the complete upper
spectral divisor.  Boundary-density summability supplies a single summable
majorant for all term derivatives in a zero-free collar, so differentiation
passes through the genuine infinite divisor.  The resulting derivative is
twice the real part of the complete signed Suzuki initial velocity.  After
identifying the real divisor sum with the finite complete proper-time action,
this becomes a differential law for the Gaussian heat action itself.
-/

open Complex Filter MeasureTheory Set Topology
open scoped Classical ENNReal Interval Topology

namespace RiemannGaussian

noncomputable section

/-- The vertically continued log-defect summand, restricted to the genuine
upper spectral divisor. -/
def zetaUpperSelectedVerticalLogDefectSummand
    (x y : ℝ) (rho : NontrivialZetaZero) : ℝ :=
  if 0 < (zetaSpectralCoordinate rho.1).im then
    zetaUpperVerticalLogDefectSummand x y rho
  else 0

/-- The real height derivative contributed by one selected upper zero. -/
def zetaUpperVerticalLogDefectDerivativeSummand
    (x y : ℝ) (rho : NontrivialZetaZero) : ℝ :=
  2 * (-Complex.I *
    zetaUpperBlaschkeSelectedLogDerivativeSummand
      (upperBoundaryApproachPoint x y) rho).re

/-- The complete real vertically continued upper-divisor log defect. -/
def riemannXiUpperVerticalLogDefectTotal (x y : ℝ) : ℝ :=
  ∑' rho : NontrivialZetaZero,
    zetaUpperSelectedVerticalLogDefectSummand x y rho

/-- The complete real height-response sum. -/
def riemannXiUpperVerticalLogDefectDerivativeTotal
    (x y : ℝ) : ℝ :=
  ∑' rho : NontrivialZetaZero,
    zetaUpperVerticalLogDefectDerivativeSummand x y rho

/-- Each selected vertical summand has the declared exact height derivative
throughout a uniform zero-free collar. -/
theorem hasDerivAt_zetaUpperSelectedVerticalLogDefectSummand
    {x delta y : ℝ} (hdelta : 0 < delta)
    (hgap : ∀ rho : NontrivialZetaZero,
      0 < (zetaSpectralCoordinate rho.1).im →
        delta ≤ ‖(x : ℂ) - zetaSpectralCoordinate rho.1‖)
    (hy : 0 < y) (hySmall : y < delta / 2)
    (rho : NontrivialZetaZero) :
    HasDerivAt
      (fun v : ℝ ↦ zetaUpperSelectedVerticalLogDefectSummand x v rho)
      (zetaUpperVerticalLogDefectDerivativeSummand x y rho) y := by
  by_cases hupper : 0 < (zetaSpectralCoordinate rho.1).im
  · have hnorm := hgap rho hupper
    have hyNorm : y < ‖(x : ℂ) - zetaSpectralCoordinate rho.1‖ := by
      have hhalf : delta / 2 ≤
          ‖(x : ℂ) - zetaSpectralCoordinate rho.1‖ :=
        (half_le_self hdelta.le).trans hnorm
      exact hySmall.trans_le hhalf
    have hradial : y ^ 2 < Complex.normSq
        ((x : ℂ) - zetaSpectralCoordinate rho.1) := by
      rw [Complex.normSq_eq_norm_sq]
      nlinarith [norm_nonneg
        ((x : ℂ) - zetaSpectralCoordinate rho.1)]
    unfold zetaUpperSelectedVerticalLogDefectSummand
      zetaUpperVerticalLogDefectDerivativeSummand
      zetaUpperBlaschkeSelectedLogDerivativeSummand
    simp only [if_pos hupper]
    exact hasDerivAt_zetaUpperVerticalLogDefectSummand
      rho hy.le hupper hradial
  · unfold zetaUpperSelectedVerticalLogDefectSummand
      zetaUpperVerticalLogDefectDerivativeSummand
      zetaUpperBlaschkeSelectedLogDerivativeSummand
    simp only [if_neg hupper, mul_zero, zero_re]
    exact hasDerivAt_const (x := y) (c := (0 : ℝ))

/-- The complete boundary density gives a summable height-independent
majorant for every selected log-defect derivative in the collar. -/
theorem norm_zetaUpperVerticalLogDefectDerivativeSummand_le
    {x delta y : ℝ} (hdelta : 0 < delta)
    (hgap : ∀ rho : NontrivialZetaZero,
      0 < (zetaSpectralCoordinate rho.1).im →
        delta ≤ ‖(x : ℂ) - zetaSpectralCoordinate rho.1‖)
    (hy : 0 < y) (hySmall : y < delta / 2)
    (rho : NontrivialZetaZero) :
    ‖zetaUpperVerticalLogDefectDerivativeSummand x y rho‖ ≤
      4 * zetaUpperBlaschkeBoundaryDensitySummand x rho := by
  have hlog :=
    norm_zetaUpperBlaschkeSelectedLogDerivativeSummand_approach_le
      hdelta hgap hy hySmall rho
  unfold zetaUpperVerticalLogDefectDerivativeSummand
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
  calc
    2 * |(-Complex.I *
          zetaUpperBlaschkeSelectedLogDerivativeSummand
            (upperBoundaryApproachPoint x y) rho).re| ≤
        2 * ‖-Complex.I *
          zetaUpperBlaschkeSelectedLogDerivativeSummand
            (upperBoundaryApproachPoint x y) rho‖ := by
      gcongr
      exact Complex.abs_re_le_norm _
    _ = 2 * ‖zetaUpperBlaschkeSelectedLogDerivativeSummand
          (upperBoundaryApproachPoint x y) rho‖ := by
      rw [norm_mul, norm_neg, norm_I, one_mul]
    _ ≤ 2 * (2 * zetaUpperBlaschkeBoundaryDensitySummand x rho) := by
      gcongr
    _ = 4 * zetaUpperBlaschkeBoundaryDensitySummand x rho := by ring

/-- In the collar, each selected vertical summand is exactly the established
hyperbolic log-defect summand. -/
theorem zetaUpperSelectedVerticalLogDefectSummand_eq_hyperbolic
    {x delta y : ℝ} (hdelta : 0 < delta)
    (hgap : ∀ rho : NontrivialZetaZero,
      0 < (zetaSpectralCoordinate rho.1).im →
        delta ≤ ‖(x : ℂ) - zetaSpectralCoordinate rho.1‖)
    (hy : 0 < y) (hySmall : y < delta / 2)
    (rho : NontrivialZetaZero) :
    zetaUpperSelectedVerticalLogDefectSummand x y rho =
      zetaUpperHyperbolicLogDefectSummand
        (upperBoundaryApproachPoint x y) rho := by
  by_cases hupper : 0 < (zetaSpectralCoordinate rho.1).im
  · have hsep := half_boundaryGap_le_norm_upperBoundaryApproachPoint_sub
      hdelta hgap hy hySmall rho hupper
    have hne : upperBoundaryApproachPoint x y ≠
        zetaSpectralCoordinate rho.1 := by
      apply sub_ne_zero.mp
      rw [← norm_pos_iff]
      exact (half_pos hdelta).trans_le hsep
    unfold zetaUpperSelectedVerticalLogDefectSummand
    rw [if_pos hupper]
    exact zetaUpperVerticalLogDefectSummand_eq_hyperbolic
      rho hy hupper hne
  · unfold zetaUpperSelectedVerticalLogDefectSummand
      zetaUpperHyperbolicLogDefectSummand
    rw [if_neg hupper, if_neg hupper]

/-- The complete selected vertical log-defect series is summable at every
point of the uniform collar. -/
theorem summable_zetaUpperSelectedVerticalLogDefectSummand
    {x delta y : ℝ} (hdelta : 0 < delta)
    (hgap : ∀ rho : NontrivialZetaZero,
      0 < (zetaSpectralCoordinate rho.1).im →
        delta ≤ ‖(x : ℂ) - zetaSpectralCoordinate rho.1‖)
    (hy : 0 < y) (hySmall : y < delta / 2) :
    Summable (zetaUpperSelectedVerticalLogDefectSummand x y) := by
  have hz : 0 < (upperBoundaryApproachPoint x y).im := by
    simpa using hy
  have hxi : riemannXiSpectral (upperBoundaryApproachPoint x y) ≠ 0 :=
    riemannXiSpectral_upperBoundaryApproachPoint_ne_zero
      hdelta hgap hy hySmall
  exact (summable_zetaUpperHyperbolicLogDefectSummand hz hxi).congr
    (fun rho ↦
      (zetaUpperSelectedVerticalLogDefectSummand_eq_hyperbolic
        hdelta hgap hy hySmall rho).symm)

/-- Differentiation passes through the complete genuine upper divisor in a
uniform zero-free collar. -/
theorem hasDerivAt_riemannXiUpperVerticalLogDefectTotal
    {x delta y : ℝ} (hdelta : 0 < delta)
    (hgap : ∀ rho : NontrivialZetaZero,
      0 < (zetaSpectralCoordinate rho.1).im →
        delta ≤ ‖(x : ℂ) - zetaSpectralCoordinate rho.1‖)
    (hy : 0 < y) (hySmall : y < delta / 2) :
    HasDerivAt
      (fun v : ℝ ↦ riemannXiUpperVerticalLogDefectTotal x v)
      (riemannXiUpperVerticalLogDefectDerivativeTotal x y) y := by
  have hmajor : Summable
      (fun rho : NontrivialZetaZero ↦
        4 * zetaUpperBlaschkeBoundaryDensitySummand x rho) :=
    (summable_zetaUpperBlaschkeBoundaryDensitySummand x).mul_left 4
  have hyMem : y ∈ Ioo (0 : ℝ) (delta / 2) := ⟨hy, hySmall⟩
  unfold riemannXiUpperVerticalLogDefectTotal
    riemannXiUpperVerticalLogDefectDerivativeTotal
  exact hasDerivAt_tsum_of_isPreconnected
    hmajor isOpen_Ioo isPreconnected_Ioo
    (fun rho v hv ↦
      hasDerivAt_zetaUpperSelectedVerticalLogDefectSummand
        hdelta hgap hv.1 hv.2 rho)
    (fun rho v hv ↦
      norm_zetaUpperVerticalLogDefectDerivativeSummand_le
        hdelta hgap hv.1 hv.2 rho)
    hyMem
    (summable_zetaUpperSelectedVerticalLogDefectSummand
      hdelta hgap hy hySmall)
    hyMem

/-- The complete vertical log defect is the actual convergent real
hyperbolic log-defect series at every point of the collar. -/
theorem riemannXiUpperVerticalLogDefectTotal_eq_hyperbolic_tsum
    {x delta y : ℝ} (hdelta : 0 < delta)
    (hgap : ∀ rho : NontrivialZetaZero,
      0 < (zetaSpectralCoordinate rho.1).im →
        delta ≤ ‖(x : ℂ) - zetaSpectralCoordinate rho.1‖)
    (hy : 0 < y) (hySmall : y < delta / 2) :
    riemannXiUpperVerticalLogDefectTotal x y =
      ∑' rho : NontrivialZetaZero,
        zetaUpperHyperbolicLogDefectSummand
          (upperBoundaryApproachPoint x y) rho := by
  unfold riemannXiUpperVerticalLogDefectTotal
  apply tsum_congr
  intro rho
  exact zetaUpperSelectedVerticalLogDefectSummand_eq_hyperbolic
    hdelta hgap hy hySmall rho

/-- The complete real derivative sum is exactly twice the real part of the
complete signed Suzuki initial velocity. -/
theorem riemannXiUpperVerticalLogDefectDerivativeTotal_eq_initialVelocity
    {x delta y : ℝ} (hdelta : 0 < delta)
    (hgap : ∀ rho : NontrivialZetaZero,
      0 < (zetaSpectralCoordinate rho.1).im →
        delta ≤ ‖(x : ℂ) - zetaSpectralCoordinate rho.1‖)
    (hy : 0 < y) (hySmall : y < delta / 2) :
    riemannXiUpperVerticalLogDefectDerivativeTotal x y =
      2 * (riemannXiSuzukiOffAxisSignedPInitialVelocity
        (upperBoundaryApproachPoint x y)).re := by
  have hz : 0 < (upperBoundaryApproachPoint x y).im := by
    simpa using hy
  have hxi : riemannXiSpectral (upperBoundaryApproachPoint x y) ≠ 0 :=
    riemannXiSpectral_upperBoundaryApproachPoint_ne_zero
      hdelta hgap hy hySmall
  let f : NontrivialZetaZero → ℂ := fun rho ↦
    zetaUpperBlaschkeSelectedLogDerivativeSummand
      (upperBoundaryApproachPoint x y) rho
  have hf : Summable f :=
    summable_zetaUpperBlaschkeSelectedLogDerivativeSummand hz hxi
  have hscaled : Summable (fun rho ↦ -Complex.I * f rho) :=
    hf.mul_left (-Complex.I)
  unfold riemannXiUpperVerticalLogDefectDerivativeTotal
    zetaUpperVerticalLogDefectDerivativeSummand
    riemannXiSuzukiOffAxisSignedPInitialVelocity
    riemannXiUpperBlaschkeCompleteLogDerivative
  change
    (∑' rho : NontrivialZetaZero, 2 * (-Complex.I * f rho).re) =
      2 * (-Complex.I * (∑' rho : NontrivialZetaZero, f rho)).re
  calc
    (∑' rho : NontrivialZetaZero, 2 * (-Complex.I * f rho).re) =
        2 * ∑' rho : NontrivialZetaZero, (-Complex.I * f rho).re := by
      rw [tsum_mul_left]
    _ = 2 * (∑' rho : NontrivialZetaZero,
        -Complex.I * f rho).re := by
      rw [Complex.re_tsum hscaled]
    _ = 2 * (-Complex.I *
        (∑' rho : NontrivialZetaZero, f rho)).re := by
      rw [tsum_mul_left]

/-- The real value of the complete Gaussian proper-time action is literally
the complete vertically continued log defect throughout the collar. -/
theorem riemannXiUpperHyperbolicHeatAction_toReal_eq_verticalLogDefectTotal
    {x delta y : ℝ} (hdelta : 0 < delta)
    (hgap : ∀ rho : NontrivialZetaZero,
      0 < (zetaSpectralCoordinate rho.1).im →
        delta ≤ ‖(x : ℂ) - zetaSpectralCoordinate rho.1‖)
    (hy : 0 < y) (hySmall : y < delta / 2) :
    (riemannXiUpperHyperbolicHeatAction
      (upperBoundaryApproachPoint x y)).toReal =
      riemannXiUpperVerticalLogDefectTotal x y := by
  have hz : 0 < (upperBoundaryApproachPoint x y).im := by
    simpa using hy
  have hxi : riemannXiSpectral (upperBoundaryApproachPoint x y) ≠ 0 :=
    riemannXiSpectral_upperBoundaryApproachPoint_ne_zero
      hdelta hgap hy hySmall
  rw [riemannXiUpperHyperbolicHeatAction_eq_ofReal_tsum hz hxi,
    ENNReal.toReal_ofReal]
  · exact
      (riemannXiUpperVerticalLogDefectTotal_eq_hyperbolic_tsum
        hdelta hgap hy hySmall).symm
  · apply tsum_nonneg
    intro rho
    apply zetaUpperHyperbolicLogDefectSummand_nonneg hz rho
    intro heq
    apply hxi
    rw [heq]
    exact (riemannXiSpectral_eq_zero_iff_exists_zetaZero _).2 ⟨rho, rfl⟩

/-- Complete Gaussian/Suzuki differential law: the height derivative of the
real complete proper-time action is twice the real part of the complete
signed Suzuki initial velocity. -/
theorem hasDerivAt_riemannXiUpperHyperbolicHeatAction_toReal_approach
    {x delta y : ℝ} (hdelta : 0 < delta)
    (hgap : ∀ rho : NontrivialZetaZero,
      0 < (zetaSpectralCoordinate rho.1).im →
        delta ≤ ‖(x : ℂ) - zetaSpectralCoordinate rho.1‖)
    (hy : 0 < y) (hySmall : y < delta / 2) :
    HasDerivAt
      (fun v : ℝ ↦ (riemannXiUpperHyperbolicHeatAction
        (upperBoundaryApproachPoint x v)).toReal)
      (2 * (riemannXiSuzukiOffAxisSignedPInitialVelocity
        (upperBoundaryApproachPoint x y)).re) y := by
  have hvertical :=
    (hasDerivAt_riemannXiUpperVerticalLogDefectTotal
      hdelta hgap hy hySmall).congr_deriv
        (riemannXiUpperVerticalLogDefectDerivativeTotal_eq_initialVelocity
          hdelta hgap hy hySmall)
  apply hvertical.congr_of_eventuallyEq
  apply eventuallyEq_of_mem (Ioo_mem_nhds hy hySmall)
  intro v hv
  exact
    (riemannXiUpperHyperbolicHeatAction_toReal_eq_verticalLogDefectTotal
      hdelta hgap hv.1 hv.2)

/-- The complete real height-response series is summable throughout the
uniform collar. -/
theorem summable_zetaUpperVerticalLogDefectDerivativeSummand
    {x delta y : ℝ} (hdelta : 0 < delta)
    (hgap : ∀ rho : NontrivialZetaZero,
      0 < (zetaSpectralCoordinate rho.1).im →
        delta ≤ ‖(x : ℂ) - zetaSpectralCoordinate rho.1‖)
    (hy : 0 < y) (hySmall : y < delta / 2) :
    Summable (zetaUpperVerticalLogDefectDerivativeSummand x y) := by
  apply ((summable_zetaUpperBlaschkeBoundaryDensitySummand x).mul_left 4).of_norm_bounded
  intro rho
  exact norm_zetaUpperVerticalLogDefectDerivativeSummand_le
    hdelta hgap hy hySmall rho

/-- Every selected complete height-response summand is nonnegative in the
collar. -/
theorem zetaUpperVerticalLogDefectDerivativeSummand_nonneg
    {x delta y : ℝ} (hdelta : 0 < delta)
    (hgap : ∀ rho : NontrivialZetaZero,
      0 < (zetaSpectralCoordinate rho.1).im →
        delta ≤ ‖(x : ℂ) - zetaSpectralCoordinate rho.1‖)
    (hy : 0 < y) (hySmall : y < delta / 2)
    (rho : NontrivialZetaZero) :
    0 ≤ zetaUpperVerticalLogDefectDerivativeSummand x y rho := by
  by_cases hupper : 0 < (zetaSpectralCoordinate rho.1).im
  · unfold zetaUpperVerticalLogDefectDerivativeSummand
      zetaUpperBlaschkeSelectedLogDerivativeSummand
    rw [if_pos hupper]
    exact mul_nonneg (by norm_num)
      (re_neg_I_mul_zetaUpperBlaschkeLogDerivativeSummand_approach_pos
        hdelta hgap hy hySmall rho hupper).le
  · unfold zetaUpperVerticalLogDefectDerivativeSummand
      zetaUpperBlaschkeSelectedLogDerivativeSummand
    simp only [if_neg hupper, mul_zero, zero_re, le_refl]

/-- One genuine upper zero contributes a strictly positive complete height
response in the collar. -/
theorem zetaUpperVerticalLogDefectDerivativeSummand_pos
    {x delta y : ℝ} (hdelta : 0 < delta)
    (hgap : ∀ rho : NontrivialZetaZero,
      0 < (zetaSpectralCoordinate rho.1).im →
        delta ≤ ‖(x : ℂ) - zetaSpectralCoordinate rho.1‖)
    (hy : 0 < y) (hySmall : y < delta / 2)
    (rho : NontrivialZetaZero)
    (hupper : 0 < (zetaSpectralCoordinate rho.1).im) :
    0 < zetaUpperVerticalLogDefectDerivativeSummand x y rho := by
  unfold zetaUpperVerticalLogDefectDerivativeSummand
    zetaUpperBlaschkeSelectedLogDerivativeSummand
  rw [if_pos hupper]
  exact mul_pos (by norm_num)
    (re_neg_I_mul_zetaUpperBlaschkeLogDerivativeSummand_approach_pos
      hdelta hgap hy hySmall rho hupper)

/-- Failure of RH makes the complete height response strictly positive at
every point of the uniform collar. -/
theorem riemannXiUpperVerticalLogDefectDerivativeTotal_pos_of_not_rh
    {x delta y : ℝ} (hdelta : 0 < delta)
    (hgap : ∀ rho : NontrivialZetaZero,
      0 < (zetaSpectralCoordinate rho.1).im →
        delta ≤ ‖(x : ℂ) - zetaSpectralCoordinate rho.1‖)
    (hy : 0 < y) (hySmall : y < delta / 2)
    (hRH : ¬RiemannHypothesis) :
    0 < riemannXiUpperVerticalLogDefectDerivativeTotal x y := by
  obtain ⟨w, hwzero, hwupper⟩ :=
    exists_riemannXiSpectral_upper_zero_of_not_riemannHypothesis hRH
  obtain ⟨rho, rfl⟩ :=
    (riemannXiSpectral_eq_zero_iff_exists_zetaZero w).mp hwzero
  unfold riemannXiUpperVerticalLogDefectDerivativeTotal
  exact
    (summable_zetaUpperVerticalLogDefectDerivativeSummand
      hdelta hgap hy hySmall).tsum_pos
      (zetaUpperVerticalLogDefectDerivativeSummand_nonneg
        hdelta hgap hy hySmall)
      rho
      (zetaUpperVerticalLogDefectDerivativeSummand_pos
        hdelta hgap hy hySmall rho hwupper)

/-- Under RH, every selected complete height-response summand vanishes. -/
theorem riemannXiUpperVerticalLogDefectDerivativeTotal_eq_zero_of_rh
    (x y : ℝ) (hRH : RiemannHypothesis) :
    riemannXiUpperVerticalLogDefectDerivativeTotal x y = 0 := by
  have hzero :
      zetaUpperVerticalLogDefectDerivativeSummand x y =
        fun _rho : NontrivialZetaZero ↦ 0 := by
    funext rho
    have him : (zetaSpectralCoordinate rho.1).im = 0 :=
      (riemannHypothesis_iff_spectralCoordinate_real.mp hRH)
        rho.1 rho.2.1 rho.2.2.1 rho.2.2.2
    unfold zetaUpperVerticalLogDefectDerivativeSummand
      zetaUpperBlaschkeSelectedLogDerivativeSummand
    rw [if_neg (by linarith : ¬0 < (zetaSpectralCoordinate rho.1).im)]
    simp
  unfold riemannXiUpperVerticalLogDefectDerivativeTotal
  rw [hzero]
  simp

/-- In any uniform boundary collar, vanishing of the complete height
response at one positive height is exactly RH. -/
theorem riemannXiUpperVerticalLogDefectDerivativeTotal_eq_zero_iff_rh
    {x delta y : ℝ} (hdelta : 0 < delta)
    (hgap : ∀ rho : NontrivialZetaZero,
      0 < (zetaSpectralCoordinate rho.1).im →
        delta ≤ ‖(x : ℂ) - zetaSpectralCoordinate rho.1‖)
    (hy : 0 < y) (hySmall : y < delta / 2) :
    riemannXiUpperVerticalLogDefectDerivativeTotal x y = 0 ↔
      RiemannHypothesis := by
  constructor
  · intro hzero
    by_contra hRH
    have hpos :=
      riemannXiUpperVerticalLogDefectDerivativeTotal_pos_of_not_rh
        hdelta hgap hy hySmall hRH
    linarith
  · exact riemannXiUpperVerticalLogDefectDerivativeTotal_eq_zero_of_rh x y

/-- Derivative form of the complete Gaussian/Suzuki law. -/
theorem deriv_riemannXiUpperHyperbolicHeatAction_toReal_approach
    {x delta y : ℝ} (hdelta : 0 < delta)
    (hgap : ∀ rho : NontrivialZetaZero,
      0 < (zetaSpectralCoordinate rho.1).im →
        delta ≤ ‖(x : ℂ) - zetaSpectralCoordinate rho.1‖)
    (hy : 0 < y) (hySmall : y < delta / 2) :
    deriv (fun v : ℝ ↦ (riemannXiUpperHyperbolicHeatAction
      (upperBoundaryApproachPoint x v)).toReal) y =
      2 * (riemannXiSuzukiOffAxisSignedPInitialVelocity
        (upperBoundaryApproachPoint x y)).re :=
  (hasDerivAt_riemannXiUpperHyperbolicHeatAction_toReal_approach
    hdelta hgap hy hySmall).deriv

/-- At every positive height in a uniform collar, the height derivative of
the complete Gaussian action vanishes exactly under RH. -/
theorem deriv_riemannXiUpperHyperbolicHeatAction_toReal_approach_eq_zero_iff_rh
    {x delta y : ℝ} (hdelta : 0 < delta)
    (hgap : ∀ rho : NontrivialZetaZero,
      0 < (zetaSpectralCoordinate rho.1).im →
        delta ≤ ‖(x : ℂ) - zetaSpectralCoordinate rho.1‖)
    (hy : 0 < y) (hySmall : y < delta / 2) :
    deriv (fun v : ℝ ↦ (riemannXiUpperHyperbolicHeatAction
      (upperBoundaryApproachPoint x v)).toReal) y = 0 ↔
      RiemannHypothesis := by
  rw [deriv_riemannXiUpperHyperbolicHeatAction_toReal_approach
    hdelta hgap hy hySmall,
    ← riemannXiUpperVerticalLogDefectDerivativeTotal_eq_initialVelocity
      hdelta hgap hy hySmall]
  exact riemannXiUpperVerticalLogDefectDerivativeTotal_eq_zero_iff_rh
    hdelta hgap hy hySmall

/-- Under failure of RH, the height derivative of the complete Gaussian
action is strictly positive at every point of the collar. -/
theorem deriv_riemannXiUpperHyperbolicHeatAction_toReal_approach_pos_of_not_rh
    {x delta y : ℝ} (hdelta : 0 < delta)
    (hgap : ∀ rho : NontrivialZetaZero,
      0 < (zetaSpectralCoordinate rho.1).im →
        delta ≤ ‖(x : ℂ) - zetaSpectralCoordinate rho.1‖)
    (hy : 0 < y) (hySmall : y < delta / 2)
    (hRH : ¬RiemannHypothesis) :
    0 < deriv (fun v : ℝ ↦ (riemannXiUpperHyperbolicHeatAction
      (upperBoundaryApproachPoint x v)).toReal) y := by
  rw [deriv_riemannXiUpperHyperbolicHeatAction_toReal_approach
    hdelta hgap hy hySmall,
    ← riemannXiUpperVerticalLogDefectDerivativeTotal_eq_initialVelocity
      hdelta hgap hy hySmall]
  exact riemannXiUpperVerticalLogDefectDerivativeTotal_pos_of_not_rh
    hdelta hgap hy hySmall hRH

/-- Under failure of RH, the real complete Gaussian action is strictly
increasing with observation height throughout every uniform boundary
collar. -/
theorem strictMonoOn_riemannXiUpperHyperbolicHeatAction_toReal_approach_of_not_rh
    {x delta : ℝ} (hdelta : 0 < delta)
    (hgap : ∀ rho : NontrivialZetaZero,
      0 < (zetaSpectralCoordinate rho.1).im →
        delta ≤ ‖(x : ℂ) - zetaSpectralCoordinate rho.1‖)
    (hRH : ¬RiemannHypothesis) :
    StrictMonoOn
      (fun y : ℝ ↦ (riemannXiUpperHyperbolicHeatAction
        (upperBoundaryApproachPoint x y)).toReal)
      (Ioo 0 (delta / 2)) := by
  apply strictMonoOn_of_deriv_pos (convex_Ioo (0 : ℝ) (delta / 2))
  · intro y hy
    exact
      (hasDerivAt_riemannXiUpperHyperbolicHeatAction_toReal_approach
        hdelta hgap hy.1 hy.2).continuousAt.continuousWithinAt
  · intro y hy
    have hy' : y ∈ Ioo (0 : ℝ) (delta / 2) := interior_subset hy
    exact
      deriv_riemannXiUpperHyperbolicHeatAction_toReal_approach_pos_of_not_rh
        hdelta hgap hy'.1 hy'.2 hRH

end

end RiemannGaussian
