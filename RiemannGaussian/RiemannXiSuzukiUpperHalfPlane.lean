import RiemannGaussian.RiemannXiSuzukiSafeEvaluation

/-!
# Suzuki's infinite spectral signal above the xi zero strip

All spectral-xi zeros lie in `|Im alpha| < 1/2`.  This file develops Suzuki's
zero expansion throughout the safe half-plane `Im z > 1/2`.  A quantitative
vertical-gap estimate controls the Cauchy evaluation coordinates by the
unconditionally summable inverse-square xi-divisor weight.  Consequently:

* evaluation at every safe point is a literal `ℓ²` vector;
* the infinite spectral `P_t(z)` series is absolutely summable;
* `P_t(z)` is exactly the Hilbert pairing of the evaluation and coefficient
  vectors;
* genuine symmetric zero windows converge to the infinite value; and
* after multiplication by the theta carrier, the infinite signal has
  Suzuki's normalized zero-function expansion (3.6).

These are unconditional spectral statements.  The functions are presently
constructed pointwise above the zero strip.  The arithmetic prime/gamma
formula, continuation to the real-axis `L²(R)` class, removable-point
extensions, and off-RH Gram control remain to be formalized separately.
-/

open Complex Filter MeasureTheory Metric Polynomial Set Topology
open scoped Classical ENNReal Interval Topology lp

namespace RiemannGaussian

noncomputable section

/-- Vertical clearance above the spectral xi zero strip. -/
def suzukiXiUpperEvaluationGap (z : ℂ) : ℝ :=
  z.im - 1 / 2

/-- A positive comparison constant for Cauchy evaluation above the zero
strip. -/
def suzukiXiUpperEvaluationConstant (z : ℂ) : ℝ :=
  (1 + 2 * z.re ^ 2 + 2 * suzukiXiUpperEvaluationGap z ^ 2) /
    suzukiXiUpperEvaluationGap z ^ 2

/-- The Cauchy denominator at a general upper safe point. -/
def suzukiXiUpperEvaluationDenominator (z alpha : ℂ) : ℂ :=
  z - alpha

/-- The general Cauchy denominator has the expected Euclidean squared norm. -/
theorem normSq_suzukiXiUpperEvaluationDenominator
    (z alpha : ℂ) :
    Complex.normSq (suzukiXiUpperEvaluationDenominator z alpha) =
      (z.re - alpha.re) ^ 2 + (z.im - alpha.im) ^ 2 := by
  simp [suzukiXiUpperEvaluationDenominator, Complex.normSq_apply]
  ring

/-- A point strictly above the half-width zero strip has positive clearance. -/
theorem suzukiXiUpperEvaluationGap_pos
    {z : ℂ} (hz : 1 / 2 < z.im) :
    0 < suzukiXiUpperEvaluationGap z := by
  unfold suzukiXiUpperEvaluationGap
  linarith

/-- Every genuine xi zero lies at least the declared clearance below a safe
upper evaluation point. -/
theorem spectral_gap_le_upperEvaluation_im_sub
    (z : ℂ) (rho : NontrivialZetaZero) :
    suzukiXiUpperEvaluationGap z ≤
      z.im - (zetaSpectralCoordinate rho.1).im := by
  have hstrip := NontrivialZetaZero.abs_spectralCoordinate_im_lt_half rho
  have him : (zetaSpectralCoordinate rho.1).im < 1 / 2 := by
    exact (le_abs_self _).trans_lt hstrip
  unfold suzukiXiUpperEvaluationGap
  linarith

/-- The vertical gap and the real-coordinate triangle inequality give an
explicit quadratic domination of inverse-square spectral weights by a Cauchy
denominator above the critical strip. -/
theorem upperEvaluation_denominator_domination
    {z : ℂ} (hz : 1 / 2 < z.im) (rho : NontrivialZetaZero) :
    suzukiXiUpperEvaluationGap z ^ 2 *
        (1 + (zetaSpectralCoordinate rho.1).re ^ 2) ≤
      (1 + 2 * z.re ^ 2 +
          2 * suzukiXiUpperEvaluationGap z ^ 2) *
        Complex.normSq
          (suzukiXiUpperEvaluationDenominator z
            (zetaSpectralCoordinate rho.1)) := by
  let delta : ℝ := suzukiXiUpperEvaluationGap z
  let a : ℝ := (zetaSpectralCoordinate rho.1).re
  let r : ℝ := z.re - a
  let v : ℝ := z.im - (zetaSpectralCoordinate rho.1).im
  have hdelta : 0 ≤ delta :=
    (suzukiXiUpperEvaluationGap_pos hz).le
  have hdeltav : delta ≤ v :=
    spectral_gap_le_upperEvaluation_im_sub z rho
  have hv : 0 ≤ v := hdelta.trans hdeltav
  have hdeltaSq : delta ^ 2 ≤ v ^ 2 :=
    (sq_le_sq₀ hdelta hv).2 hdeltav
  have hreal : a ^ 2 ≤ 2 * z.re ^ 2 + 2 * r ^ 2 := by
    dsimp [r]
    nlinarith [sq_nonneg (a - 2 * z.re)]
  have hrealScaled :
      delta ^ 2 * a ^ 2 ≤
        delta ^ 2 * (2 * z.re ^ 2 + 2 * r ^ 2) :=
    mul_le_mul_of_nonneg_left hreal (sq_nonneg delta)
  have hvisScaled :
      (1 + 2 * z.re ^ 2) * delta ^ 2 ≤
        (1 + 2 * z.re ^ 2) * v ^ 2 :=
    mul_le_mul_of_nonneg_left hdeltaSq (by positivity)
  rw [normSq_suzukiXiUpperEvaluationDenominator]
  change delta ^ 2 * (1 + a ^ 2) ≤
    (1 + 2 * z.re ^ 2 + 2 * delta ^ 2) * (r ^ 2 + v ^ 2)
  nlinarith [sq_nonneg r, sq_nonneg v,
    mul_nonneg (sq_nonneg delta) (sq_nonneg v),
    mul_nonneg (sq_nonneg z.re) (sq_nonneg r)]

/-- The Cauchy denominator at a safe point is nonzero for every genuine xi
zero. -/
theorem normSq_suzukiXiUpperEvaluationDenominator_pos
    {z : ℂ} (hz : 1 / 2 < z.im) (rho : NontrivialZetaZero) :
    0 < Complex.normSq
      (suzukiXiUpperEvaluationDenominator z
        (zetaSpectralCoordinate rho.1)) := by
  rw [normSq_suzukiXiUpperEvaluationDenominator]
  have hv : 0 < z.im - (zetaSpectralCoordinate rho.1).im :=
    (suzukiXiUpperEvaluationGap_pos hz).trans_le
      (spectral_gap_le_upperEvaluation_im_sub z rho)
  positivity

/-- The explicit upper-evaluation comparison constant is nonnegative. -/
theorem suzukiXiUpperEvaluationConstant_nonneg
    (z : ℂ) :
    0 ≤ suzukiXiUpperEvaluationConstant z := by
  unfold suzukiXiUpperEvaluationConstant
  exact div_nonneg (by positivity)
    (sq_nonneg (suzukiXiUpperEvaluationGap z))

/-- The conjugate Cauchy-evaluation coordinate at an arbitrary safe upper
point. -/
def zetaSuzukiUpperEvaluationFeature
    (z : ℂ) (rho : NontrivialZetaZero) : ℂ :=
  (Real.sqrt (analyticZetaZeroMultiplicity rho : ℝ) : ℂ) /
    starRingEnd ℂ
      (suzukiXiUpperEvaluationDenominator z
        (zetaSpectralCoordinate rho.1))

/-- The positive squared norm of an upper evaluation coordinate. -/
def zetaSuzukiUpperEvaluationEnergy
    (z : ℂ) (rho : NontrivialZetaZero) : ℝ :=
  (analyticZetaZeroMultiplicity rho : ℝ) /
    Complex.normSq
      (suzukiXiUpperEvaluationDenominator z
        (zetaSpectralCoordinate rho.1))

/-- The squared modulus of an upper-evaluation coordinate is its positive
energy. -/
theorem normSq_zetaSuzukiUpperEvaluationFeature
    (z : ℂ) (rho : NontrivialZetaZero) :
    Complex.normSq (zetaSuzukiUpperEvaluationFeature z rho) =
      zetaSuzukiUpperEvaluationEnergy z rho := by
  rw [zetaSuzukiUpperEvaluationFeature, Complex.normSq_div,
    Complex.normSq_ofReal, Complex.normSq_conj,
    Real.mul_self_sqrt (Nat.cast_nonneg _)]
  rfl

/-- Every safe upper-evaluation energy is nonnegative. -/
theorem zetaSuzukiUpperEvaluationEnergy_nonneg
    {z : ℂ} (hz : 1 / 2 < z.im) (rho : NontrivialZetaZero) :
    0 ≤ zetaSuzukiUpperEvaluationEnergy z rho := by
  unfold zetaSuzukiUpperEvaluationEnergy
  exact div_nonneg (Nat.cast_nonneg _)
    (normSq_suzukiXiUpperEvaluationDenominator_pos hz rho).le

/-- Upper-evaluation energy is controlled by the explicit point-dependent
constant times the inverse-square xi-divisor weight. -/
theorem zetaSuzukiUpperEvaluationEnergy_le_inverseSquare
    {z : ℂ} (hz : 1 / 2 < z.im) (rho : NontrivialZetaZero) :
    zetaSuzukiUpperEvaluationEnergy z rho ≤
      suzukiXiUpperEvaluationConstant z *
        ((analyticZetaZeroMultiplicity rho : ℝ) /
          (1 + (zetaSpectralCoordinate rho.1).re ^ 2)) := by
  let delta : ℝ := suzukiXiUpperEvaluationGap z
  let N : ℝ := 1 + 2 * z.re ^ 2 + 2 * delta ^ 2
  let m : ℝ := analyticZetaZeroMultiplicity rho
  let D : ℝ := Complex.normSq
    (suzukiXiUpperEvaluationDenominator z
      (zetaSpectralCoordinate rho.1))
  let Q : ℝ := 1 + (zetaSpectralCoordinate rho.1).re ^ 2
  have hdelta : 0 < delta := suzukiXiUpperEvaluationGap_pos hz
  have hdeltaSq : 0 < delta ^ 2 := sq_pos_of_pos hdelta
  have hm : 0 ≤ m := Nat.cast_nonneg _
  have hD : 0 < D :=
    normSq_suzukiXiUpperEvaluationDenominator_pos hz rho
  have hQ : 0 < Q := by
    dsimp [Q]
    positivity
  have hdomination : delta ^ 2 * Q ≤ N * D := by
    exact upperEvaluation_denominator_domination hz rho
  have hrecip : 1 / D ≤ N / (delta ^ 2 * Q) := by
    rw [div_le_div_iff₀ hD (mul_pos hdeltaSq hQ)]
    simpa only [one_mul] using hdomination
  change m / D ≤ (N / delta ^ 2) * (m / Q)
  calc
    m / D = m * (1 / D) := by ring
    _ ≤ m * (N / (delta ^ 2 * Q)) :=
      mul_le_mul_of_nonneg_left hrecip hm
    _ = (N / delta ^ 2) * (m / Q) := by
      field_simp [hdelta.ne', hQ.ne']

/-- The complete upper-evaluation energy is summable at every safe point. -/
theorem summable_zetaSuzukiUpperEvaluationEnergy
    {z : ℂ} (hz : 1 / 2 < z.im) :
    Summable (zetaSuzukiUpperEvaluationEnergy z) := by
  apply
    (summable_distinct_zetaZeroInverseSquareSpectralRe.mul_left
      (suzukiXiUpperEvaluationConstant z)).of_nonneg_of_le
      (zetaSuzukiUpperEvaluationEnergy_nonneg hz)
  exact zetaSuzukiUpperEvaluationEnergy_le_inverseSquare hz

/-- The upper-evaluation coordinates form a square-summable family. -/
theorem summable_norm_sq_zetaSuzukiUpperEvaluationFeature
    {z : ℂ} (hz : 1 / 2 < z.im) :
    Summable (fun rho : NontrivialZetaZero ↦
      ‖zetaSuzukiUpperEvaluationFeature z rho‖ ^ 2) := by
  simpa only [Complex.sq_norm,
    normSq_zetaSuzukiUpperEvaluationFeature] using
      summable_zetaSuzukiUpperEvaluationEnergy hz

/-- Evaluation at any point above the zero strip as a literal coefficient
space vector. -/
def riemannXiSuzukiUpperEvaluationVector
    (z : ℂ) (hz : 1 / 2 < z.im) :
    ℓ²(NontrivialZetaZero, ℂ) :=
  ⟨zetaSuzukiUpperEvaluationFeature z, by
    apply memℓp_gen
    simpa using summable_norm_sq_zetaSuzukiUpperEvaluationFeature hz⟩

/-- One term in Suzuki's upper-half-plane spectral `P_t(z)` expansion. -/
def zetaSuzukiSpectralPSummand
    (t : ℝ) (z : ℂ) (rho : NontrivialZetaZero) : ℂ :=
  (analyticZetaZeroMultiplicity rho : ℂ) *
    suzukiSpectralScrewCoefficient t
      (zetaSpectralCoordinate rho.1) /
        suzukiXiUpperEvaluationDenominator z
          (zetaSpectralCoordinate rho.1)

/-- Each upper-half-plane spectral summand is the coordinate Hilbert pairing
of its evaluation and coefficient features. -/
theorem zetaSuzukiSpectralPSummand_eq_inner
    (t : ℝ) (z : ℂ) (rho : NontrivialZetaZero) :
    zetaSuzukiSpectralPSummand t z rho =
      inner ℂ (zetaSuzukiUpperEvaluationFeature z rho)
        (zetaSuzukiSpectralCoefficientFeature t rho) := by
  rw [RCLike.inner_apply]
  unfold zetaSuzukiSpectralPSummand
    zetaSuzukiUpperEvaluationFeature
    zetaSuzukiSpectralCoefficientFeature
  simp [div_eq_mul_inv]
  have hsqrt :
      (Real.sqrt (analyticZetaZeroMultiplicity rho : ℝ) : ℂ) ^ 2 =
        (analyticZetaZeroMultiplicity rho : ℂ) := by
    norm_cast
    exact Real.sq_sqrt (Nat.cast_nonneg _)
  rw [← hsqrt]
  ring

/-- The spectral `P_t(z)` series is absolutely summable throughout Suzuki's
safe half-plane. -/
theorem summable_zetaSuzukiSpectralPSummand
    (t : ℝ) {z : ℂ} (hz : 1 / 2 < z.im) :
    Summable (zetaSuzukiSpectralPSummand t z) := by
  refine
    (lp.summable_inner (riemannXiSuzukiUpperEvaluationVector z hz)
      (riemannXiSuzukiSpectralCoefficientVector t)).congr ?_
  intro rho
  exact (zetaSuzukiSpectralPSummand_eq_inner t z rho).symm

/-- Suzuki's infinite spectral `P_t(z)` in the safe upper half-plane. The
definition is total, while convergence theorems carry the necessary
half-plane hypothesis explicitly. -/
def riemannXiSuzukiSpectralP (t : ℝ) (z : ℂ) : ℂ :=
  ∑' rho : NontrivialZetaZero,
    zetaSuzukiSpectralPSummand t z rho

/-- The infinite upper-half-plane spectral `P_t(z)` is an exact coefficient
space Hilbert pairing. -/
theorem riemannXiSuzukiSpectralP_eq_inner
    (t : ℝ) {z : ℂ} (hz : 1 / 2 < z.im) :
    riemannXiSuzukiSpectralP t z =
      inner ℂ (riemannXiSuzukiUpperEvaluationVector z hz)
        (riemannXiSuzukiSpectralCoefficientVector t) := by
  rw [riemannXiSuzukiSpectralP, lp.inner_eq_tsum]
  apply tsum_congr
  exact zetaSuzukiSpectralPSummand_eq_inner t z

/-- Genuine symmetric zero windows converge to `P_t(z)` at every safe upper
point. -/
theorem tendsto_suzukiXiSpectralPWindow
    (t : ℝ) {z : ℂ} (hz : 1 / 2 < z.im) :
    Tendsto (fun T : ℝ ↦ suzukiXiSpectralPWindow t T z) atTop
      (nhds (riemannXiSuzukiSpectralP t z)) := by
  have hsum := (summable_zetaSuzukiSpectralPSummand t hz).hasSum
  change Tendsto
    (fun T : ℝ ↦
      ∑ rho ∈ spectralZetaZeroWindow T,
        zetaSuzukiSpectralPSummand t z rho) atTop
      (nhds (riemannXiSuzukiSpectralP t z))
  unfold riemannXiSuzukiSpectralP
  exact hsum.comp tendsto_spectralZetaZeroWindow_atTop

/-- Cauchy--Schwarz controls every safe-half-plane spectral value. -/
theorem norm_riemannXiSuzukiSpectralP_le
    (t : ℝ) {z : ℂ} (hz : 1 / 2 < z.im) :
    ‖riemannXiSuzukiSpectralP t z‖ ≤
      ‖riemannXiSuzukiUpperEvaluationVector z hz‖ *
        ‖riemannXiSuzukiSpectralCoefficientVector t‖ := by
  rw [riemannXiSuzukiSpectralP_eq_inner t hz]
  exact norm_inner_le_norm _ _

/-- The general upper-half-plane construction specializes exactly to the
previous safe-point value at `z=i`. -/
theorem riemannXiSuzukiSpectralP_at_I (t : ℝ) :
    riemannXiSuzukiSpectralP t Complex.I =
      riemannXiSuzukiSpectralPAtI t := by
  apply tsum_congr
  intro rho
  rfl

/-- Every safe-half-plane spectral `P_0` vanishes. -/
@[simp] theorem riemannXiSuzukiSpectralP_zero_time (z : ℂ) :
    riemannXiSuzukiSpectralP 0 z = 0 := by
  unfold riemannXiSuzukiSpectralP zetaSuzukiSpectralPSummand
  simp

/-- The infinite spectral Suzuki signal obtained by applying the common theta
carrier to `P_t(z)`. -/
def riemannXiSuzukiSpectralSignal (t : ℝ) (z : ℂ) : ℂ :=
  suzukiXiZeroCarrier z * riemannXiSuzukiSpectralP t z

/-- One term of the carrier-weighted infinite spectral signal. -/
def zetaSuzukiSpectralSignalSummand
    (t : ℝ) (z : ℂ) (rho : NontrivialZetaZero) : ℂ :=
  suzukiXiZeroCarrier z * zetaSuzukiSpectralPSummand t z rho

/-- Each signal summand is exactly Suzuki's published coefficient times the
normalized zero-function quotient formula. -/
theorem zetaSuzukiSpectralSignalSummand_eq_zeroFunctionFormula
    (t : ℝ) (z : ℂ) (rho : NontrivialZetaZero) :
    zetaSuzukiSpectralSignalSummand t z rho =
      (suzukiXiZeroCoefficientAmplitude rho : ℂ) *
        suzukiSpectralScrewCoefficient t
          (zetaSpectralCoordinate rho.1) *
            suzukiXiZeroFunctionFormula rho z := by
  unfold zetaSuzukiSpectralSignalSummand
    zetaSuzukiSpectralPSummand suzukiXiZeroFunctionFormula
    suzukiXiUpperEvaluationDenominator
  have hnormalization :
      (suzukiXiZeroCoefficientAmplitude rho : ℂ) *
          (suzukiXiZeroNormalization rho : ℂ) =
        (analyticZetaZeroMultiplicity rho : ℂ) := by
    exact_mod_cast
      suzukiXiZeroCoefficientAmplitude_mul_normalization rho
  rw [← hnormalization]
  ring

/-- The complete signal summands are absolutely summable at every safe upper
point. -/
theorem summable_zetaSuzukiSpectralSignalSummand
    (t : ℝ) {z : ℂ} (hz : 1 / 2 < z.im) :
    Summable (zetaSuzukiSpectralSignalSummand t z) := by
  exact (summable_zetaSuzukiSpectralPSummand t hz).mul_left
    (suzukiXiZeroCarrier z)

/-- The infinite spectral signal has Suzuki's zero-function expansion (3.6)
throughout the safe upper half-plane. -/
theorem riemannXiSuzukiSpectralSignal_eq_tsum_zeroFunctionFormulas
    (t : ℝ) {z : ℂ} (_hz : 1 / 2 < z.im) :
    riemannXiSuzukiSpectralSignal t z =
      ∑' rho : NontrivialZetaZero,
        (suzukiXiZeroCoefficientAmplitude rho : ℂ) *
          suzukiSpectralScrewCoefficient t
            (zetaSpectralCoordinate rho.1) *
              suzukiXiZeroFunctionFormula rho z := by
  unfold riemannXiSuzukiSpectralSignal riemannXiSuzukiSpectralP
  rw [← tsum_mul_left]
  apply tsum_congr
  exact zetaSuzukiSpectralSignalSummand_eq_zeroFunctionFormula t z

/-- Finite spectral Suzuki signals converge pointwise to the infinite signal
at every safe upper point. -/
theorem tendsto_suzukiXiSignalWindow
    (t : ℝ) {z : ℂ} (hz : 1 / 2 < z.im) :
    Tendsto (fun T : ℝ ↦ suzukiXiSignalWindow t T z) atTop
      (nhds (riemannXiSuzukiSpectralSignal t z)) := by
  have hP := tendsto_suzukiXiSpectralPWindow t hz
  have hconst : Tendsto (fun _ : ℝ ↦ suzukiXiZeroCarrier z) atTop
      (nhds (suzukiXiZeroCarrier z)) := tendsto_const_nhds
  have hmul := hconst.mul hP
  simpa [suzukiXiSignalWindow,
    riemannXiSuzukiSpectralSignal] using hmul

/-- The complete spectral Suzuki signal starts at zero. -/
@[simp] theorem riemannXiSuzukiSpectralSignal_zero_time (z : ℂ) :
    riemannXiSuzukiSpectralSignal 0 z = 0 := by
  simp [riemannXiSuzukiSpectralSignal]

end

end RiemannGaussian
