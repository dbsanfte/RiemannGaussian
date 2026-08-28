import RiemannGaussian.RiemannXiSuzukiWeilVerticalLimit
import Mathlib.Analysis.Calculus.SmoothSeries

/-!
# Consequences of the closed Suzuki arithmetic--spectral meeting theorem

The global contour argument identifies Suzuki's arithmetic formula with its
complete spectral Cauchy transform throughout `Im z > 1/2`.  This file starts
transporting structures across that equality.

At `z = i`, the arithmetic expression is identified with the previously
constructed coefficient-space Hilbert pairing.  Spatial differentiation is
then transported across the identity.  A second, real-time differentiation
is justified term by term only after the spatial derivative has supplied a
square Cauchy denominator; the resulting inverse-square majorant is summable
unconditionally.  This avoids assuming convergence of the generally harder
undifferentiated raw screw series.
-/

open Complex Filter MeasureTheory Metric Polynomial Set Topology
open scoped Classical ENNReal Interval Topology lp

namespace RiemannGaussian

noncomputable section

/-- At the canonical safe point, Suzuki's arithmetic formula is exactly the
checked coefficient-space Hilbert pairing. -/
theorem riemannXiSuzukiArithmeticPPositive_at_I_eq_inner
    {t : ℝ} (ht : 0 < t) :
    riemannXiSuzukiArithmeticPPositive t Complex.I =
      inner ℂ riemannXiSuzukiSafeEvaluationVector
        (riemannXiSuzukiSpectralCoefficientVector t) := by
  rw [riemannXiSuzukiArithmeticPPositive_eq_spectral_safe ht
      (by simp [suzukiXiSafeUpperHalfPlane]; norm_num),
    riemannXiSuzukiSpectralP_at_I,
    riemannXiSuzukiSpectralPAtI_eq_inner]

/-- The arithmetic safe-point value inherits the exact spectral
Cauchy--Schwarz bound. -/
theorem norm_riemannXiSuzukiArithmeticPPositive_at_I_le
    {t : ℝ} (ht : 0 < t) :
    ‖riemannXiSuzukiArithmeticPPositive t Complex.I‖ ≤
      ‖riemannXiSuzukiSafeEvaluationVector‖ *
        ‖riemannXiSuzukiSpectralCoefficientVector t‖ := by
  rw [riemannXiSuzukiArithmeticPPositive_at_I_eq_inner ht]
  exact norm_inner_le_norm _ _

/-- Suzuki's carrier-weighted arithmetic signal after the arithmetic formula
has been identified with the spectral Cauchy transform. -/
def riemannXiSuzukiArithmeticSignalPositive
    (t : ℝ) (z : ℂ) : ℂ :=
  suzukiXiZeroCarrier z * riemannXiSuzukiArithmeticPPositive t z

/-- The complete arithmetic and spectral carrier-weighted signals agree on
Suzuki's safe half-plane. -/
theorem riemannXiSuzukiArithmeticSignalPositive_eq_spectral
    {t : ℝ} (ht : 0 < t) {z : ℂ}
    (hz : z ∈ suzukiXiSafeUpperHalfPlane) :
    riemannXiSuzukiArithmeticSignalPositive t z =
      riemannXiSuzukiSpectralSignal t z := by
  unfold riemannXiSuzukiArithmeticSignalPositive
    riemannXiSuzukiSpectralSignal
  rw [riemannXiSuzukiArithmeticPPositive_eq_spectral_safe ht hz]

/-- Pointwise in the safe half-plane, the arithmetic signal is the carrier
times the exact coefficient-space Hilbert pairing. -/
theorem riemannXiSuzukiArithmeticSignalPositive_eq_inner
    {t : ℝ} (ht : 0 < t) {z : ℂ}
    (hz : z ∈ suzukiXiSafeUpperHalfPlane) :
    riemannXiSuzukiArithmeticSignalPositive t z =
      suzukiXiZeroCarrier z *
        inner ℂ (riemannXiSuzukiUpperEvaluationVector z hz)
          (riemannXiSuzukiSpectralCoefficientVector t) := by
  rw [riemannXiSuzukiArithmeticSignalPositive_eq_spectral ht hz]
  unfold riemannXiSuzukiSpectralSignal
  rw [riemannXiSuzukiSpectralP_eq_inner t hz]

/-- The arithmetic signal inherits the pointwise coefficient-space
Cauchy--Schwarz bound. -/
theorem norm_riemannXiSuzukiArithmeticSignalPositive_le
    {t : ℝ} (ht : 0 < t) {z : ℂ}
    (hz : z ∈ suzukiXiSafeUpperHalfPlane) :
    ‖riemannXiSuzukiArithmeticSignalPositive t z‖ ≤
      ‖suzukiXiZeroCarrier z‖ *
        (‖riemannXiSuzukiUpperEvaluationVector z hz‖ *
          ‖riemannXiSuzukiSpectralCoefficientVector t‖) := by
  rw [riemannXiSuzukiArithmeticSignalPositive_eq_inner ht hz, norm_mul]
  exact mul_le_mul_of_nonneg_left (norm_inner_le_norm _ _)
    (norm_nonneg _)

/-- The normalized zero-function terms in the arithmetic signal are
absolutely summable at every safe point. -/
theorem summable_zetaSuzukiArithmeticZeroFunctionSummand
    (t : ℝ) {z : ℂ} (hz : z ∈ suzukiXiSafeUpperHalfPlane) :
    Summable (fun rho : NontrivialZetaZero ↦
      (suzukiXiZeroCoefficientAmplitude rho : ℂ) *
        suzukiSpectralScrewCoefficient t
          (zetaSpectralCoordinate rho.1) *
            suzukiXiZeroFunctionFormula rho z) := by
  refine (summable_zetaSuzukiSpectralSignalSummand t hz).congr ?_
  intro rho
  exact zetaSuzukiSpectralSignalSummand_eq_zeroFunctionFormula t z rho

/-- Suzuki's full normalized zero-function expansion `(3.6)` now holds for
the arithmetic signal throughout the safe half-plane. -/
theorem riemannXiSuzukiArithmeticSignalPositive_eq_tsum_zeroFunctionFormulas
    {t : ℝ} (ht : 0 < t) {z : ℂ}
    (hz : z ∈ suzukiXiSafeUpperHalfPlane) :
    riemannXiSuzukiArithmeticSignalPositive t z =
      ∑' rho : NontrivialZetaZero,
        (suzukiXiZeroCoefficientAmplitude rho : ℂ) *
          suzukiSpectralScrewCoefficient t
            (zetaSpectralCoordinate rho.1) *
              suzukiXiZeroFunctionFormula rho z := by
  rw [riemannXiSuzukiArithmeticSignalPositive_eq_spectral ht hz]
  exact riemannXiSuzukiSpectralSignal_eq_tsum_zeroFunctionFormulas t hz

/-- Genuine finite zero windows converge pointwise to the arithmetic signal,
not merely to a separately named spectral object. -/
theorem tendsto_suzukiXiSignalWindow_arithmetic
    {t : ℝ} (ht : 0 < t) {z : ℂ}
    (hz : z ∈ suzukiXiSafeUpperHalfPlane) :
    Tendsto (fun T : ℝ ↦ suzukiXiSignalWindow t T z) atTop
      (nhds (riemannXiSuzukiArithmeticSignalPositive t z)) := by
  rw [riemannXiSuzukiArithmeticSignalPositive_eq_spectral ht hz]
  exact tendsto_suzukiXiSignalWindow t hz

/-- Spatial derivatives of the arithmetic and spectral Suzuki functions
agree throughout the safe half-plane. -/
theorem deriv_riemannXiSuzukiArithmeticPPositive_eq_spectral
    {t : ℝ} (ht : 0 < t) {z : ℂ}
    (hz : z ∈ suzukiXiSafeUpperHalfPlane) :
    deriv (riemannXiSuzukiArithmeticPPositive t) z =
      deriv (riemannXiSuzukiSpectralP t) z := by
  apply Filter.EventuallyEq.deriv_eq
  exact eventuallyEq_of_mem
    (isOpen_suzukiXiSafeUpperHalfPlane.mem_nhds hz)
    (fun w hw ↦
      riemannXiSuzukiArithmeticPPositive_eq_spectral_safe ht hw)

/-- The spatial derivative of the arithmetic formula is the absolutely
convergent complete double-pole spectral series. -/
theorem deriv_riemannXiSuzukiArithmeticPPositive_eq_tsum
    {t : ℝ} (ht : 0 < t) {z : ℂ}
    (hz : z ∈ suzukiXiSafeUpperHalfPlane) :
    deriv (riemannXiSuzukiArithmeticPPositive t) z =
      ∑' rho : NontrivialZetaZero,
        zetaSuzukiSpectralPSpatialDerivativeSummand t z rho := by
  rw [deriv_riemannXiSuzukiArithmeticPPositive_eq_spectral ht hz,
    deriv_riemannXiSuzukiSpectralP_eq_tsum t hz]

/-- The mixed spatial/time derivative summand.  The spatial derivative has
created the square Cauchy denominator needed for unconditional summability. -/
def zetaSuzukiSpectralPSpatialTimeDerivativeSummand
    (t : ℝ) (z : ℂ) (rho : NontrivialZetaZero) : ℂ :=
  -((analyticZetaZeroMultiplicity rho : ℂ) *
      suzukiSpectralScrewCoefficientDerivative t
        (zetaSpectralCoordinate rho.1)) /
    (z - zetaSpectralCoordinate rho.1) ^ 2

/-- One spatial derivative summand has the asserted real-time derivative. -/
theorem hasDerivAt_zetaSuzukiSpectralPSpatialDerivativeSummand_time
    (t : ℝ) (z : ℂ) (rho : NontrivialZetaZero) :
    HasDerivAt
      (fun u : ℝ ↦
        zetaSuzukiSpectralPSpatialDerivativeSummand u z rho)
      (zetaSuzukiSpectralPSpatialTimeDerivativeSummand t z rho) t := by
  simpa [zetaSuzukiSpectralPSpatialDerivativeSummand,
    zetaSuzukiSpectralPSpatialTimeDerivativeSummand] using
      (((hasDerivAt_suzukiSpectralScrewCoefficient t
          (zetaSpectralCoordinate rho.1)).const_mul
            (analyticZetaZeroMultiplicity rho : ℂ)).neg.div_const
              ((z - zetaSpectralCoordinate rho.1) ^ 2))

/-- The norm of a mixed summand factors into the raw exponential rate and
the positive upper-evaluation energy. -/
theorem norm_zetaSuzukiSpectralPSpatialTimeDerivativeSummand
    (t : ℝ) (z : ℂ) (rho : NontrivialZetaZero) :
    ‖zetaSuzukiSpectralPSpatialTimeDerivativeSummand t z rho‖ =
      Real.exp ((zetaSpectralCoordinate rho.1).im * t) *
        zetaSuzukiUpperEvaluationEnergy z rho := by
  unfold zetaSuzukiSpectralPSpatialTimeDerivativeSummand
    zetaSuzukiUpperEvaluationEnergy
    suzukiXiUpperEvaluationDenominator
  rw [norm_div, norm_neg, norm_mul,
    norm_suzukiSpectralScrewCoefficientDerivative, norm_pow,
    ← Complex.sq_norm]
  simp only [norm_natCast]
  ring

/-- On a unit time neighborhood, every mixed summand is dominated by one
fixed multiple of the summable inverse-square xi-divisor weight. -/
theorem norm_zetaSuzukiSpectralPSpatialTimeDerivativeSummand_le
    (t : ℝ) {z : ℂ} (hz : 1 / 2 < z.im)
    (rho : NontrivialZetaZero) {u : ℝ}
    (hu : u ∈ Set.Ioo (t - 1) (t + 1)) :
    ‖zetaSuzukiSpectralPSpatialTimeDerivativeSummand u z rho‖ ≤
      (Real.exp ((|t| + 1) / 2) *
        suzukiXiUpperEvaluationConstant z) *
          ((analyticZetaZeroMultiplicity rho : ℝ) /
            (1 + (zetaSpectralCoordinate rho.1).re ^ 2)) := by
  have huabs : |u| ≤ |t| + 1 := by
    rw [abs_le]
    constructor
    · linarith [hu.1, neg_le_abs t]
    · linarith [hu.2, le_abs_self t]
  have hstrip :=
    NontrivialZetaZero.abs_spectralCoordinate_im_lt_half rho
  have hexponent :
      (zetaSpectralCoordinate rho.1).im * u ≤ (|t| + 1) / 2 := by
    calc
      (zetaSpectralCoordinate rho.1).im * u ≤
          |(zetaSpectralCoordinate rho.1).im * u| := le_abs_self _
      _ = |(zetaSpectralCoordinate rho.1).im| * |u| := abs_mul _ _
      _ ≤ (1 / 2) * (|t| + 1) :=
        mul_le_mul hstrip.le huabs (abs_nonneg _) (by norm_num)
      _ = (|t| + 1) / 2 := by ring
  have hexp :
      Real.exp ((zetaSpectralCoordinate rho.1).im * u) ≤
        Real.exp ((|t| + 1) / 2) :=
    Real.exp_le_exp.mpr hexponent
  have henergy := zetaSuzukiUpperEvaluationEnergy_le_inverseSquare hz rho
  rw [norm_zetaSuzukiSpectralPSpatialTimeDerivativeSummand]
  calc
    Real.exp ((zetaSpectralCoordinate rho.1).im * u) *
        zetaSuzukiUpperEvaluationEnergy z rho ≤
      Real.exp ((|t| + 1) / 2) *
        (suzukiXiUpperEvaluationConstant z *
          ((analyticZetaZeroMultiplicity rho : ℝ) /
            (1 + (zetaSpectralCoordinate rho.1).re ^ 2))) :=
      mul_le_mul hexp henergy
        (zetaSuzukiUpperEvaluationEnergy_nonneg hz rho) (by positivity)
    _ = (Real.exp ((|t| + 1) / 2) *
        suzukiXiUpperEvaluationConstant z) *
          ((analyticZetaZeroMultiplicity rho : ℝ) /
            (1 + (zetaSpectralCoordinate rho.1).re ^ 2)) := by ring

/-- The complete mixed-derivative spectral series is absolutely summable at
every real time and every safe evaluation point. -/
theorem summable_zetaSuzukiSpectralPSpatialTimeDerivativeSummand
    (t : ℝ) {z : ℂ} (hz : 1 / 2 < z.im) :
    Summable (zetaSuzukiSpectralPSpatialTimeDerivativeSummand t z) := by
  have hmajor : Summable (fun rho : NontrivialZetaZero ↦
      (Real.exp ((|t| + 1) / 2) *
        suzukiXiUpperEvaluationConstant z) *
          ((analyticZetaZeroMultiplicity rho : ℝ) /
            (1 + (zetaSpectralCoordinate rho.1).re ^ 2))) :=
    summable_distinct_zetaZeroInverseSquareSpectralRe.mul_left
      (Real.exp ((|t| + 1) / 2) *
        suzukiXiUpperEvaluationConstant z)
  apply hmajor.of_norm_bounded
  intro rho
  exact norm_zetaSuzukiSpectralPSpatialTimeDerivativeSummand_le
    t hz rho (by constructor <;> linarith)

/-- After one spatial derivative, real-time differentiation passes through
the complete spectral series.  No convergence of the undifferentiated raw
screw series is assumed. -/
theorem hasDerivAt_deriv_riemannXiSuzukiSpectralP_time
    (t : ℝ) {z : ℂ} (hz : z ∈ suzukiXiSafeUpperHalfPlane) :
    HasDerivAt
      (fun u : ℝ ↦ deriv (riemannXiSuzukiSpectralP u) z)
      (∑' rho : NontrivialZetaZero,
        zetaSuzukiSpectralPSpatialTimeDerivativeSummand t z rho) t := by
  have hz' : 1 / 2 < z.im := hz
  have hmajor : Summable (fun rho : NontrivialZetaZero ↦
      (Real.exp ((|t| + 1) / 2) *
        suzukiXiUpperEvaluationConstant z) *
          ((analyticZetaZeroMultiplicity rho : ℝ) /
            (1 + (zetaSpectralCoordinate rho.1).re ^ 2))) :=
    summable_distinct_zetaZeroInverseSquareSpectralRe.mul_left
      (Real.exp ((|t| + 1) / 2) *
        suzukiXiUpperEvaluationConstant z)
  have hbase : Summable (fun rho : NontrivialZetaZero ↦
      zetaSuzukiSpectralPSpatialDerivativeSummand t z rho) :=
    (hasSum_zetaSuzukiSpectralPSpatialDerivativeSummand t hz).summable
  have htmem : t ∈ Set.Ioo (t - 1) (t + 1) := by
    constructor <;> linarith
  have hraw : HasDerivAt
      (fun u : ℝ ↦ ∑' rho : NontrivialZetaZero,
        zetaSuzukiSpectralPSpatialDerivativeSummand u z rho)
      (∑' rho : NontrivialZetaZero,
        zetaSuzukiSpectralPSpatialTimeDerivativeSummand t z rho) t := by
    refine hasDerivAt_tsum_of_isPreconnected
      (t := Set.Ioo (t - 1) (t + 1))
      (g := fun rho u ↦
        zetaSuzukiSpectralPSpatialDerivativeSummand u z rho)
      (g' := fun rho u ↦
        zetaSuzukiSpectralPSpatialTimeDerivativeSummand u z rho)
      (y₀ := t) (y := t)
      hmajor isOpen_Ioo isPreconnected_Ioo ?_ ?_ htmem hbase htmem
    · intro rho u _hu
      exact
        hasDerivAt_zetaSuzukiSpectralPSpatialDerivativeSummand_time
          u z rho
    · intro rho u hu
      exact norm_zetaSuzukiSpectralPSpatialTimeDerivativeSummand_le
        t hz' rho hu
  apply hraw.congr_of_eventuallyEq
  exact Eventually.of_forall fun u ↦
    deriv_riemannXiSuzukiSpectralP_eq_tsum u hz

/-- The arithmetic formula inherits the same mixed spatial/time derivative
throughout positive screw time and the complete safe half-plane. -/
theorem hasDerivAt_deriv_riemannXiSuzukiArithmeticPPositive_time
    {t : ℝ} (ht : 0 < t) {z : ℂ}
    (hz : z ∈ suzukiXiSafeUpperHalfPlane) :
    HasDerivAt
      (fun u : ℝ ↦ deriv (riemannXiSuzukiArithmeticPPositive u) z)
      (∑' rho : NontrivialZetaZero,
        zetaSuzukiSpectralPSpatialTimeDerivativeSummand t z rho) t := by
  apply (hasDerivAt_deriv_riemannXiSuzukiSpectralP_time t hz).congr_of_eventuallyEq
  exact eventuallyEq_of_mem (Ioi_mem_nhds ht) fun u hu ↦
    deriv_riemannXiSuzukiArithmeticPPositive_eq_spectral hu hz

/-- At `z = i`, the mixed derivative is a square-resolvent raw screw
summand. -/
def zetaSuzukiResolventSquareRawDerivativeSummand
    (t : ℝ) (rho : NontrivialZetaZero) : ℂ :=
  (analyticZetaZeroMultiplicity rho : ℂ) *
      suzukiSpectralScrewCoefficientDerivative t
        (zetaSpectralCoordinate rho.1) /
    spectralScrewResolventDenominator
      (zetaSpectralCoordinate rho.1) ^ 2

/-- The unit factor relating the safe Cauchy denominator to Suzuki's
resolvent cancels the minus sign of the spatial derivative. -/
theorem zetaSuzukiSpectralPSpatialTimeDerivativeSummand_at_I
    (t : ℝ) (rho : NontrivialZetaZero) :
    zetaSuzukiSpectralPSpatialTimeDerivativeSummand t Complex.I rho =
      zetaSuzukiResolventSquareRawDerivativeSummand t rho := by
  change
    -((analyticZetaZeroMultiplicity rho : ℂ) *
        suzukiSpectralScrewCoefficientDerivative t
          (zetaSpectralCoordinate rho.1)) /
        suzukiXiSafeEvaluationDenominator
          (zetaSpectralCoordinate rho.1) ^ 2 = _
  rw [suzukiXiSafeEvaluationDenominator_eq_resolvent]
  unfold zetaSuzukiResolventSquareRawDerivativeSummand
  rw [mul_pow, Complex.I_sq]
  ring

/-- The complete square-resolvent raw screw series is absolutely summable. -/
theorem summable_zetaSuzukiResolventSquareRawDerivativeSummand
    (t : ℝ) :
    Summable (zetaSuzukiResolventSquareRawDerivativeSummand t) := by
  refine
    (summable_zetaSuzukiSpectralPSpatialTimeDerivativeSummand t
      (z := Complex.I)
      (by norm_num)).congr ?_
  intro rho
  exact zetaSuzukiSpectralPSpatialTimeDerivativeSummand_at_I t rho

/-- At the canonical Hilbert evaluation point, the time derivative of the
arithmetic spatial derivative is the complete square-resolvent raw screw
series. -/
theorem hasDerivAt_deriv_riemannXiSuzukiArithmeticPPositive_at_I_time
    {t : ℝ} (ht : 0 < t) :
    HasDerivAt
      (fun u : ℝ ↦
        deriv (riemannXiSuzukiArithmeticPPositive u) Complex.I)
      (∑' rho : NontrivialZetaZero,
        zetaSuzukiResolventSquareRawDerivativeSummand t rho) t := by
  have hz : Complex.I ∈ suzukiXiSafeUpperHalfPlane := by
    simp [suzukiXiSafeUpperHalfPlane]
    norm_num
  have h :=
    hasDerivAt_deriv_riemannXiSuzukiArithmeticPPositive_time ht hz
  have hsum :
      (∑' rho : NontrivialZetaZero,
          zetaSuzukiSpectralPSpatialTimeDerivativeSummand
            t Complex.I rho) =
        ∑' rho : NontrivialZetaZero,
          zetaSuzukiResolventSquareRawDerivativeSummand t rho :=
    tsum_congr (zetaSuzukiSpectralPSpatialTimeDerivativeSummand_at_I t)
  rw [hsum] at h
  exact h

end

end RiemannGaussian
