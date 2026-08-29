import RiemannGaussian.RiemannXiSuzukiPositiveCriticalStripEtaLeadingLogMomentGapComparison
import RiemannGaussian.RiemannXiSuzukiPositiveCriticalStripEtaHorizontalDefectGapFinite

/-!
# Finite phase-sensitive lower bounds for leading eta moments

The first-gap estimate bounds a leading eta defect from above by discarding
its oscillatory phase.  Here the actual complex phase is retained.  For every
cutoff `N`, the complete support moment is split exactly into its first `N`
arithmetic intervals and the literal support tail beginning at
`log (2N+1)`.

For `0 < theta < 1`, exponential splitting gives the uniform tail estimate

`exp (-(1-theta) * sigma * log (2N+1)) * k! / (theta*sigma)^(k+1)`.

Consequently the norm of the finite complex prefix, minus this explicit
tail, is a rigorous lower bound for the complete moment.  At a nontrivial
zeta zero this is a finite, phase-sensitive lower certificate for the exact
nonzero leading gap defect.  Combining it with completed partner symmetry
produces necessary complementary inequalities for every cutoff.  No claim
that those inequalities already exclude an off-critical zero is made.
-/

open Complex Filter MeasureTheory Metric Set Topology
open scoped Classical ComplexConjugate ENNReal Interval Topology

namespace RiemannGaussian

noncomputable section

/-- The order-`k` logarithmic moment on one retained eta support interval. -/
def pairedEtaLogLaplaceMomentInterval
    (k : ℕ) (s : ℂ) (n : ℕ) : ℂ :=
  ∫ t : ℝ in Real.log (2 * n + 1)..Real.log (2 * n + 2),
    (t : ℂ) ^ k * Complex.exp (-s * t)

/-- The first `N` explicit support-interval moments, retaining their complex
phases before taking a norm. -/
def pairedEtaLogLaplaceMomentPartialSum
    (k : ℕ) (s : ℂ) (N : ℕ) : ℂ :=
  ∑ n ∈ Finset.range N, pairedEtaLogLaplaceMomentInterval k s n

/-- Support-interval moments are absolutely summable throughout the positive
half-plane. -/
theorem summable_pairedEtaLogLaplaceMomentInterval
    (k : ℕ) {s : ℂ} (hs : 0 < s.re) :
    Summable (pairedEtaLogLaplaceMomentInterval k s) := by
  have hint := integrable_pairedEtaLogLaplaceMoment k hs
  rw [pairedEtaLogMeasure_eq_sum_restrict] at hint
  have hnorm := hint.summable_integral
  apply hnorm.of_norm_bounded
  intro n
  unfold pairedEtaLogLaplaceMomentInterval pairedEtaLogInterval
  rw [intervalIntegral.integral_of_le
    (pairedEtaFiniteLogInterval_pos n).le]
  exact norm_integral_le_integral_norm _

/-- The complete eta-support moment is the absolutely convergent sum of its
literal support-interval moments. -/
theorem pairedEtaLogLaplaceMoment_eq_tsum_interval
    (k : ℕ) {s : ℂ} (hs : 0 < s.re) :
    pairedEtaLogLaplaceMoment k s =
      ∑' n : ℕ, pairedEtaLogLaplaceMomentInterval k s n := by
  have hint := integrable_pairedEtaLogLaplaceMoment k hs
  rw [pairedEtaLogMeasure_eq_sum_restrict] at hint
  unfold pairedEtaLogLaplaceMoment
  rw [pairedEtaLogMeasure_eq_sum_restrict, integral_sum_measure hint]
  apply tsum_congr
  intro n
  unfold pairedEtaLogLaplaceMomentInterval pairedEtaLogInterval
  exact (intervalIntegral.integral_of_le
    (pairedEtaFiniteLogInterval_pos n).le).symm

/-- Every shifted eta support tail is measurable. -/
theorem measurableSet_pairedEtaLogTailSupport (N : ℕ) :
    MeasurableSet (pairedEtaLogTailSupport N) := by
  unfold pairedEtaLogTailSupport pairedEtaLogInterval
  exact MeasurableSet.iUnion fun _ ↦ measurableSet_Ioc

/-- Every complex logarithmic moment is integrable on an eta support tail. -/
theorem integrable_pairedEtaLogLaplaceMoment_tail
    (k : ℕ) {s : ℂ} (hs : 0 < s.re) (N : ℕ) :
    Integrable (fun t : ℝ ↦
      (t : ℂ) ^ k * Complex.exp (-s * t))
      (pairedEtaLogTailMeasure N) := by
  have hlog : 0 ≤ Real.log (2 * N + 1) := by
    apply Real.log_nonneg
    norm_num
  have hmeasure : pairedEtaLogTailMeasure N ≤
      volume.restrict (Ioi 0) :=
    (pairedEtaLogTailMeasure_le_restrict_Ioi_log_odd N).trans
      (Measure.restrict_mono (Ioi_subset_Ioi hlog) le_rfl)
  exact Integrable.mono_measure
    (integrable_positiveHalfLineLogLaplaceMoment k hs) hmeasure

/-- Integrating an order-`k` moment over the support tail is the shifted
infinite sum of the corresponding interval moments. -/
theorem integral_pairedEtaLogLaplaceMoment_tail_eq_tsum_natAdd
    (k : ℕ) {s : ℂ} (hs : 0 < s.re) (N : ℕ) :
    (∫ t : ℝ, (t : ℂ) ^ k * Complex.exp (-s * t)
      ∂pairedEtaLogTailMeasure N) =
      ∑' n : ℕ, pairedEtaLogLaplaceMomentInterval k s (n + N) := by
  have hint := integrable_pairedEtaLogLaplaceMoment_tail k hs N
  rw [pairedEtaLogTailMeasure_eq_sum_restrict] at hint
  rw [pairedEtaLogTailMeasure_eq_sum_restrict,
    integral_sum_measure hint]
  apply tsum_congr
  intro n
  unfold pairedEtaLogLaplaceMomentInterval pairedEtaLogInterval
  exact (intervalIntegral.integral_of_le
    (pairedEtaFiniteLogInterval_pos (n + N)).le).symm

/-- The complete complex moment splits exactly into its finite arithmetic
prefix and its literal support tail. -/
theorem pairedEtaLogLaplaceMoment_eq_partialSum_add_tail
    (k : ℕ) {s : ℂ} (hs : 0 < s.re) (N : ℕ) :
    pairedEtaLogLaplaceMoment k s =
      pairedEtaLogLaplaceMomentPartialSum k s N +
        ∫ t : ℝ, (t : ℂ) ^ k * Complex.exp (-s * t)
          ∂pairedEtaLogTailMeasure N := by
  have hsplit :=
    (summable_pairedEtaLogLaplaceMomentInterval k hs).sum_add_tsum_nat_add N
  rw [pairedEtaLogLaplaceMoment_eq_tsum_interval k hs,
    integral_pairedEtaLogLaplaceMoment_tail_eq_tsum_natAdd k hs]
  exact hsplit.symm

/-- The explicit exponentially decaying upper envelope for an order-`k`
support tail after splitting the real exponential rate by `theta`. -/
def pairedEtaLogLaplaceMomentTailUpper
    (k : ℕ) (sigma theta : ℝ) (N : ℕ) : ℝ :=
  Real.exp (-(1 - theta) * sigma * Real.log (2 * N + 1)) *
    ((k.factorial : ℝ) / (theta * sigma) ^ (k + 1))

/-- The phase-independent norm of the literal support tail is bounded by the
explicit split-rate envelope. -/
theorem norm_integral_pairedEtaLogLaplaceMoment_tail_le
    (k : ℕ) {s : ℂ} (hs : 0 < s.re) {theta : ℝ}
    (htheta : 0 < theta) (hthetaOne : theta < 1) (N : ℕ) :
    ‖∫ t : ℝ, (t : ℂ) ^ k * Complex.exp (-s * t)
        ∂pairedEtaLogTailMeasure N‖ ≤
      pairedEtaLogLaplaceMomentTailUpper k s.re theta N := by
  let a : ℝ := Real.log (2 * N + 1)
  let sigma : ℝ := s.re
  let rate : ℝ := theta * sigma
  let reserve : ℝ := (1 - theta) * sigma
  let f : ℝ → ℝ := fun t ↦ t ^ k * Real.exp (-sigma * t)
  let g : ℝ → ℝ := fun t ↦ t ^ k * Real.exp (-rate * t)
  have ha : 0 ≤ a := by
    dsimp [a]
    apply Real.log_nonneg
    norm_num
  have hsigma : 0 < sigma := hs
  have hrate : 0 < rate := mul_pos htheta hsigma
  have hreserve : 0 < reserve := mul_pos (sub_pos.mpr hthetaOne) hsigma
  have hfullF : Integrable f (volume.restrict (Ioi 0)) := by
    exact integrableOn_pow_mul_exp_neg_mul_Ioi_zero_nat k hsigma
  have hfullG : Integrable g (volume.restrict (Ioi 0)) := by
    exact integrableOn_pow_mul_exp_neg_mul_Ioi_zero_nat k hrate
  have htailF : Integrable f (volume.restrict (Ioi a)) :=
    Integrable.mono_measure hfullF
      (Measure.restrict_mono (Ioi_subset_Ioi ha) le_rfl)
  have htailG : Integrable g (volume.restrict (Ioi a)) :=
    Integrable.mono_measure hfullG
      (Measure.restrict_mono (Ioi_subset_Ioi ha) le_rfl)
  have hmeasure : pairedEtaLogTailMeasure N ≤
      volume.restrict (Ioi a) := by
    simpa [a] using pairedEtaLogTailMeasure_le_restrict_Ioi_log_odd N
  have hnorm :
      ‖∫ t : ℝ, (t : ℂ) ^ k * Complex.exp (-s * t)
          ∂pairedEtaLogTailMeasure N‖ ≤
        ∫ t : ℝ, f t ∂pairedEtaLogTailMeasure N := by
    calc
      ‖∫ t : ℝ, (t : ℂ) ^ k * Complex.exp (-s * t)
            ∂pairedEtaLogTailMeasure N‖ ≤
          ∫ t : ℝ,
            ‖(t : ℂ) ^ k * Complex.exp (-s * t)‖
              ∂pairedEtaLogTailMeasure N :=
        norm_integral_le_integral_norm _
      _ = ∫ t : ℝ, f t ∂pairedEtaLogTailMeasure N := by
        apply integral_congr_ae
        filter_upwards
          [ae_restrict_mem (measurableSet_pairedEtaLogTailSupport N)]
            with t ht
        have hta : a < t := by
          simpa [a] using
            (pairedEtaLogTailSupport_subset_Ioi_log_odd N ht)
        have htpos : 0 < t := ha.trans_lt hta
        rw [norm_mul, norm_pow, norm_real, Complex.norm_exp]
        norm_num [f, sigma, Complex.mul_re, abs_of_nonneg htpos.le]
  have hnonnegF : ∀ᵐ t ∂volume.restrict (Ioi a), 0 ≤ f t := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    exact mul_nonneg (pow_nonneg (ha.trans ht.le) k)
      (Real.exp_pos _).le
  have htoIoi :
      (∫ t : ℝ, f t ∂pairedEtaLogTailMeasure N) ≤
        ∫ t : ℝ in Ioi a, f t :=
    integral_mono_measure hmeasure hnonnegF htailF
  have hpointwise : ∀ t ∈ Ioi a,
      f t ≤ Real.exp (-reserve * a) * g t := by
    intro t ht
    have htNonneg : 0 ≤ t := ha.trans ht.le
    have harg : -reserve * t ≤ -reserve * a :=
      mul_le_mul_of_nonpos_left ht.le (neg_nonpos.mpr hreserve.le)
    have hexp : Real.exp (-sigma * t) ≤
        Real.exp (-reserve * a) * Real.exp (-rate * t) := by
      calc
        Real.exp (-sigma * t) =
            Real.exp (-reserve * t) * Real.exp (-rate * t) := by
          rw [← Real.exp_add]
          congr 1
          dsimp [reserve, rate, sigma]
          ring
        _ ≤ Real.exp (-reserve * a) * Real.exp (-rate * t) :=
          mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr harg)
            (Real.exp_pos _).le
    calc
      f t = t ^ k * Real.exp (-sigma * t) := rfl
      _ ≤ t ^ k *
          (Real.exp (-reserve * a) * Real.exp (-rate * t)) :=
        mul_le_mul_of_nonneg_left hexp (pow_nonneg htNonneg k)
      _ = Real.exp (-reserve * a) * g t := by
        dsimp [g]
        ring
  have hsplitIntegral :
      (∫ t : ℝ in Ioi a, f t) ≤
        Real.exp (-reserve * a) * ∫ t : ℝ in Ioi a, g t := by
    calc
      (∫ t : ℝ in Ioi a, f t) ≤
          ∫ t : ℝ in Ioi a, Real.exp (-reserve * a) * g t := by
        apply integral_mono_ae htailF
          (htailG.const_mul (Real.exp (-reserve * a)))
        filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
        exact hpointwise t ht
      _ = Real.exp (-reserve * a) * ∫ t : ℝ in Ioi a, g t := by
        rw [integral_const_mul]
  have hnonnegG : ∀ᵐ t ∂volume.restrict (Ioi 0), 0 ≤ g t := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    exact mul_nonneg (pow_nonneg ht.le k)
      (Real.exp_pos _).le
  have htailToFull :
      (∫ t : ℝ in Ioi a, g t) ≤ ∫ t : ℝ in Ioi 0, g t := by
    exact integral_mono_measure
      (Measure.restrict_mono (Ioi_subset_Ioi ha) le_rfl)
      hnonnegG hfullG
  calc
    ‖∫ t : ℝ, (t : ℂ) ^ k * Complex.exp (-s * t)
          ∂pairedEtaLogTailMeasure N‖ ≤
        ∫ t : ℝ, f t ∂pairedEtaLogTailMeasure N := hnorm
    _ ≤ ∫ t : ℝ in Ioi a, f t := htoIoi
    _ ≤ Real.exp (-reserve * a) * ∫ t : ℝ in Ioi a, g t :=
      hsplitIntegral
    _ ≤ Real.exp (-reserve * a) * ∫ t : ℝ in Ioi 0, g t :=
      mul_le_mul_of_nonneg_left htailToFull (Real.exp_pos _).le
    _ = pairedEtaLogLaplaceMomentTailUpper k s.re theta N := by
      rw [← positiveHalfLineRealLogLaplaceMoment,
        positiveHalfLineRealLogLaplaceMoment_eq_factorial k hrate]
      unfold pairedEtaLogLaplaceMomentTailUpper
      dsimp [a, sigma, rate, reserve]
      congr 1
      ring_nf

/-- The split-rate tail envelope is strictly positive for every admissible
positive tilt and split parameter. -/
theorem pairedEtaLogLaplaceMomentTailUpper_pos
    (k : ℕ) {sigma theta : ℝ} (hsigma : 0 < sigma)
    (htheta : 0 < theta) (N : ℕ) :
    0 < pairedEtaLogLaplaceMomentTailUpper k sigma theta N := by
  unfold pairedEtaLogLaplaceMomentTailUpper
  have hrate : 0 < theta * sigma := mul_pos htheta hsigma
  positivity

/-- The finite complex prefix approximates the complete support moment with
the explicit split-rate tail error. -/
theorem norm_pairedEtaLogLaplaceMomentPartialSum_sub_le_tailUpper
    (k : ℕ) {s : ℂ} (hs : 0 < s.re) {theta : ℝ}
    (htheta : 0 < theta) (hthetaOne : theta < 1) (N : ℕ) :
    ‖pairedEtaLogLaplaceMomentPartialSum k s N -
        pairedEtaLogLaplaceMoment k s‖ ≤
      pairedEtaLogLaplaceMomentTailUpper k s.re theta N := by
  have hsplit := pairedEtaLogLaplaceMoment_eq_partialSum_add_tail k hs N
  calc
    ‖pairedEtaLogLaplaceMomentPartialSum k s N -
          pairedEtaLogLaplaceMoment k s‖ =
        ‖-(∫ t : ℝ, (t : ℂ) ^ k * Complex.exp (-s * t)
          ∂pairedEtaLogTailMeasure N)‖ := by
      rw [hsplit]
      congr 1
      ring
    _ = ‖∫ t : ℝ, (t : ℂ) ^ k * Complex.exp (-s * t)
          ∂pairedEtaLogTailMeasure N‖ := norm_neg _
    _ ≤ pairedEtaLogLaplaceMomentTailUpper k s.re theta N :=
      norm_integral_pairedEtaLogLaplaceMoment_tail_le
        k hs htheta hthetaOne N

/-- Hence the finite prefix norm approximates the complete moment norm with
the same explicit error. -/
theorem abs_norm_pairedEtaLogLaplaceMomentPartialSum_sub_norm_le_tailUpper
    (k : ℕ) {s : ℂ} (hs : 0 < s.re) {theta : ℝ}
    (htheta : 0 < theta) (hthetaOne : theta < 1) (N : ℕ) :
    |‖pairedEtaLogLaplaceMomentPartialSum k s N‖ -
        ‖pairedEtaLogLaplaceMoment k s‖| ≤
      pairedEtaLogLaplaceMomentTailUpper k s.re theta N := by
  exact (abs_norm_sub_norm_le
    (pairedEtaLogLaplaceMomentPartialSum k s N)
    (pairedEtaLogLaplaceMoment k s)).trans
      (norm_pairedEtaLogLaplaceMomentPartialSum_sub_le_tailUpper
        k hs htheta hthetaOne N)

/-- The nonnegative finite, phase-sensitive lower certificate obtained from
one complex prefix and its rigorous tail envelope. -/
def pairedEtaLogLaplaceMomentFiniteLower
    (k : ℕ) (s : ℂ) (theta : ℝ) (N : ℕ) : ℝ :=
  max 0 (‖pairedEtaLogLaplaceMomentPartialSum k s N‖ -
    pairedEtaLogLaplaceMomentTailUpper k s.re theta N)

/-- Every admissible finite lower certificate lies below the norm of the
complete complex support moment. -/
theorem pairedEtaLogLaplaceMomentFiniteLower_le_norm
    (k : ℕ) {s : ℂ} (hs : 0 < s.re) {theta : ℝ}
    (htheta : 0 < theta) (hthetaOne : theta < 1) (N : ℕ) :
    pairedEtaLogLaplaceMomentFiniteLower k s theta N ≤
      ‖pairedEtaLogLaplaceMoment k s‖ := by
  unfold pairedEtaLogLaplaceMomentFiniteLower
  apply max_le
  · exact norm_nonneg _
  · have hreverse := norm_sub_norm_le
      (pairedEtaLogLaplaceMomentPartialSum k s N)
      (pairedEtaLogLaplaceMoment k s)
    have htail :=
      norm_pairedEtaLogLaplaceMomentPartialSum_sub_le_tailUpper
        k hs htheta hthetaOne N
    linarith

/-- At a nontrivial zero, the finite certificate bounds the exact nonzero
leading gap-moment defect from below. -/
theorem pairedEtaLeadingLogGapMomentFiniteLower_le_norm_defect
    (rho : NontrivialZetaZero) {theta : ℝ}
    (htheta : 0 < theta) (hthetaOne : theta < 1) (N : ℕ) :
    pairedEtaLogLaplaceMomentFiniteLower
        (analyticZetaZeroMultiplicity rho) rho.1 theta N ≤
      ‖pairedEtaLeadingLogGapMomentDefect rho‖ := by
  rw [pairedEtaLeadingLogGapMomentDefect_eq_logLaplaceMoment]
  exact pairedEtaLogLaplaceMomentFiniteLower_le_norm
    (analyticZetaZeroMultiplicity rho)
    (NontrivialZetaZero.zero_lt_re rho) htheta hthetaOne N

/-- Each finite phase-sensitive lower certificate at `rho` is constrained by
the explicit first-gap upper envelope at the complementary zero. -/
theorem pairedEtaCompletedLeadingLogFiniteLower_le_complementaryUpper
    (rho : NontrivialZetaZero) {theta : ℝ}
    (htheta : 0 < theta) (hthetaOne : theta < 1) (N : ℕ) :
    pairedEtaCompletionSpectralWeight rho *
        pairedEtaLogLaplaceMomentFiniteLower
          (analyticZetaZeroMultiplicity rho) rho.1 theta N ≤
      pairedEtaCompletionSpectralWeight
          (NontrivialZetaZero.conjugatePartner rho) *
        pairedEtaLeadingLogGapMomentDefectUpper
          (analyticZetaZeroMultiplicity rho) (1 - rho.1.re) := by
  calc
    pairedEtaCompletionSpectralWeight rho *
          pairedEtaLogLaplaceMomentFiniteLower
            (analyticZetaZeroMultiplicity rho) rho.1 theta N ≤
        pairedEtaCompletionSpectralWeight rho *
          ‖pairedEtaLeadingLogGapMomentDefect rho‖ :=
      mul_le_mul_of_nonneg_left
        (pairedEtaLeadingLogGapMomentFiniteLower_le_norm_defect
          rho htheta hthetaOne N)
        (pairedEtaCompletionSpectralWeight_pos rho).le
    _ = pairedEtaCompletedLeadingLogGapMomentMagnitude rho := rfl
    _ ≤ pairedEtaCompletionSpectralWeight
          (NontrivialZetaZero.conjugatePartner rho) *
        pairedEtaLeadingLogGapMomentDefectUpper
          (analyticZetaZeroMultiplicity rho) (1 - rho.1.re) :=
      (pairedEtaCompletedLeadingLogGapMomentMagnitude_le_both_tilts rho).2

/-- The finite lower versus first-gap upper constraint holds in both
directions across every complementary pair. -/
theorem pairedEtaCompletedLeadingLogFiniteLower_le_both_complementaryUpper
    (rho : NontrivialZetaZero) {theta : ℝ}
    (htheta : 0 < theta) (hthetaOne : theta < 1) (N : ℕ) :
    (pairedEtaCompletionSpectralWeight rho *
          pairedEtaLogLaplaceMomentFiniteLower
            (analyticZetaZeroMultiplicity rho) rho.1 theta N ≤
        pairedEtaCompletionSpectralWeight
            (NontrivialZetaZero.conjugatePartner rho) *
          pairedEtaLeadingLogGapMomentDefectUpper
            (analyticZetaZeroMultiplicity rho) (1 - rho.1.re)) ∧
      (pairedEtaCompletionSpectralWeight
            (NontrivialZetaZero.conjugatePartner rho) *
          pairedEtaLogLaplaceMomentFiniteLower
            (analyticZetaZeroMultiplicity rho)
            (NontrivialZetaZero.conjugatePartner rho).1 theta N ≤
        pairedEtaCompletionSpectralWeight rho *
          pairedEtaLeadingLogGapMomentDefectUpper
            (analyticZetaZeroMultiplicity rho) rho.1.re) := by
  constructor
  · exact pairedEtaCompletedLeadingLogFiniteLower_le_complementaryUpper
      rho htheta hthetaOne N
  · simpa [NontrivialZetaZero.conjugatePartner_coe] using
      pairedEtaCompletedLeadingLogFiniteLower_le_complementaryUpper
        (NontrivialZetaZero.conjugatePartner rho) htheta hthetaOne N

/-- For every admissible split, the explicit tail envelope tends to zero as
the number of retained arithmetic intervals tends to infinity. -/
theorem tendsto_pairedEtaLogLaplaceMomentTailUpper_zero
    (k : ℕ) {sigma theta : ℝ} (hsigma : 0 < sigma)
    (_htheta : 0 < theta) (hthetaOne : theta < 1) :
    Tendsto (fun N : ℕ ↦
      pairedEtaLogLaplaceMomentTailUpper k sigma theta N)
      atTop (nhds 0) := by
  let reserve : ℝ := (1 - theta) * sigma
  have hreserve : 0 < reserve :=
    mul_pos (sub_pos.mpr hthetaOne) hsigma
  have hbase : Tendsto (fun N : ℕ ↦ ((2 * N + 1 : ℕ) : ℝ))
      atTop atTop := by
    convert tendsto_atTop_add_const_right atTop 1
      ((tendsto_natCast_atTop_atTop (R := ℝ)).const_mul_atTop
        (by norm_num : (0 : ℝ) < 2)) using 1
    funext N
    norm_num
  have hrpow := (tendsto_rpow_neg_atTop hreserve).comp hbase
  have hscaled := hrpow.mul_const
    ((k.factorial : ℝ) / (theta * sigma) ^ (k + 1))
  convert hscaled using 1
  · funext N
    unfold pairedEtaLogLaplaceMomentTailUpper
    have hbasePos : (0 : ℝ) < ((2 * N + 1 : ℕ) : ℝ) := by
      positivity
    simp only [Function.comp_apply]
    rw [Real.rpow_def_of_pos hbasePos]
    congr 1
    dsimp [reserve]
    norm_num
    ring_nf
  · simp

/-- The finite complex support-moment prefixes converge to the complete
support moment. -/
theorem tendsto_pairedEtaLogLaplaceMomentPartialSum
    (k : ℕ) {s : ℂ} (hs : 0 < s.re) :
    Tendsto (fun N : ℕ ↦
      pairedEtaLogLaplaceMomentPartialSum k s N)
      atTop (nhds (pairedEtaLogLaplaceMoment k s)) := by
  have hsum :=
    (summable_pairedEtaLogLaplaceMomentInterval k hs).tendsto_sum_tsum_nat
  rw [← pairedEtaLogLaplaceMoment_eq_tsum_interval k hs] at hsum
  simpa only [pairedEtaLogLaplaceMomentPartialSum] using hsum

/-- The finite lower certificates converge to the exact norm of the complete
complex support moment. -/
theorem tendsto_pairedEtaLogLaplaceMomentFiniteLower
    (k : ℕ) {s : ℂ} (hs : 0 < s.re) {theta : ℝ}
    (htheta : 0 < theta) (hthetaOne : theta < 1) :
    Tendsto (fun N : ℕ ↦
      pairedEtaLogLaplaceMomentFiniteLower k s theta N)
      atTop (nhds ‖pairedEtaLogLaplaceMoment k s‖) := by
  have hprefix := (tendsto_pairedEtaLogLaplaceMomentPartialSum k hs).norm
  have htail := tendsto_pairedEtaLogLaplaceMomentTailUpper_zero
    k hs htheta hthetaOne
  have hzero : Tendsto (fun _ : ℕ ↦ (0 : ℝ)) atTop (nhds 0) :=
    tendsto_const_nhds
  have hlower := hzero.max (hprefix.sub htail)
  simpa [pairedEtaLogLaplaceMomentFiniteLower,
    max_eq_right (norm_nonneg (pairedEtaLogLaplaceMoment k s))] using hlower

/-- At every nontrivial zero the leading finite lower certificates converge
to the exact nonzero leading gap-defect norm. -/
theorem tendsto_pairedEtaLeadingLogGapMomentFiniteLower
    (rho : NontrivialZetaZero) {theta : ℝ}
    (htheta : 0 < theta) (hthetaOne : theta < 1) :
    Tendsto (fun N : ℕ ↦
      pairedEtaLogLaplaceMomentFiniteLower
        (analyticZetaZeroMultiplicity rho) rho.1 theta N)
      atTop (nhds ‖pairedEtaLeadingLogGapMomentDefect rho‖) := by
  rw [pairedEtaLeadingLogGapMomentDefect_eq_logLaplaceMoment]
  exact tendsto_pairedEtaLogLaplaceMomentFiniteLower
    (analyticZetaZeroMultiplicity rho)
    (NontrivialZetaZero.zero_lt_re rho) htheta hthetaOne

/-- Thus every leading defect admits eventually strictly positive finite
phase-sensitive lower certificates; the construction is not vacuous. -/
theorem eventually_pairedEtaLeadingLogGapMomentFiniteLower_pos
    (rho : NontrivialZetaZero) {theta : ℝ}
    (htheta : 0 < theta) (hthetaOne : theta < 1) :
    ∀ᶠ N : ℕ in atTop,
      0 < pairedEtaLogLaplaceMomentFiniteLower
        (analyticZetaZeroMultiplicity rho) rho.1 theta N := by
  exact Filter.Tendsto.eventually_const_lt
    (norm_pos_iff.mpr (pairedEtaLeadingLogGapMomentDefect_ne_zero rho))
    (tendsto_pairedEtaLeadingLogGapMomentFiniteLower
      rho htheta hthetaOne)

/-- The completion-weighted version of the finite phase-sensitive leading
defect lower certificate. -/
def pairedEtaCompletedLeadingLogFiniteLower
    (rho : NontrivialZetaZero) (theta : ℝ) (N : ℕ) : ℝ :=
  pairedEtaCompletionSpectralWeight rho *
    pairedEtaLogLaplaceMomentFiniteLower
      (analyticZetaZeroMultiplicity rho) rho.1 theta N

/-- Completion-weighted finite lower certificates converge to the exact
positive completed leading-defect magnitude. -/
theorem tendsto_pairedEtaCompletedLeadingLogFiniteLower
    (rho : NontrivialZetaZero) {theta : ℝ}
    (htheta : 0 < theta) (hthetaOne : theta < 1) :
    Tendsto (fun N : ℕ ↦
      pairedEtaCompletedLeadingLogFiniteLower rho theta N)
      atTop (nhds
        (pairedEtaCompletedLeadingLogGapMomentMagnitude rho)) := by
  have hweight : Tendsto
      (fun _ : ℕ ↦ pairedEtaCompletionSpectralWeight rho)
      atTop (nhds (pairedEtaCompletionSpectralWeight rho)) :=
    tendsto_const_nhds
  have hlower := tendsto_pairedEtaLeadingLogGapMomentFiniteLower
    rho htheta hthetaOne
  simpa only [pairedEtaCompletedLeadingLogFiniteLower,
    pairedEtaCompletedLeadingLogGapMomentMagnitude] using
    hweight.mul hlower

/-- The two complementary finite arithmetic lower sequences converge to one
and the same positive completed defect magnitude. -/
theorem tendsto_pairedEtaCompletedLeadingLogFiniteLower_both
    (rho : NontrivialZetaZero) {theta : ℝ}
    (htheta : 0 < theta) (hthetaOne : theta < 1) :
    Tendsto (fun N : ℕ ↦
        pairedEtaCompletedLeadingLogFiniteLower rho theta N)
        atTop (nhds
          (pairedEtaCompletedLeadingLogGapMomentMagnitude rho)) ∧
      Tendsto (fun N : ℕ ↦
        pairedEtaCompletedLeadingLogFiniteLower
          (NontrivialZetaZero.conjugatePartner rho) theta N)
        atTop (nhds
          (pairedEtaCompletedLeadingLogGapMomentMagnitude rho)) := by
  constructor
  · exact tendsto_pairedEtaCompletedLeadingLogFiniteLower
      rho htheta hthetaOne
  · rw [←
      pairedEtaCompletedLeadingLogGapMomentMagnitude_conjugatePartner rho]
    exact tendsto_pairedEtaCompletedLeadingLogFiniteLower
      (NontrivialZetaZero.conjugatePartner rho) htheta hthetaOne

/-- Both completed finite lower sequences are eventually strictly positive. -/
theorem eventually_pairedEtaCompletedLeadingLogFiniteLower_both_pos
    (rho : NontrivialZetaZero) {theta : ℝ}
    (htheta : 0 < theta) (hthetaOne : theta < 1) :
    ∀ᶠ N : ℕ in atTop,
      0 < pairedEtaCompletedLeadingLogFiniteLower rho theta N ∧
        0 < pairedEtaCompletedLeadingLogFiniteLower
          (NontrivialZetaZero.conjugatePartner rho) theta N := by
  filter_upwards
    [eventually_pairedEtaLeadingLogGapMomentFiniteLower_pos
      rho htheta hthetaOne,
    eventually_pairedEtaLeadingLogGapMomentFiniteLower_pos
      (NontrivialZetaZero.conjugatePartner rho) htheta hthetaOne]
      with N hrho hpartner
  exact ⟨mul_pos (pairedEtaCompletionSpectralWeight_pos rho) hrho,
    mul_pos (pairedEtaCompletionSpectralWeight_pos
      (NontrivialZetaZero.conjugatePartner rho)) hpartner⟩

end

end RiemannGaussian
