import RiemannGaussian.RiemannXiSuzukiPositiveCriticalStripEtaLeadingCoefficientFiniteCertificate

/-!
# Convergent finite enclosures for complementary eta coefficient gain

The preceding finite certificate used a simple first-gap envelope for the
partner moment.  Here both sides retain phase.  A finite eta moment prefix
plus its rigorous tail bound is an upper certificate, while the existing
prefix-minus-tail quantity is a lower certificate.

Taking the appropriate squared quotients gives a two-sided finite enclosure
for the complementary localized-Gaussian coefficient ratio.  The lower bound
is valid at every cutoff, the upper bound is valid as soon as its denominator
certificate is positive, and both converge to the exact ratio.  Thus the
enclosure width is not an analytic remainder or an appeal to computation: its
collapse is proved in Lean.

The finite upper endpoint remains strictly above one for right-half zeros,
including critical-line zeros, because its tail allowance is positive.  Thus
`upper ≤ 1` is not a viable finite target; useful closure criteria must retain
a positive uncertainty that tends to zero.
-/

open Complex Filter MeasureTheory Metric Set Topology
open scoped Classical ComplexConjugate ENNReal Interval Topology

namespace RiemannGaussian

noncomputable section

/-- A finite complex eta moment prefix plus its explicit tail error. -/
def pairedEtaLogLaplaceMomentFiniteUpper
    (k : ℕ) (s : ℂ) (theta : ℝ) (N : ℕ) : ℝ :=
  ‖pairedEtaLogLaplaceMomentPartialSum k s N‖ +
    pairedEtaLogLaplaceMomentTailUpper k s.re theta N

/-- Every admissible prefix-plus-tail quantity bounds the exact eta moment
norm from above. -/
theorem norm_pairedEtaLogLaplaceMoment_le_finiteUpper
    (k : ℕ) {s : ℂ} (hs : 0 < s.re) {theta : ℝ}
    (htheta : 0 < theta) (hthetaOne : theta < 1) (N : ℕ) :
    ‖pairedEtaLogLaplaceMoment k s‖ ≤
      pairedEtaLogLaplaceMomentFiniteUpper k s theta N := by
  have htail :=
    norm_pairedEtaLogLaplaceMomentPartialSum_sub_le_tailUpper
      k hs htheta hthetaOne N
  unfold pairedEtaLogLaplaceMomentFiniteUpper
  calc
    ‖pairedEtaLogLaplaceMoment k s‖ =
        ‖pairedEtaLogLaplaceMomentPartialSum k s N -
          (pairedEtaLogLaplaceMomentPartialSum k s N -
            pairedEtaLogLaplaceMoment k s)‖ := by ring_nf
    _ ≤ ‖pairedEtaLogLaplaceMomentPartialSum k s N‖ +
          ‖pairedEtaLogLaplaceMomentPartialSum k s N -
            pairedEtaLogLaplaceMoment k s‖ := norm_sub_le _ _
    _ ≤ ‖pairedEtaLogLaplaceMomentPartialSum k s N‖ +
          pairedEtaLogLaplaceMomentTailUpper k s.re theta N :=
      by linarith

/-- At a nontrivial zero, the phase-sensitive finite upper certificate bounds
the exact leading gap-moment defect. -/
theorem norm_pairedEtaLeadingLogGapMomentDefect_le_finiteUpper
    (rho : NontrivialZetaZero) {theta : ℝ}
    (htheta : 0 < theta) (hthetaOne : theta < 1) (N : ℕ) :
    ‖pairedEtaLeadingLogGapMomentDefect rho‖ ≤
      pairedEtaLogLaplaceMomentFiniteUpper
        (analyticZetaZeroMultiplicity rho) rho.1 theta N := by
  rw [pairedEtaLeadingLogGapMomentDefect_eq_logLaplaceMoment]
  exact norm_pairedEtaLogLaplaceMoment_le_finiteUpper
    (analyticZetaZeroMultiplicity rho)
    (NontrivialZetaZero.zero_lt_re rho) htheta hthetaOne N

/-- For every positive split parameter, prefix-minus-tail is strictly smaller
than prefix-plus-tail. -/
theorem pairedEtaLogLaplaceMomentFiniteLower_lt_finiteUpper
    (k : ℕ) {s : ℂ} (hs : 0 < s.re) {theta : ℝ}
    (htheta : 0 < theta) (N : ℕ) :
    pairedEtaLogLaplaceMomentFiniteLower k s theta N <
      pairedEtaLogLaplaceMomentFiniteUpper k s theta N := by
  have htail : 0 < pairedEtaLogLaplaceMomentTailUpper k s.re theta N :=
    pairedEtaLogLaplaceMomentTailUpper_pos k hs htheta N
  unfold pairedEtaLogLaplaceMomentFiniteLower
    pairedEtaLogLaplaceMomentFiniteUpper
  by_cases hdiff : 0 ≤
      ‖pairedEtaLogLaplaceMomentPartialSum k s N‖ -
        pairedEtaLogLaplaceMomentTailUpper k s.re theta N
  · rw [max_eq_right hdiff]
    nlinarith
  · rw [max_eq_left (le_of_not_ge hdiff)]
    nlinarith [norm_nonneg
      (pairedEtaLogLaplaceMomentPartialSum k s N)]

/-- Finite prefix-plus-tail upper certificates converge to the exact complex
eta moment norm. -/
theorem tendsto_pairedEtaLogLaplaceMomentFiniteUpper
    (k : ℕ) {s : ℂ} (hs : 0 < s.re) {theta : ℝ}
    (htheta : 0 < theta) (hthetaOne : theta < 1) :
    Tendsto (fun N : ℕ ↦
      pairedEtaLogLaplaceMomentFiniteUpper k s theta N)
      atTop (nhds ‖pairedEtaLogLaplaceMoment k s‖) := by
  have hprefix := (tendsto_pairedEtaLogLaplaceMomentPartialSum k hs).norm
  have htail := tendsto_pairedEtaLogLaplaceMomentTailUpper_zero
    k hs htheta hthetaOne
  simpa [pairedEtaLogLaplaceMomentFiniteUpper] using hprefix.add htail

/-- The lower endpoint of the finite two-sided enclosure for the partner-to-
original leading-coefficient ratio. -/
def pairedEtaLeadingCoefficientRatioFiniteEnclosureLower
    (rho : NontrivialZetaZero) (theta : ℝ) (N : ℕ) : ℝ :=
  (pairedEtaLogLaplaceMomentFiniteLower
        (analyticZetaZeroMultiplicity rho)
        (NontrivialZetaZero.conjugatePartner rho).1 theta N /
      pairedEtaLogLaplaceMomentFiniteUpper
        (analyticZetaZeroMultiplicity rho) rho.1 theta N) ^ 2

/-- The upper endpoint of the finite two-sided enclosure for the partner-to-
original leading-coefficient ratio. -/
def pairedEtaLeadingCoefficientRatioFiniteEnclosureUpper
    (rho : NontrivialZetaZero) (theta : ℝ) (N : ℕ) : ℝ :=
  (pairedEtaLogLaplaceMomentFiniteUpper
        (analyticZetaZeroMultiplicity rho)
        (NontrivialZetaZero.conjugatePartner rho).1 theta N /
      pairedEtaLogLaplaceMomentFiniteLower
        (analyticZetaZeroMultiplicity rho) rho.1 theta N) ^ 2

/-- Every admissible finite lower enclosure endpoint lies below the exact
complementary leading-coefficient ratio. -/
theorem pairedEtaLeadingCoefficientRatioFiniteEnclosureLower_le_exact
    (rho : NontrivialZetaZero) {theta : ℝ}
    (htheta : 0 < theta) (hthetaOne : theta < 1) (N : ℕ) :
    pairedEtaLeadingCoefficientRatioFiniteEnclosureLower rho theta N ≤
      pairedEtaLocalizedGaussianLargeTimeLeadingCoefficient
            (NontrivialZetaZero.conjugatePartner rho) /
          pairedEtaLocalizedGaussianLargeTimeLeadingCoefficient rho := by
  rw [
    pairedEtaLocalizedGaussianLargeTimeLeadingCoefficient_conjugatePartner_div_eq_norm_defect_div_sq]
  have hlowerPartner :
      pairedEtaLogLaplaceMomentFiniteLower
          (analyticZetaZeroMultiplicity rho)
          (NontrivialZetaZero.conjugatePartner rho).1 theta N ≤
        ‖pairedEtaLeadingLogGapMomentDefect
          (NontrivialZetaZero.conjugatePartner rho)‖ := by
    simpa only [analyticZetaZeroMultiplicity_conjugatePartner] using
      pairedEtaLeadingLogGapMomentFiniteLower_le_norm_defect
        (NontrivialZetaZero.conjugatePartner rho) htheta hthetaOne N
  have hupperRho :
      ‖pairedEtaLeadingLogGapMomentDefect rho‖ ≤
        pairedEtaLogLaplaceMomentFiniteUpper
          (analyticZetaZeroMultiplicity rho) rho.1 theta N :=
    norm_pairedEtaLeadingLogGapMomentDefect_le_finiteUpper
      rho htheta hthetaOne N
  have hratio :
      pairedEtaLogLaplaceMomentFiniteLower
            (analyticZetaZeroMultiplicity rho)
            (NontrivialZetaZero.conjugatePartner rho).1 theta N /
          pairedEtaLogLaplaceMomentFiniteUpper
            (analyticZetaZeroMultiplicity rho) rho.1 theta N ≤
        ‖pairedEtaLeadingLogGapMomentDefect
              (NontrivialZetaZero.conjugatePartner rho)‖ /
            ‖pairedEtaLeadingLogGapMomentDefect rho‖ :=
    div_le_div₀ (norm_nonneg _) hlowerPartner
      (norm_pos_iff.mpr (pairedEtaLeadingLogGapMomentDefect_ne_zero rho))
      hupperRho
  have hlowerNonneg :
      0 ≤ pairedEtaLogLaplaceMomentFiniteLower
        (analyticZetaZeroMultiplicity rho)
        (NontrivialZetaZero.conjugatePartner rho).1 theta N := by
    unfold pairedEtaLogLaplaceMomentFiniteLower
    exact le_max_left _ _
  have hupperPos :
      0 < pairedEtaLogLaplaceMomentFiniteUpper
        (analyticZetaZeroMultiplicity rho) rho.1 theta N := by
    unfold pairedEtaLogLaplaceMomentFiniteUpper
    exact add_pos_of_nonneg_of_pos (norm_nonneg _)
      (pairedEtaLogLaplaceMomentTailUpper_pos _
        (NontrivialZetaZero.zero_lt_re rho) htheta N)
  have hleftNonneg :
      0 ≤ pairedEtaLogLaplaceMomentFiniteLower
            (analyticZetaZeroMultiplicity rho)
            (NontrivialZetaZero.conjugatePartner rho).1 theta N /
          pairedEtaLogLaplaceMomentFiniteUpper
            (analyticZetaZeroMultiplicity rho) rho.1 theta N :=
    div_nonneg hlowerNonneg hupperPos.le
  have hrightNonneg :
      0 ≤ ‖pairedEtaLeadingLogGapMomentDefect
              (NontrivialZetaZero.conjugatePartner rho)‖ /
            ‖pairedEtaLeadingLogGapMomentDefect rho‖ := by positivity
  unfold pairedEtaLeadingCoefficientRatioFiniteEnclosureLower
  nlinarith

/-- A positive denominator lower certificate makes the finite upper enclosure
endpoint a valid upper bound for the exact coefficient ratio. -/
theorem pairedEtaLeadingCoefficientRatio_exact_le_finiteEnclosureUpper
    (rho : NontrivialZetaZero) {theta : ℝ}
    (htheta : 0 < theta) (hthetaOne : theta < 1) (N : ℕ)
    (hlower : 0 < pairedEtaLogLaplaceMomentFiniteLower
      (analyticZetaZeroMultiplicity rho) rho.1 theta N) :
    pairedEtaLocalizedGaussianLargeTimeLeadingCoefficient
            (NontrivialZetaZero.conjugatePartner rho) /
          pairedEtaLocalizedGaussianLargeTimeLeadingCoefficient rho ≤
      pairedEtaLeadingCoefficientRatioFiniteEnclosureUpper rho theta N := by
  rw [
    pairedEtaLocalizedGaussianLargeTimeLeadingCoefficient_conjugatePartner_div_eq_norm_defect_div_sq]
  have hlowerRho :
      pairedEtaLogLaplaceMomentFiniteLower
          (analyticZetaZeroMultiplicity rho) rho.1 theta N ≤
        ‖pairedEtaLeadingLogGapMomentDefect rho‖ :=
    pairedEtaLeadingLogGapMomentFiniteLower_le_norm_defect
      rho htheta hthetaOne N
  have hupperPartner :
      ‖pairedEtaLeadingLogGapMomentDefect
          (NontrivialZetaZero.conjugatePartner rho)‖ ≤
        pairedEtaLogLaplaceMomentFiniteUpper
          (analyticZetaZeroMultiplicity rho)
          (NontrivialZetaZero.conjugatePartner rho).1 theta N := by
    simpa only [analyticZetaZeroMultiplicity_conjugatePartner] using
      norm_pairedEtaLeadingLogGapMomentDefect_le_finiteUpper
        (NontrivialZetaZero.conjugatePartner rho) htheta hthetaOne N
  have hupperPartnerPos :
      0 < pairedEtaLogLaplaceMomentFiniteUpper
          (analyticZetaZeroMultiplicity rho)
          (NontrivialZetaZero.conjugatePartner rho).1 theta N := by
    unfold pairedEtaLogLaplaceMomentFiniteUpper
    exact add_pos_of_nonneg_of_pos (norm_nonneg _)
      (pairedEtaLogLaplaceMomentTailUpper_pos _
        (NontrivialZetaZero.zero_lt_re
          (NontrivialZetaZero.conjugatePartner rho)) htheta N)
  have hratio :
      ‖pairedEtaLeadingLogGapMomentDefect
            (NontrivialZetaZero.conjugatePartner rho)‖ /
          ‖pairedEtaLeadingLogGapMomentDefect rho‖ ≤
        pairedEtaLogLaplaceMomentFiniteUpper
              (analyticZetaZeroMultiplicity rho)
              (NontrivialZetaZero.conjugatePartner rho).1 theta N /
            pairedEtaLogLaplaceMomentFiniteLower
              (analyticZetaZeroMultiplicity rho) rho.1 theta N :=
    div_le_div₀ hupperPartnerPos.le hupperPartner hlower hlowerRho
  have hleftNonneg :
      0 ≤ ‖pairedEtaLeadingLogGapMomentDefect
              (NontrivialZetaZero.conjugatePartner rho)‖ /
            ‖pairedEtaLeadingLogGapMomentDefect rho‖ := by positivity
  have hrightNonneg :
      0 ≤ pairedEtaLogLaplaceMomentFiniteUpper
            (analyticZetaZeroMultiplicity rho)
            (NontrivialZetaZero.conjugatePartner rho).1 theta N /
          pairedEtaLogLaplaceMomentFiniteLower
            (analyticZetaZeroMultiplicity rho) rho.1 theta N := by
    exact div_nonneg hupperPartnerPos.le hlower.le
  unfold pairedEtaLeadingCoefficientRatioFiniteEnclosureUpper
  nlinarith

/-- The finite lower enclosure endpoints converge to the exact complementary
leading-coefficient ratio. -/
theorem tendsto_pairedEtaLeadingCoefficientRatioFiniteEnclosureLower
    (rho : NontrivialZetaZero) {theta : ℝ}
    (htheta : 0 < theta) (hthetaOne : theta < 1) :
    Tendsto (fun N : ℕ ↦
      pairedEtaLeadingCoefficientRatioFiniteEnclosureLower rho theta N)
      atTop
      (nhds
        (pairedEtaLocalizedGaussianLargeTimeLeadingCoefficient
              (NontrivialZetaZero.conjugatePartner rho) /
            pairedEtaLocalizedGaussianLargeTimeLeadingCoefficient rho)) := by
  rw [
    pairedEtaLocalizedGaussianLargeTimeLeadingCoefficient_conjugatePartner_div_eq_norm_defect_div_sq]
  have hlowerPartner :=
    tendsto_pairedEtaLeadingLogGapMomentFiniteLower
      (NontrivialZetaZero.conjugatePartner rho) htheta hthetaOne
  have hupperRho :=
    tendsto_pairedEtaLogLaplaceMomentFiniteUpper
      (analyticZetaZeroMultiplicity rho)
      (NontrivialZetaZero.zero_lt_re rho) htheta hthetaOne
  rw [← pairedEtaLeadingLogGapMomentDefect_eq_logLaplaceMoment] at hupperRho
  have hratio := hlowerPartner.div hupperRho
    (norm_ne_zero_iff.mpr (pairedEtaLeadingLogGapMomentDefect_ne_zero rho))
  simpa [pairedEtaLeadingCoefficientRatioFiniteEnclosureLower,
    analyticZetaZeroMultiplicity_conjugatePartner] using hratio.pow 2

/-- The finite upper enclosure endpoints also converge to the exact
complementary leading-coefficient ratio. -/
theorem tendsto_pairedEtaLeadingCoefficientRatioFiniteEnclosureUpper
    (rho : NontrivialZetaZero) {theta : ℝ}
    (htheta : 0 < theta) (hthetaOne : theta < 1) :
    Tendsto (fun N : ℕ ↦
      pairedEtaLeadingCoefficientRatioFiniteEnclosureUpper rho theta N)
      atTop
      (nhds
        (pairedEtaLocalizedGaussianLargeTimeLeadingCoefficient
              (NontrivialZetaZero.conjugatePartner rho) /
            pairedEtaLocalizedGaussianLargeTimeLeadingCoefficient rho)) := by
  rw [
    pairedEtaLocalizedGaussianLargeTimeLeadingCoefficient_conjugatePartner_div_eq_norm_defect_div_sq]
  have hupperPartner :
      Tendsto (fun N : ℕ ↦
        pairedEtaLogLaplaceMomentFiniteUpper
          (analyticZetaZeroMultiplicity rho)
          (NontrivialZetaZero.conjugatePartner rho).1 theta N)
        atTop
        (nhds ‖pairedEtaLeadingLogGapMomentDefect
          (NontrivialZetaZero.conjugatePartner rho)‖) := by
    rw [pairedEtaLeadingLogGapMomentDefect_eq_logLaplaceMoment]
    simpa only [analyticZetaZeroMultiplicity_conjugatePartner] using
      tendsto_pairedEtaLogLaplaceMomentFiniteUpper
        (analyticZetaZeroMultiplicity
          (NontrivialZetaZero.conjugatePartner rho))
        (NontrivialZetaZero.zero_lt_re
          (NontrivialZetaZero.conjugatePartner rho)) htheta hthetaOne
  have hlowerRho :=
    tendsto_pairedEtaLeadingLogGapMomentFiniteLower
      rho htheta hthetaOne
  have hratio := hupperPartner.div hlowerRho
    (norm_ne_zero_iff.mpr (pairedEtaLeadingLogGapMomentDefect_ne_zero rho))
  simpa [pairedEtaLeadingCoefficientRatioFiniteEnclosureUpper,
    analyticZetaZeroMultiplicity_conjugatePartner] using hratio.pow 2

/-- The width of the two finite coefficient-ratio enclosures converges to
zero, so the certified interval collapses to the exact arithmetic gain. -/
theorem tendsto_pairedEtaLeadingCoefficientRatioFiniteEnclosure_width_zero
    (rho : NontrivialZetaZero) {theta : ℝ}
    (htheta : 0 < theta) (hthetaOne : theta < 1) :
    Tendsto (fun N : ℕ ↦
      pairedEtaLeadingCoefficientRatioFiniteEnclosureUpper rho theta N -
        pairedEtaLeadingCoefficientRatioFiniteEnclosureLower rho theta N)
      atTop (nhds 0) := by
  have hupper :=
    tendsto_pairedEtaLeadingCoefficientRatioFiniteEnclosureUpper
      rho htheta hthetaOne
  have hlower :=
    tendsto_pairedEtaLeadingCoefficientRatioFiniteEnclosureLower
      rho htheta hthetaOne
  simpa only [sub_self] using hupper.sub hlower

/-- Every admissible fixed tail split eventually gives a genuine two-sided
finite enclosure of the exact complementary coefficient ratio. -/
theorem eventually_pairedEtaLeadingCoefficientRatio_mem_finiteEnclosure
    (rho : NontrivialZetaZero) {theta : ℝ}
    (htheta : 0 < theta) (hthetaOne : theta < 1) :
    ∀ᶠ N : ℕ in atTop,
      pairedEtaLeadingCoefficientRatioFiniteEnclosureLower rho theta N ≤
          pairedEtaLocalizedGaussianLargeTimeLeadingCoefficient
                (NontrivialZetaZero.conjugatePartner rho) /
              pairedEtaLocalizedGaussianLargeTimeLeadingCoefficient rho ∧
        pairedEtaLocalizedGaussianLargeTimeLeadingCoefficient
                (NontrivialZetaZero.conjugatePartner rho) /
              pairedEtaLocalizedGaussianLargeTimeLeadingCoefficient rho ≤
          pairedEtaLeadingCoefficientRatioFiniteEnclosureUpper rho theta N := by
  filter_upwards
    [eventually_pairedEtaLeadingLogGapMomentFiniteLower_pos
      rho htheta hthetaOne] with N hlower
  exact ⟨
    pairedEtaLeadingCoefficientRatioFiniteEnclosureLower_le_exact
      rho htheta hthetaOne N,
    pairedEtaLeadingCoefficientRatio_exact_le_finiteEnclosureUpper
      rho htheta hthetaOne N hlower⟩

/-- At high ordinate on or to the right of the critical line, a positive
denominator certificate turns the convergent upper enclosure into an explicit
horizontal-displacement bound. -/
theorem re_sub_half_le_100_mul_realLog_finiteEnclosureUpper_of_eight_le_abs_im
    (rho : NontrivialZetaZero) {theta : ℝ}
    (htheta : 0 < theta) (hthetaOne : theta < 1) (N : ℕ)
    (hlower : 0 < pairedEtaLogLaplaceMomentFiniteLower
      (analyticZetaZeroMultiplicity rho) rho.1 theta N)
    (hhalf : 1 / 2 ≤ rho.1.re) (hy : 8 ≤ |rho.1.im|) :
    rho.1.re - 1 / 2 ≤
      100 * Real.log
        (pairedEtaLeadingCoefficientRatioFiniteEnclosureUpper rho theta N) := by
  have hdisplacement :=
    one_over_100_mul_abs_re_sub_half_le_abs_realLog_leadingCoefficient_ratio_of_eight_le_abs_im
      rho hy
  have hratioBound :=
    pairedEtaLeadingCoefficientRatio_exact_le_finiteEnclosureUpper
      rho htheta hthetaOne N hlower
  have hratioPos :
      0 < pairedEtaLocalizedGaussianLargeTimeLeadingCoefficient
            (NontrivialZetaZero.conjugatePartner rho) /
          pairedEtaLocalizedGaussianLargeTimeLeadingCoefficient rho :=
    div_pos
      (pairedEtaLocalizedGaussianLargeTimeLeadingCoefficient_pos _)
      (pairedEtaLocalizedGaussianLargeTimeLeadingCoefficient_pos rho)
  have hlogUpper :
      Real.log
          (pairedEtaLocalizedGaussianLargeTimeLeadingCoefficient
                (NontrivialZetaZero.conjugatePartner rho) /
              pairedEtaLocalizedGaussianLargeTimeLeadingCoefficient rho) ≤
        Real.log
          (pairedEtaLeadingCoefficientRatioFiniteEnclosureUpper rho theta N) :=
    Real.log_le_log hratioPos hratioBound
  have hlogNonneg :
      0 ≤ Real.log
        (pairedEtaLocalizedGaussianLargeTimeLeadingCoefficient
              (NontrivialZetaZero.conjugatePartner rho) /
            pairedEtaLocalizedGaussianLargeTimeLeadingCoefficient rho) := by
    rw [
      realLog_pairedEtaLocalizedGaussianLargeTimeLeadingCoefficient_conjugatePartner_div_eq_two_mul_reflectionLogNorm]
    rcases hhalf.eq_or_lt with hline | hright
    · rw [← hline, pairedEtaLaplaceReflectionLogNorm_half]
      norm_num
    · exact mul_nonneg (by norm_num)
        (pairedEtaLaplaceReflectionLogNorm_pos_of_half_lt_of_eight_le_abs
          hright (NontrivialZetaZero.re_lt_one rho) hy).le
  rw [abs_of_nonneg (sub_nonneg.mpr hhalf), abs_of_nonneg hlogNonneg] at hdisplacement
  nlinarith

/-- Every fixed admissible tail split eventually yields the convergent
high-ordinate horizontal-displacement certificate. -/
theorem
    eventually_re_sub_half_le_100_mul_realLog_finiteEnclosureUpper_of_eight_le_abs_im
    (rho : NontrivialZetaZero) {theta : ℝ}
    (htheta : 0 < theta) (hthetaOne : theta < 1)
    (hhalf : 1 / 2 ≤ rho.1.re) (hy : 8 ≤ |rho.1.im|) :
    ∀ᶠ N : ℕ in atTop,
      rho.1.re - 1 / 2 ≤
        100 * Real.log
          (pairedEtaLeadingCoefficientRatioFiniteEnclosureUpper rho theta N) := by
  filter_upwards
    [eventually_pairedEtaLeadingLogGapMomentFiniteLower_pos
      rho htheta hthetaOne] with N hlower
  exact
    re_sub_half_le_100_mul_realLog_finiteEnclosureUpper_of_eight_le_abs_im
      rho htheta hthetaOne N hlower hhalf hy

/-- Every valid fixed-split upper enclosure is strictly greater than one for a
zero on or to the right of the critical line.  In particular, the tempting
finite target `upper ≤ 1` is vacuous even on the critical line. -/
theorem one_lt_pairedEtaLeadingCoefficientRatioFiniteEnclosureUpper_of_half_le_re
    (rho : NontrivialZetaZero) {theta : ℝ}
    (htheta : 0 < theta) (hthetaOne : theta < 1) (N : ℕ)
    (hlower : 0 < pairedEtaLogLaplaceMomentFiniteLower
      (analyticZetaZeroMultiplicity rho) rho.1 theta N)
    (hhalf : 1 / 2 ≤ rho.1.re) :
    1 < pairedEtaLeadingCoefficientRatioFiniteEnclosureUpper
      rho theta N := by
  rcases hhalf.eq_or_lt with hline | hright
  · have hpartner : NontrivialZetaZero.conjugatePartner rho = rho := by
      apply Subtype.ext
      rw [NontrivialZetaZero.conjugatePartner_coe]
      apply Complex.ext
      · simp only [Complex.sub_re, Complex.one_re, Complex.conj_re]
        linarith
      · simp
    have hstrict := pairedEtaLogLaplaceMomentFiniteLower_lt_finiteUpper
      (analyticZetaZeroMultiplicity rho)
      (NontrivialZetaZero.zero_lt_re rho) htheta N
    have hratioGt :
        1 < pairedEtaLogLaplaceMomentFiniteUpper
              (analyticZetaZeroMultiplicity rho) rho.1 theta N /
            pairedEtaLogLaplaceMomentFiniteLower
              (analyticZetaZeroMultiplicity rho) rho.1 theta N :=
      (one_lt_div₀ hlower).2 hstrict
    unfold pairedEtaLeadingCoefficientRatioFiniteEnclosureUpper
    rw [hpartner]
    nlinarith
  · have hratioExact :
        1 < pairedEtaLocalizedGaussianLargeTimeLeadingCoefficient
              (NontrivialZetaZero.conjugatePartner rho) /
            pairedEtaLocalizedGaussianLargeTimeLeadingCoefficient rho :=
      (one_lt_div₀
        (pairedEtaLocalizedGaussianLargeTimeLeadingCoefficient_pos rho)).2
          ((pairedEtaLocalizedGaussianLargeTimeLeadingCoefficient_lt_conjugatePartner_iff_half_lt_re
            rho).2 hright)
    exact hratioExact.trans_le
      (pairedEtaLeadingCoefficientRatio_exact_le_finiteEnclosureUpper
        rho htheta hthetaOne N hlower)

end
end RiemannGaussian
