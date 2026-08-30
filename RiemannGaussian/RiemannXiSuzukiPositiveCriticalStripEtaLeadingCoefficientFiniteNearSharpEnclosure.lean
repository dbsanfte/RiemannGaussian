import RiemannGaussian.RiemannXiSuzukiPositiveCriticalStripEtaLeadingCoefficientFiniteEnclosure
import RiemannGaussian.RiemannXiSuzukiPositiveCriticalStripEtaLeadingLogMomentFiniteOptimizedTail

/-!
# Near-sharp finite enclosures for complementary eta coefficient gain

The fixed-split enclosure sacrifices part of the horizontal decay exponent in
its rigorous tail.  This module substitutes the already checked balanced
cutoff-dependent split.  Its elementary tail keeps the full exponent
`sigma`, with only the unavoidable fixed logarithmic power.

Once the explicit cutoff inequalities hold at both complementary tilts, the
near-sharp prefix-minus-tail and prefix-plus-tail quotients enclose the exact
leading-coefficient ratio.  The cutoff conditions are eventual, both
endpoints converge to the exact ratio, and their width tends to zero.

Crucially, Lean also proves that the finite upper endpoint is strictly above
one for every right-half zero, even on the critical line: positive rigorous
tail allowances make `upper ≤ 1` an unattainable target.  The correct
non-vacuous comparison allows the intrinsic upper-to-lower self-slack, which
tends to zero.  It reduces exactly to eventual monotonicity of the two
prefix-plus-tail upper certificates.  Proving that eta-specific monotonicity,
not eliminating a necessary finite error bar, is the literal frontier.
-/

open Complex Filter MeasureTheory Metric Set Topology
open scoped Classical ComplexConjugate ENNReal Interval Topology

namespace RiemannGaussian

noncomputable section

/-- The near-sharp finite eta moment upper certificate: retained prefix norm
plus the balanced full-exponent tail envelope. -/
def pairedEtaLogLaplaceMomentNearSharpFiniteUpper
    (k : ℕ) (s : ℂ) (N : ℕ) : ℝ :=
  ‖pairedEtaLogLaplaceMomentPartialSum k s N‖ +
    pairedEtaLogLaplaceMomentNearSharpTailUpper k s.re N

/-- The balanced full-exponent tail envelope is strictly positive whenever
its explicit cutoff condition is valid. -/
theorem pairedEtaLogLaplaceMomentNearSharpTailUpper_pos_of_cutoff
    (k N : ℕ) {sigma : ℝ} (hsigma : 0 < sigma)
    (hcutoff : ((k + 1 : ℕ) : ℝ) <
      sigma * Real.log (((2 * N + 1 : ℕ) : ℝ))) :
    0 < pairedEtaLogLaplaceMomentNearSharpTailUpper k sigma N := by
  rw [← pairedEtaLogLaplaceMomentTailUpper_balancedTheta_eq_nearSharp
    k N hsigma hcutoff]
  exact pairedEtaLogLaplaceMomentTailUpper_pos k hsigma
    (pairedEtaLogLaplaceMomentBalancedTheta_pos k N hcutoff) N

/-- Past the explicit balanced-split cutoff, the exact eta moment norm lies
below its near-sharp finite upper certificate. -/
theorem norm_pairedEtaLogLaplaceMoment_le_nearSharpFiniteUpper
    (k : ℕ) {s : ℂ} (hs : 0 < s.re) (N : ℕ)
    (hcutoff : ((k + 1 : ℕ) : ℝ) <
      s.re * Real.log (((2 * N + 1 : ℕ) : ℝ))) :
    ‖pairedEtaLogLaplaceMoment k s‖ ≤
      pairedEtaLogLaplaceMomentNearSharpFiniteUpper k s N := by
  have htail :=
    norm_pairedEtaLogLaplaceMomentPartialSum_sub_le_nearSharp
      k hs N hcutoff
  unfold pairedEtaLogLaplaceMomentNearSharpFiniteUpper
  calc
    ‖pairedEtaLogLaplaceMoment k s‖ =
        ‖pairedEtaLogLaplaceMomentPartialSum k s N -
          (pairedEtaLogLaplaceMomentPartialSum k s N -
            pairedEtaLogLaplaceMoment k s)‖ := by ring_nf
    _ ≤ ‖pairedEtaLogLaplaceMomentPartialSum k s N‖ +
          ‖pairedEtaLogLaplaceMomentPartialSum k s N -
            pairedEtaLogLaplaceMoment k s‖ := norm_sub_le _ _
    _ ≤ ‖pairedEtaLogLaplaceMomentPartialSum k s N‖ +
          pairedEtaLogLaplaceMomentNearSharpTailUpper k s.re N := by
      linarith

/-- At a zeta zero, the exact leading gap defect lies below its near-sharp
finite upper certificate once the explicit cutoff condition holds. -/
theorem norm_pairedEtaLeadingLogGapMomentDefect_le_nearSharpFiniteUpper
    (rho : NontrivialZetaZero) (N : ℕ)
    (hcutoff :
      (((analyticZetaZeroMultiplicity rho + 1 : ℕ) : ℝ)) <
        rho.1.re * Real.log (((2 * N + 1 : ℕ) : ℝ))) :
    ‖pairedEtaLeadingLogGapMomentDefect rho‖ ≤
      pairedEtaLogLaplaceMomentNearSharpFiniteUpper
        (analyticZetaZeroMultiplicity rho) rho.1 N := by
  rw [pairedEtaLeadingLogGapMomentDefect_eq_logLaplaceMoment]
  exact norm_pairedEtaLogLaplaceMoment_le_nearSharpFiniteUpper
    (analyticZetaZeroMultiplicity rho)
    (NontrivialZetaZero.zero_lt_re rho) N hcutoff

/-- At every valid cutoff, the near-sharp prefix-minus-tail certificate is
strictly smaller than the prefix-plus-tail certificate. -/
theorem pairedEtaLogLaplaceMomentNearSharpFiniteLower_lt_finiteUpper
    (k : ℕ) {s : ℂ} (hs : 0 < s.re) (N : ℕ)
    (hcutoff : ((k + 1 : ℕ) : ℝ) <
      s.re * Real.log (((2 * N + 1 : ℕ) : ℝ))) :
    pairedEtaLogLaplaceMomentNearSharpFiniteLower k s N <
      pairedEtaLogLaplaceMomentNearSharpFiniteUpper k s N := by
  have htail :
      0 < pairedEtaLogLaplaceMomentNearSharpTailUpper k s.re N :=
    pairedEtaLogLaplaceMomentNearSharpTailUpper_pos_of_cutoff
      k N hs hcutoff
  unfold pairedEtaLogLaplaceMomentNearSharpFiniteLower
    pairedEtaLogLaplaceMomentNearSharpFiniteUpper
  by_cases hdiff : 0 ≤
      ‖pairedEtaLogLaplaceMomentPartialSum k s N‖ -
        pairedEtaLogLaplaceMomentNearSharpTailUpper k s.re N
  · rw [max_eq_right hdiff]
    nlinarith
  · rw [max_eq_left (le_of_not_ge hdiff)]
    nlinarith [norm_nonneg
      (pairedEtaLogLaplaceMomentPartialSum k s N)]

/-- Near-sharp prefix-plus-tail upper certificates converge to the exact eta
moment norm. -/
theorem tendsto_pairedEtaLogLaplaceMomentNearSharpFiniteUpper
    (k : ℕ) {s : ℂ} (hs : 0 < s.re) :
    Tendsto (fun N : ℕ ↦
      pairedEtaLogLaplaceMomentNearSharpFiniteUpper k s N)
      atTop (nhds ‖pairedEtaLogLaplaceMoment k s‖) := by
  have hprefix := (tendsto_pairedEtaLogLaplaceMomentPartialSum k hs).norm
  have htail :=
    tendsto_pairedEtaLogLaplaceMomentNearSharpTailUpper_zero k hs
  simpa [pairedEtaLogLaplaceMomentNearSharpFiniteUpper] using hprefix.add htail

/-- The near-sharp lower endpoint for the complementary leading-coefficient
ratio. -/
def pairedEtaLeadingCoefficientRatioNearSharpEnclosureLower
    (rho : NontrivialZetaZero) (N : ℕ) : ℝ :=
  (pairedEtaLogLaplaceMomentNearSharpFiniteLower
        (analyticZetaZeroMultiplicity rho)
        (NontrivialZetaZero.conjugatePartner rho).1 N /
      pairedEtaLogLaplaceMomentNearSharpFiniteUpper
        (analyticZetaZeroMultiplicity rho) rho.1 N) ^ 2

/-- The near-sharp upper endpoint for the complementary leading-coefficient
ratio. -/
def pairedEtaLeadingCoefficientRatioNearSharpEnclosureUpper
    (rho : NontrivialZetaZero) (N : ℕ) : ℝ :=
  (pairedEtaLogLaplaceMomentNearSharpFiniteUpper
        (analyticZetaZeroMultiplicity rho)
        (NontrivialZetaZero.conjugatePartner rho).1 N /
      pairedEtaLogLaplaceMomentNearSharpFiniteLower
        (analyticZetaZeroMultiplicity rho) rho.1 N) ^ 2

/-- Once both balanced-split cutoff conditions hold, the near-sharp lower
endpoint bounds the exact complementary coefficient ratio from below. -/
theorem pairedEtaLeadingCoefficientRatioNearSharpEnclosureLower_le_exact
    (rho : NontrivialZetaZero) (N : ℕ)
    (hpartnerCutoff :
      (((analyticZetaZeroMultiplicity rho + 1 : ℕ) : ℝ)) <
        (NontrivialZetaZero.conjugatePartner rho).1.re *
          Real.log (((2 * N + 1 : ℕ) : ℝ)))
    (hrhoCutoff :
      (((analyticZetaZeroMultiplicity rho + 1 : ℕ) : ℝ)) <
        rho.1.re * Real.log (((2 * N + 1 : ℕ) : ℝ))) :
    pairedEtaLeadingCoefficientRatioNearSharpEnclosureLower rho N ≤
      pairedEtaLocalizedGaussianLargeTimeLeadingCoefficient
            (NontrivialZetaZero.conjugatePartner rho) /
          pairedEtaLocalizedGaussianLargeTimeLeadingCoefficient rho := by
  rw [
    pairedEtaLocalizedGaussianLargeTimeLeadingCoefficient_conjugatePartner_div_eq_norm_defect_div_sq]
  have hlowerPartner :
      pairedEtaLogLaplaceMomentNearSharpFiniteLower
          (analyticZetaZeroMultiplicity rho)
          (NontrivialZetaZero.conjugatePartner rho).1 N ≤
        ‖pairedEtaLeadingLogGapMomentDefect
          (NontrivialZetaZero.conjugatePartner rho)‖ := by
    simpa only [analyticZetaZeroMultiplicity_conjugatePartner] using
      pairedEtaLeadingLogGapMomentNearSharpFiniteLower_le_norm_defect
        (NontrivialZetaZero.conjugatePartner rho) N
        (by simpa only [analyticZetaZeroMultiplicity_conjugatePartner] using
          hpartnerCutoff)
  have hupperRho :
      ‖pairedEtaLeadingLogGapMomentDefect rho‖ ≤
        pairedEtaLogLaplaceMomentNearSharpFiniteUpper
          (analyticZetaZeroMultiplicity rho) rho.1 N :=
    norm_pairedEtaLeadingLogGapMomentDefect_le_nearSharpFiniteUpper
      rho N hrhoCutoff
  have hupperRhoPos :
      0 < pairedEtaLogLaplaceMomentNearSharpFiniteUpper
        (analyticZetaZeroMultiplicity rho) rho.1 N :=
    (norm_pos_iff.mpr
      (pairedEtaLeadingLogGapMomentDefect_ne_zero rho)).trans_le hupperRho
  have hratio :
      pairedEtaLogLaplaceMomentNearSharpFiniteLower
            (analyticZetaZeroMultiplicity rho)
            (NontrivialZetaZero.conjugatePartner rho).1 N /
          pairedEtaLogLaplaceMomentNearSharpFiniteUpper
            (analyticZetaZeroMultiplicity rho) rho.1 N ≤
        ‖pairedEtaLeadingLogGapMomentDefect
              (NontrivialZetaZero.conjugatePartner rho)‖ /
            ‖pairedEtaLeadingLogGapMomentDefect rho‖ :=
    div_le_div₀ (norm_nonneg _) hlowerPartner
      (norm_pos_iff.mpr (pairedEtaLeadingLogGapMomentDefect_ne_zero rho))
      hupperRho
  have hlowerNonneg :
      0 ≤ pairedEtaLogLaplaceMomentNearSharpFiniteLower
        (analyticZetaZeroMultiplicity rho)
        (NontrivialZetaZero.conjugatePartner rho).1 N := by
    unfold pairedEtaLogLaplaceMomentNearSharpFiniteLower
    exact le_max_left _ _
  have hleftNonneg :
      0 ≤ pairedEtaLogLaplaceMomentNearSharpFiniteLower
            (analyticZetaZeroMultiplicity rho)
            (NontrivialZetaZero.conjugatePartner rho).1 N /
          pairedEtaLogLaplaceMomentNearSharpFiniteUpper
            (analyticZetaZeroMultiplicity rho) rho.1 N :=
    div_nonneg hlowerNonneg hupperRhoPos.le
  have hrightNonneg :
      0 ≤ ‖pairedEtaLeadingLogGapMomentDefect
              (NontrivialZetaZero.conjugatePartner rho)‖ /
            ‖pairedEtaLeadingLogGapMomentDefect rho‖ := by positivity
  unfold pairedEtaLeadingCoefficientRatioNearSharpEnclosureLower
  nlinarith

/-- A positive near-sharp lower certificate at `rho`, together with both
cutoff conditions, makes the near-sharp upper endpoint rigorous. -/
theorem pairedEtaLeadingCoefficientRatio_exact_le_nearSharpEnclosureUpper
    (rho : NontrivialZetaZero) (N : ℕ)
    (hpartnerCutoff :
      (((analyticZetaZeroMultiplicity rho + 1 : ℕ) : ℝ)) <
        (NontrivialZetaZero.conjugatePartner rho).1.re *
          Real.log (((2 * N + 1 : ℕ) : ℝ)))
    (hrhoCutoff :
      (((analyticZetaZeroMultiplicity rho + 1 : ℕ) : ℝ)) <
        rho.1.re * Real.log (((2 * N + 1 : ℕ) : ℝ)))
    (hlower : 0 < pairedEtaLogLaplaceMomentNearSharpFiniteLower
      (analyticZetaZeroMultiplicity rho) rho.1 N) :
    pairedEtaLocalizedGaussianLargeTimeLeadingCoefficient
            (NontrivialZetaZero.conjugatePartner rho) /
          pairedEtaLocalizedGaussianLargeTimeLeadingCoefficient rho ≤
      pairedEtaLeadingCoefficientRatioNearSharpEnclosureUpper rho N := by
  rw [
    pairedEtaLocalizedGaussianLargeTimeLeadingCoefficient_conjugatePartner_div_eq_norm_defect_div_sq]
  have hlowerRho :
      pairedEtaLogLaplaceMomentNearSharpFiniteLower
          (analyticZetaZeroMultiplicity rho) rho.1 N ≤
        ‖pairedEtaLeadingLogGapMomentDefect rho‖ :=
    pairedEtaLeadingLogGapMomentNearSharpFiniteLower_le_norm_defect
      rho N hrhoCutoff
  have hupperPartner :
      ‖pairedEtaLeadingLogGapMomentDefect
          (NontrivialZetaZero.conjugatePartner rho)‖ ≤
        pairedEtaLogLaplaceMomentNearSharpFiniteUpper
          (analyticZetaZeroMultiplicity rho)
          (NontrivialZetaZero.conjugatePartner rho).1 N := by
    simpa only [analyticZetaZeroMultiplicity_conjugatePartner] using
      norm_pairedEtaLeadingLogGapMomentDefect_le_nearSharpFiniteUpper
        (NontrivialZetaZero.conjugatePartner rho) N
        (by simpa only [analyticZetaZeroMultiplicity_conjugatePartner] using
          hpartnerCutoff)
  have hupperPartnerPos :
      0 < pairedEtaLogLaplaceMomentNearSharpFiniteUpper
          (analyticZetaZeroMultiplicity rho)
          (NontrivialZetaZero.conjugatePartner rho).1 N :=
    (norm_pos_iff.mpr
      (pairedEtaLeadingLogGapMomentDefect_ne_zero
        (NontrivialZetaZero.conjugatePartner rho))).trans_le hupperPartner
  have hratio :
      ‖pairedEtaLeadingLogGapMomentDefect
            (NontrivialZetaZero.conjugatePartner rho)‖ /
          ‖pairedEtaLeadingLogGapMomentDefect rho‖ ≤
        pairedEtaLogLaplaceMomentNearSharpFiniteUpper
              (analyticZetaZeroMultiplicity rho)
              (NontrivialZetaZero.conjugatePartner rho).1 N /
            pairedEtaLogLaplaceMomentNearSharpFiniteLower
              (analyticZetaZeroMultiplicity rho) rho.1 N :=
    div_le_div₀ hupperPartnerPos.le hupperPartner hlower hlowerRho
  have hleftNonneg :
      0 ≤ ‖pairedEtaLeadingLogGapMomentDefect
              (NontrivialZetaZero.conjugatePartner rho)‖ /
            ‖pairedEtaLeadingLogGapMomentDefect rho‖ := by positivity
  have hrightNonneg :
      0 ≤ pairedEtaLogLaplaceMomentNearSharpFiniteUpper
            (analyticZetaZeroMultiplicity rho)
            (NontrivialZetaZero.conjugatePartner rho).1 N /
          pairedEtaLogLaplaceMomentNearSharpFiniteLower
            (analyticZetaZeroMultiplicity rho) rho.1 N :=
    div_nonneg hupperPartnerPos.le hlower.le
  unfold pairedEtaLeadingCoefficientRatioNearSharpEnclosureUpper
  nlinarith

/-- The near-sharp lower endpoints converge to the exact complementary
leading-coefficient ratio. -/
theorem tendsto_pairedEtaLeadingCoefficientRatioNearSharpEnclosureLower
    (rho : NontrivialZetaZero) :
    Tendsto (fun N : ℕ ↦
      pairedEtaLeadingCoefficientRatioNearSharpEnclosureLower rho N)
      atTop
      (nhds
        (pairedEtaLocalizedGaussianLargeTimeLeadingCoefficient
              (NontrivialZetaZero.conjugatePartner rho) /
            pairedEtaLocalizedGaussianLargeTimeLeadingCoefficient rho)) := by
  rw [
    pairedEtaLocalizedGaussianLargeTimeLeadingCoefficient_conjugatePartner_div_eq_norm_defect_div_sq]
  have hlowerPartner :=
    tendsto_pairedEtaLeadingLogGapMomentNearSharpFiniteLower
      (NontrivialZetaZero.conjugatePartner rho)
  have hupperRho :=
    tendsto_pairedEtaLogLaplaceMomentNearSharpFiniteUpper
      (analyticZetaZeroMultiplicity rho)
      (NontrivialZetaZero.zero_lt_re rho)
  rw [← pairedEtaLeadingLogGapMomentDefect_eq_logLaplaceMoment] at hupperRho
  have hratio := hlowerPartner.div hupperRho
    (norm_ne_zero_iff.mpr (pairedEtaLeadingLogGapMomentDefect_ne_zero rho))
  simpa [pairedEtaLeadingCoefficientRatioNearSharpEnclosureLower,
    analyticZetaZeroMultiplicity_conjugatePartner] using hratio.pow 2

/-- The near-sharp upper endpoints converge to the exact complementary
leading-coefficient ratio. -/
theorem tendsto_pairedEtaLeadingCoefficientRatioNearSharpEnclosureUpper
    (rho : NontrivialZetaZero) :
    Tendsto (fun N : ℕ ↦
      pairedEtaLeadingCoefficientRatioNearSharpEnclosureUpper rho N)
      atTop
      (nhds
        (pairedEtaLocalizedGaussianLargeTimeLeadingCoefficient
              (NontrivialZetaZero.conjugatePartner rho) /
            pairedEtaLocalizedGaussianLargeTimeLeadingCoefficient rho)) := by
  rw [
    pairedEtaLocalizedGaussianLargeTimeLeadingCoefficient_conjugatePartner_div_eq_norm_defect_div_sq]
  have hupperPartner :
      Tendsto (fun N : ℕ ↦
        pairedEtaLogLaplaceMomentNearSharpFiniteUpper
          (analyticZetaZeroMultiplicity rho)
          (NontrivialZetaZero.conjugatePartner rho).1 N)
        atTop
        (nhds ‖pairedEtaLeadingLogGapMomentDefect
          (NontrivialZetaZero.conjugatePartner rho)‖) := by
    rw [pairedEtaLeadingLogGapMomentDefect_eq_logLaplaceMoment]
    simpa only [analyticZetaZeroMultiplicity_conjugatePartner] using
      tendsto_pairedEtaLogLaplaceMomentNearSharpFiniteUpper
        (analyticZetaZeroMultiplicity
          (NontrivialZetaZero.conjugatePartner rho))
        (NontrivialZetaZero.zero_lt_re
          (NontrivialZetaZero.conjugatePartner rho))
  have hlowerRho :=
    tendsto_pairedEtaLeadingLogGapMomentNearSharpFiniteLower rho
  have hratio := hupperPartner.div hlowerRho
    (norm_ne_zero_iff.mpr (pairedEtaLeadingLogGapMomentDefect_ne_zero rho))
  simpa [pairedEtaLeadingCoefficientRatioNearSharpEnclosureUpper,
    analyticZetaZeroMultiplicity_conjugatePartner] using hratio.pow 2

/-- The near-sharp enclosure width tends to zero. -/
theorem tendsto_pairedEtaLeadingCoefficientRatioNearSharpEnclosure_width_zero
    (rho : NontrivialZetaZero) :
    Tendsto (fun N : ℕ ↦
      pairedEtaLeadingCoefficientRatioNearSharpEnclosureUpper rho N -
        pairedEtaLeadingCoefficientRatioNearSharpEnclosureLower rho N)
      atTop (nhds 0) := by
  have hupper :=
    tendsto_pairedEtaLeadingCoefficientRatioNearSharpEnclosureUpper rho
  have hlower :=
    tendsto_pairedEtaLeadingCoefficientRatioNearSharpEnclosureLower rho
  simpa only [sub_self] using hupper.sub hlower

/-- Both near-sharp cutoff conditions hold eventually for every complementary
zero pair. -/
theorem eventually_pairedEtaLeadingCoefficientRatioNearSharp_cutoffs
    (rho : NontrivialZetaZero) :
    ∀ᶠ N : ℕ in atTop,
      (((analyticZetaZeroMultiplicity rho + 1 : ℕ) : ℝ)) <
          (NontrivialZetaZero.conjugatePartner rho).1.re *
            Real.log (((2 * N + 1 : ℕ) : ℝ)) ∧
        (((analyticZetaZeroMultiplicity rho + 1 : ℕ) : ℝ)) <
          rho.1.re * Real.log (((2 * N + 1 : ℕ) : ℝ)) := by
  filter_upwards
    [eventually_pairedEtaLogLaplaceMoment_nearSharp_cutoff
      (analyticZetaZeroMultiplicity rho)
      (NontrivialZetaZero.zero_lt_re
        (NontrivialZetaZero.conjugatePartner rho)),
    eventually_pairedEtaLogLaplaceMoment_nearSharp_cutoff
      (analyticZetaZeroMultiplicity rho)
      (NontrivialZetaZero.zero_lt_re rho)] with N hpartner hrho
  exact ⟨hpartner, hrho⟩

/-- Eventually, the near-sharp endpoints form a rigorous two-sided enclosure
of the exact complementary coefficient ratio. -/
theorem eventually_pairedEtaLeadingCoefficientRatio_mem_nearSharpEnclosure
    (rho : NontrivialZetaZero) :
    ∀ᶠ N : ℕ in atTop,
      pairedEtaLeadingCoefficientRatioNearSharpEnclosureLower rho N ≤
          pairedEtaLocalizedGaussianLargeTimeLeadingCoefficient
                (NontrivialZetaZero.conjugatePartner rho) /
              pairedEtaLocalizedGaussianLargeTimeLeadingCoefficient rho ∧
        pairedEtaLocalizedGaussianLargeTimeLeadingCoefficient
                (NontrivialZetaZero.conjugatePartner rho) /
              pairedEtaLocalizedGaussianLargeTimeLeadingCoefficient rho ≤
          pairedEtaLeadingCoefficientRatioNearSharpEnclosureUpper rho N := by
  filter_upwards
    [eventually_pairedEtaLeadingCoefficientRatioNearSharp_cutoffs rho,
    eventually_pairedEtaLeadingLogGapMomentNearSharpFiniteLower_pos rho]
      with N hcutoffs hlower
  exact ⟨
    pairedEtaLeadingCoefficientRatioNearSharpEnclosureLower_le_exact
      rho N hcutoffs.1 hcutoffs.2,
    pairedEtaLeadingCoefficientRatio_exact_le_nearSharpEnclosureUpper
      rho N hcutoffs.1 hcutoffs.2 hlower⟩

/-- A valid finite near-sharp upper endpoint is strictly greater than one for
every zero on or to the right of the critical line.  Off the line this follows
from the exact coefficient gain; on the line it is the unavoidable positive
tail gap between prefix-plus-tail and prefix-minus-tail. -/
theorem one_lt_pairedEtaLeadingCoefficientRatioNearSharpEnclosureUpper_of_half_le_re
    (rho : NontrivialZetaZero) (N : ℕ)
    (hpartnerCutoff :
      (((analyticZetaZeroMultiplicity rho + 1 : ℕ) : ℝ)) <
        (NontrivialZetaZero.conjugatePartner rho).1.re *
          Real.log (((2 * N + 1 : ℕ) : ℝ)))
    (hrhoCutoff :
      (((analyticZetaZeroMultiplicity rho + 1 : ℕ) : ℝ)) <
        rho.1.re * Real.log (((2 * N + 1 : ℕ) : ℝ)))
    (hlower : 0 < pairedEtaLogLaplaceMomentNearSharpFiniteLower
      (analyticZetaZeroMultiplicity rho) rho.1 N)
    (hhalf : 1 / 2 ≤ rho.1.re) :
    1 < pairedEtaLeadingCoefficientRatioNearSharpEnclosureUpper rho N := by
  rcases hhalf.eq_or_lt with hline | hright
  · have hpartner : NontrivialZetaZero.conjugatePartner rho = rho := by
      apply Subtype.ext
      rw [NontrivialZetaZero.conjugatePartner_coe]
      apply Complex.ext
      · simp only [Complex.sub_re, Complex.one_re, Complex.conj_re]
        linarith
      · simp
    have hstrict :=
      pairedEtaLogLaplaceMomentNearSharpFiniteLower_lt_finiteUpper
        (analyticZetaZeroMultiplicity rho)
        (NontrivialZetaZero.zero_lt_re rho) N hrhoCutoff
    have hratioGt :
        1 < pairedEtaLogLaplaceMomentNearSharpFiniteUpper
              (analyticZetaZeroMultiplicity rho) rho.1 N /
            pairedEtaLogLaplaceMomentNearSharpFiniteLower
              (analyticZetaZeroMultiplicity rho) rho.1 N :=
      (one_lt_div₀ hlower).2 hstrict
    unfold pairedEtaLeadingCoefficientRatioNearSharpEnclosureUpper
    rw [hpartner]
    nlinarith
  · have hratioExact :
        1 < pairedEtaLocalizedGaussianLargeTimeLeadingCoefficient
              (NontrivialZetaZero.conjugatePartner rho) /
            pairedEtaLocalizedGaussianLargeTimeLeadingCoefficient rho := by
      apply (one_lt_div₀
        (pairedEtaLocalizedGaussianLargeTimeLeadingCoefficient_pos rho)).2
      exact
        (pairedEtaLocalizedGaussianLargeTimeLeadingCoefficient_lt_conjugatePartner_iff_half_lt_re
          rho).2 hright
    exact hratioExact.trans_le
      (pairedEtaLeadingCoefficientRatio_exact_le_nearSharpEnclosureUpper
        rho N hpartnerCutoff hrhoCutoff hlower)

/-- With a positive denominator and a valid partner upper certificate, the
near-sharp ratio endpoint is at most one exactly when the partner upper moment
certificate is at most the original lower certificate. -/
theorem pairedEtaLeadingCoefficientRatioNearSharpEnclosureUpper_le_one_iff
    (rho : NontrivialZetaZero) (N : ℕ)
    (hpartnerCutoff :
      (((analyticZetaZeroMultiplicity rho + 1 : ℕ) : ℝ)) <
        (NontrivialZetaZero.conjugatePartner rho).1.re *
          Real.log (((2 * N + 1 : ℕ) : ℝ)))
    (hlower : 0 < pairedEtaLogLaplaceMomentNearSharpFiniteLower
      (analyticZetaZeroMultiplicity rho) rho.1 N) :
    pairedEtaLeadingCoefficientRatioNearSharpEnclosureUpper rho N ≤ 1 ↔
      pairedEtaLogLaplaceMomentNearSharpFiniteUpper
          (analyticZetaZeroMultiplicity rho)
          (NontrivialZetaZero.conjugatePartner rho).1 N ≤
        pairedEtaLogLaplaceMomentNearSharpFiniteLower
          (analyticZetaZeroMultiplicity rho) rho.1 N := by
  have hupperPartner :
      ‖pairedEtaLeadingLogGapMomentDefect
          (NontrivialZetaZero.conjugatePartner rho)‖ ≤
        pairedEtaLogLaplaceMomentNearSharpFiniteUpper
          (analyticZetaZeroMultiplicity rho)
          (NontrivialZetaZero.conjugatePartner rho).1 N := by
    simpa only [analyticZetaZeroMultiplicity_conjugatePartner] using
      norm_pairedEtaLeadingLogGapMomentDefect_le_nearSharpFiniteUpper
        (NontrivialZetaZero.conjugatePartner rho) N
        (by simpa only [analyticZetaZeroMultiplicity_conjugatePartner] using
          hpartnerCutoff)
  have hupperPos :
      0 < pairedEtaLogLaplaceMomentNearSharpFiniteUpper
          (analyticZetaZeroMultiplicity rho)
          (NontrivialZetaZero.conjugatePartner rho).1 N :=
    (norm_pos_iff.mpr
      (pairedEtaLeadingLogGapMomentDefect_ne_zero
        (NontrivialZetaZero.conjugatePartner rho))).trans_le hupperPartner
  let A := pairedEtaLogLaplaceMomentNearSharpFiniteUpper
    (analyticZetaZeroMultiplicity rho)
    (NontrivialZetaZero.conjugatePartner rho).1 N
  let B := pairedEtaLogLaplaceMomentNearSharpFiniteLower
    (analyticZetaZeroMultiplicity rho) rho.1 N
  change (A / B) ^ 2 ≤ 1 ↔ A ≤ B
  have hA : 0 < A := by simpa [A] using hupperPos
  have hB : 0 < B := by simpa [B] using hlower
  have hdivNonneg : 0 ≤ A / B := div_nonneg hA.le hB.le
  constructor
  · intro hsq
    apply (div_le_one₀ hB).mp
    nlinarith
  · intro hle
    have hdivLe : A / B ≤ 1 := (div_le_one₀ hB).2 hle
    nlinarith

/-- The over-strong zero-slack condition is a literal finite phase-sensitive
prefix separation: partner prefix plus tail is at most original prefix minus
tail. -/
theorem
    pairedEtaLeadingCoefficientRatioNearSharpEnclosureUpper_le_one_iff_prefix_separation
    (rho : NontrivialZetaZero) (N : ℕ)
    (hpartnerCutoff :
      (((analyticZetaZeroMultiplicity rho + 1 : ℕ) : ℝ)) <
        (NontrivialZetaZero.conjugatePartner rho).1.re *
          Real.log (((2 * N + 1 : ℕ) : ℝ)))
    (hlower : 0 < pairedEtaLogLaplaceMomentNearSharpFiniteLower
      (analyticZetaZeroMultiplicity rho) rho.1 N) :
    pairedEtaLeadingCoefficientRatioNearSharpEnclosureUpper rho N ≤ 1 ↔
      ‖pairedEtaLogLaplaceMomentPartialSum
          (analyticZetaZeroMultiplicity rho)
          (NontrivialZetaZero.conjugatePartner rho).1 N‖ +
          pairedEtaLogLaplaceMomentNearSharpTailUpper
            (analyticZetaZeroMultiplicity rho)
            (NontrivialZetaZero.conjugatePartner rho).1.re N ≤
        ‖pairedEtaLogLaplaceMomentPartialSum
          (analyticZetaZeroMultiplicity rho) rho.1 N‖ -
          pairedEtaLogLaplaceMomentNearSharpTailUpper
            (analyticZetaZeroMultiplicity rho) rho.1.re N := by
  have hdiff :
      0 < ‖pairedEtaLogLaplaceMomentPartialSum
            (analyticZetaZeroMultiplicity rho) rho.1 N‖ -
          pairedEtaLogLaplaceMomentNearSharpTailUpper
            (analyticZetaZeroMultiplicity rho) rho.1.re N := by
    by_contra hnot
    have hle :
        ‖pairedEtaLogLaplaceMomentPartialSum
              (analyticZetaZeroMultiplicity rho) rho.1 N‖ -
            pairedEtaLogLaplaceMomentNearSharpTailUpper
              (analyticZetaZeroMultiplicity rho) rho.1.re N ≤ 0 :=
      le_of_not_gt hnot
    unfold pairedEtaLogLaplaceMomentNearSharpFiniteLower at hlower
    rw [max_eq_left hle] at hlower
    exact (lt_irrefl 0 hlower)
  rw [pairedEtaLeadingCoefficientRatioNearSharpEnclosureUpper_le_one_iff
    rho N hpartnerCutoff hlower]
  unfold pairedEtaLogLaplaceMomentNearSharpFiniteUpper
    pairedEtaLogLaplaceMomentNearSharpFiniteLower
  rw [max_eq_right hdiff.le]

/-- The stronger one-cutoff prefix-plus-tail versus prefix-minus-tail
separation is impossible for a zero on or to the right of the critical line.
This rules out the superficially attractive but vacuous `upper ≤ 1` target. -/
theorem not_nearSharp_prefix_plus_tail_le_prefix_minus_tail_of_half_le_re
    (rho : NontrivialZetaZero) (N : ℕ)
    (hpartnerCutoff :
      (((analyticZetaZeroMultiplicity rho + 1 : ℕ) : ℝ)) <
        (NontrivialZetaZero.conjugatePartner rho).1.re *
          Real.log (((2 * N + 1 : ℕ) : ℝ)))
    (hrhoCutoff :
      (((analyticZetaZeroMultiplicity rho + 1 : ℕ) : ℝ)) <
        rho.1.re * Real.log (((2 * N + 1 : ℕ) : ℝ)))
    (hlower : 0 < pairedEtaLogLaplaceMomentNearSharpFiniteLower
      (analyticZetaZeroMultiplicity rho) rho.1 N)
    (hhalf : 1 / 2 ≤ rho.1.re)
    : ¬ (
      ‖pairedEtaLogLaplaceMomentPartialSum
          (analyticZetaZeroMultiplicity rho)
          (NontrivialZetaZero.conjugatePartner rho).1 N‖ +
          pairedEtaLogLaplaceMomentNearSharpTailUpper
            (analyticZetaZeroMultiplicity rho)
            (NontrivialZetaZero.conjugatePartner rho).1.re N ≤
        ‖pairedEtaLogLaplaceMomentPartialSum
          (analyticZetaZeroMultiplicity rho) rho.1 N‖ -
          pairedEtaLogLaplaceMomentNearSharpTailUpper
            (analyticZetaZeroMultiplicity rho) rho.1.re N) := by
  intro hseparation
  have hleOne :=
    (pairedEtaLeadingCoefficientRatioNearSharpEnclosureUpper_le_one_iff_prefix_separation
      rho N hpartnerCutoff hlower).2 hseparation
  have hgtOne :=
    one_lt_pairedEtaLeadingCoefficientRatioNearSharpEnclosureUpper_of_half_le_re
      rho N hpartnerCutoff hrhoCutoff hlower hhalf
  linarith

/-- The intrinsic finite uncertainty at `rho`: its own upper-to-lower squared
ratio minus one.  Unlike the impossible zero-slack target, this quantity is
positive at valid finite cutoffs and converges to zero. -/
def pairedEtaLeadingCoefficientRatioNearSharpSelfSlack
    (rho : NontrivialZetaZero) (N : ℕ) : ℝ :=
  (pairedEtaLogLaplaceMomentNearSharpFiniteUpper
        (analyticZetaZeroMultiplicity rho) rho.1 N /
      pairedEtaLogLaplaceMomentNearSharpFiniteLower
        (analyticZetaZeroMultiplicity rho) rho.1 N) ^ 2 - 1

/-- At a valid cutoff with positive lower certificate, the intrinsic
near-sharp self-slack is strictly positive. -/
theorem zero_lt_pairedEtaLeadingCoefficientRatioNearSharpSelfSlack
    (rho : NontrivialZetaZero) (N : ℕ)
    (hrhoCutoff :
      (((analyticZetaZeroMultiplicity rho + 1 : ℕ) : ℝ)) <
        rho.1.re * Real.log (((2 * N + 1 : ℕ) : ℝ)))
    (hlower : 0 < pairedEtaLogLaplaceMomentNearSharpFiniteLower
      (analyticZetaZeroMultiplicity rho) rho.1 N) :
    0 < pairedEtaLeadingCoefficientRatioNearSharpSelfSlack rho N := by
  have hstrict :=
    pairedEtaLogLaplaceMomentNearSharpFiniteLower_lt_finiteUpper
      (analyticZetaZeroMultiplicity rho)
      (NontrivialZetaZero.zero_lt_re rho) N hrhoCutoff
  have hratio :
      1 < pairedEtaLogLaplaceMomentNearSharpFiniteUpper
            (analyticZetaZeroMultiplicity rho) rho.1 N /
          pairedEtaLogLaplaceMomentNearSharpFiniteLower
            (analyticZetaZeroMultiplicity rho) rho.1 N :=
    (one_lt_div₀ hlower).2 hstrict
  unfold pairedEtaLeadingCoefficientRatioNearSharpSelfSlack
  nlinarith

/-- The intrinsic near-sharp self-slack tends to zero. -/
theorem tendsto_pairedEtaLeadingCoefficientRatioNearSharpSelfSlack_zero
    (rho : NontrivialZetaZero) :
    Tendsto (pairedEtaLeadingCoefficientRatioNearSharpSelfSlack rho)
      atTop (nhds 0) := by
  have hupper :=
    tendsto_pairedEtaLogLaplaceMomentNearSharpFiniteUpper
      (analyticZetaZeroMultiplicity rho)
      (NontrivialZetaZero.zero_lt_re rho)
  rw [← pairedEtaLeadingLogGapMomentDefect_eq_logLaplaceMoment] at hupper
  have hlower :=
    tendsto_pairedEtaLeadingLogGapMomentNearSharpFiniteLower rho
  have hnormNe : ‖pairedEtaLeadingLogGapMomentDefect rho‖ ≠ 0 :=
    norm_ne_zero_iff.mpr (pairedEtaLeadingLogGapMomentDefect_ne_zero rho)
  have hratio := hupper.div hlower hnormNe
  have hlimit := (hratio.pow 2).sub
    (tendsto_const_nhds : Tendsto (fun _ : ℕ ↦ (1 : ℝ)) atTop (nhds 1))
  change Tendsto (fun N : ℕ ↦
    (pairedEtaLogLaplaceMomentNearSharpFiniteUpper
          (analyticZetaZeroMultiplicity rho) rho.1 N /
        pairedEtaLogLaplaceMomentNearSharpFiniteLower
          (analyticZetaZeroMultiplicity rho) rho.1 N) ^ 2 - 1)
    atTop (nhds 0)
  simpa [hnormNe] using hlimit

/-- Allowing the vanishing intrinsic self-slack converts the complementary
ratio bound into the non-vacuous comparison of the two prefix-plus-tail upper
certificates. -/
theorem
    pairedEtaLeadingCoefficientRatioNearSharpEnclosureUpper_le_one_add_selfSlack_iff
    (rho : NontrivialZetaZero) (N : ℕ)
    (hpartnerCutoff :
      (((analyticZetaZeroMultiplicity rho + 1 : ℕ) : ℝ)) <
        (NontrivialZetaZero.conjugatePartner rho).1.re *
          Real.log (((2 * N + 1 : ℕ) : ℝ)))
    (hrhoCutoff :
      (((analyticZetaZeroMultiplicity rho + 1 : ℕ) : ℝ)) <
        rho.1.re * Real.log (((2 * N + 1 : ℕ) : ℝ)))
    (hlower : 0 < pairedEtaLogLaplaceMomentNearSharpFiniteLower
      (analyticZetaZeroMultiplicity rho) rho.1 N) :
    pairedEtaLeadingCoefficientRatioNearSharpEnclosureUpper rho N ≤
        1 + pairedEtaLeadingCoefficientRatioNearSharpSelfSlack rho N ↔
      pairedEtaLogLaplaceMomentNearSharpFiniteUpper
          (analyticZetaZeroMultiplicity rho)
          (NontrivialZetaZero.conjugatePartner rho).1 N ≤
        pairedEtaLogLaplaceMomentNearSharpFiniteUpper
          (analyticZetaZeroMultiplicity rho) rho.1 N := by
  have hupperPartner :
      ‖pairedEtaLeadingLogGapMomentDefect
          (NontrivialZetaZero.conjugatePartner rho)‖ ≤
        pairedEtaLogLaplaceMomentNearSharpFiniteUpper
          (analyticZetaZeroMultiplicity rho)
          (NontrivialZetaZero.conjugatePartner rho).1 N := by
    simpa only [analyticZetaZeroMultiplicity_conjugatePartner] using
      norm_pairedEtaLeadingLogGapMomentDefect_le_nearSharpFiniteUpper
        (NontrivialZetaZero.conjugatePartner rho) N
        (by simpa only [analyticZetaZeroMultiplicity_conjugatePartner] using
          hpartnerCutoff)
  have hupperRho :
      ‖pairedEtaLeadingLogGapMomentDefect rho‖ ≤
        pairedEtaLogLaplaceMomentNearSharpFiniteUpper
          (analyticZetaZeroMultiplicity rho) rho.1 N :=
    norm_pairedEtaLeadingLogGapMomentDefect_le_nearSharpFiniteUpper
      rho N hrhoCutoff
  let A := pairedEtaLogLaplaceMomentNearSharpFiniteUpper
    (analyticZetaZeroMultiplicity rho)
    (NontrivialZetaZero.conjugatePartner rho).1 N
  let B := pairedEtaLogLaplaceMomentNearSharpFiniteLower
    (analyticZetaZeroMultiplicity rho) rho.1 N
  let C := pairedEtaLogLaplaceMomentNearSharpFiniteUpper
    (analyticZetaZeroMultiplicity rho) rho.1 N
  have hA : 0 < A := by
    dsimp [A]
    exact (norm_pos_iff.mpr
      (pairedEtaLeadingLogGapMomentDefect_ne_zero
        (NontrivialZetaZero.conjugatePartner rho))).trans_le hupperPartner
  have hB : 0 < B := by simpa [B] using hlower
  have hC : 0 < C := by
    dsimp [C]
    exact (norm_pos_iff.mpr
      (pairedEtaLeadingLogGapMomentDefect_ne_zero rho)).trans_le hupperRho
  change (A / B) ^ 2 ≤ 1 + ((C / B) ^ 2 - 1) ↔ A ≤ C
  rw [show 1 + ((C / B) ^ 2 - 1) = (C / B) ^ 2 by ring]
  have hAB : 0 ≤ A / B := div_nonneg hA.le hB.le
  have hCB : 0 ≤ C / B := div_nonneg hC.le hB.le
  constructor
  · intro hsq
    apply (div_le_div_iff_of_pos_right hB).mp
    nlinarith
  · intro hle
    have hdiv : A / B ≤ C / B :=
      (div_le_div_iff_of_pos_right hB).2 hle
    nlinarith

/-- Eventual horizontal monotonicity of the near-sharp finite upper
certificates forces a right-half zero onto the critical line.  This is the
non-vacuous finite arithmetic frontier exposed by the enclosure. -/
theorem re_eq_half_of_eventually_nearSharpFiniteUpper_conjugatePartner_le
    (rho : NontrivialZetaZero) (hhalf : 1 / 2 ≤ rho.1.re)
    (hupper : ∀ᶠ N : ℕ in atTop,
      pairedEtaLogLaplaceMomentNearSharpFiniteUpper
          (analyticZetaZeroMultiplicity rho)
          (NontrivialZetaZero.conjugatePartner rho).1 N ≤
        pairedEtaLogLaplaceMomentNearSharpFiniteUpper
          (analyticZetaZeroMultiplicity rho) rho.1 N) :
    rho.1.re = 1 / 2 := by
  have hpartnerLimit :
      Tendsto (fun N : ℕ ↦
        pairedEtaLogLaplaceMomentNearSharpFiniteUpper
          (analyticZetaZeroMultiplicity rho)
          (NontrivialZetaZero.conjugatePartner rho).1 N)
        atTop
        (nhds ‖pairedEtaLeadingLogGapMomentDefect
          (NontrivialZetaZero.conjugatePartner rho)‖) := by
    rw [pairedEtaLeadingLogGapMomentDefect_eq_logLaplaceMoment]
    simpa only [analyticZetaZeroMultiplicity_conjugatePartner] using
      tendsto_pairedEtaLogLaplaceMomentNearSharpFiniteUpper
        (analyticZetaZeroMultiplicity
          (NontrivialZetaZero.conjugatePartner rho))
        (NontrivialZetaZero.zero_lt_re
          (NontrivialZetaZero.conjugatePartner rho))
  have hrhoLimit :=
    tendsto_pairedEtaLogLaplaceMomentNearSharpFiniteUpper
      (analyticZetaZeroMultiplicity rho)
      (NontrivialZetaZero.zero_lt_re rho)
  rw [← pairedEtaLeadingLogGapMomentDefect_eq_logLaplaceMoment] at hrhoLimit
  have hnormLe :
      ‖pairedEtaLeadingLogGapMomentDefect
          (NontrivialZetaZero.conjugatePartner rho)‖ ≤
        ‖pairedEtaLeadingLogGapMomentDefect rho‖ :=
    le_of_tendsto_of_tendsto hpartnerLimit hrhoLimit hupper
  rcases hhalf.eq_or_lt with hline | hright
  · exact hline.symm
  · have hdenPos : 0 < ‖pairedEtaLeadingLogGapMomentDefect rho‖ :=
      norm_pos_iff.mpr (pairedEtaLeadingLogGapMomentDefect_ne_zero rho)
    have hdivLe :
        ‖pairedEtaLeadingLogGapMomentDefect
              (NontrivialZetaZero.conjugatePartner rho)‖ /
            ‖pairedEtaLeadingLogGapMomentDefect rho‖ ≤ 1 :=
      (div_le_one₀ hdenPos).2 hnormLe
    have hdivNonneg :
        0 ≤ ‖pairedEtaLeadingLogGapMomentDefect
              (NontrivialZetaZero.conjugatePartner rho)‖ /
            ‖pairedEtaLeadingLogGapMomentDefect rho‖ := by positivity
    have hsqLe :
        (‖pairedEtaLeadingLogGapMomentDefect
              (NontrivialZetaZero.conjugatePartner rho)‖ /
            ‖pairedEtaLeadingLogGapMomentDefect rho‖) ^ 2 ≤ 1 := by
      nlinarith
    have hsqGt :
        1 < (‖pairedEtaLeadingLogGapMomentDefect
              (NontrivialZetaZero.conjugatePartner rho)‖ /
            ‖pairedEtaLeadingLogGapMomentDefect rho‖) ^ 2 := by
      rw [←
        pairedEtaLocalizedGaussianLargeTimeLeadingCoefficient_conjugatePartner_div_eq_norm_defect_div_sq]
      apply (one_lt_div₀
        (pairedEtaLocalizedGaussianLargeTimeLeadingCoefficient_pos rho)).2
      exact
        (pairedEtaLocalizedGaussianLargeTimeLeadingCoefficient_lt_conjugatePartner_iff_half_lt_re
          rho).2 hright
    linarith

/-- On the critical line the two near-sharp finite upper certificates are
identical at every cutoff. -/
theorem pairedEtaLogLaplaceMomentNearSharpFiniteUpper_conjugatePartner_le_of_re_eq_half
    (rho : NontrivialZetaZero) (hline : rho.1.re = 1 / 2) :
    ∀ N : ℕ,
      pairedEtaLogLaplaceMomentNearSharpFiniteUpper
          (analyticZetaZeroMultiplicity rho)
          (NontrivialZetaZero.conjugatePartner rho).1 N ≤
        pairedEtaLogLaplaceMomentNearSharpFiniteUpper
          (analyticZetaZeroMultiplicity rho) rho.1 N := by
  have hpartner : NontrivialZetaZero.conjugatePartner rho = rho := by
    apply Subtype.ext
    rw [NontrivialZetaZero.conjugatePartner_coe]
    apply Complex.ext
    · simp only [Complex.sub_re, Complex.one_re, Complex.conj_re]
      linarith
    · simp
  intro N
  rw [hpartner]

/-- For a zero known to lie in the closed right half of the strip, eventual
near-sharp finite-upper monotonicity is equivalent to the critical-line
equation.  The critical-line-to-monotonicity direction is definitional
equality; the converse is the substantive closure theorem above. -/
theorem re_eq_half_iff_eventually_nearSharpFiniteUpper_conjugatePartner_le
    (rho : NontrivialZetaZero) (hhalf : 1 / 2 ≤ rho.1.re) :
    rho.1.re = 1 / 2 ↔
      ∀ᶠ N : ℕ in atTop,
        pairedEtaLogLaplaceMomentNearSharpFiniteUpper
            (analyticZetaZeroMultiplicity rho)
            (NontrivialZetaZero.conjugatePartner rho).1 N ≤
          pairedEtaLogLaplaceMomentNearSharpFiniteUpper
            (analyticZetaZeroMultiplicity rho) rho.1 N := by
  constructor
  · intro hline
    exact Eventually.of_forall
      (pairedEtaLogLaplaceMomentNearSharpFiniteUpper_conjugatePartner_le_of_re_eq_half
        rho hline)
  · exact re_eq_half_of_eventually_nearSharpFiniteUpper_conjugatePartner_le
      rho hhalf

/-- Equivalently, an eventual complementary upper-enclosure bound by one plus
the intrinsic vanishing self-slack forces a right-half zero onto the critical
line. -/
theorem
    re_eq_half_of_eventually_nearSharpEnclosureUpper_le_one_add_selfSlack
    (rho : NontrivialZetaZero) (hhalf : 1 / 2 ≤ rho.1.re)
    (hbound : ∀ᶠ N : ℕ in atTop,
      pairedEtaLeadingCoefficientRatioNearSharpEnclosureUpper rho N ≤
        1 + pairedEtaLeadingCoefficientRatioNearSharpSelfSlack rho N) :
    rho.1.re = 1 / 2 := by
  apply re_eq_half_of_eventually_nearSharpFiniteUpper_conjugatePartner_le
    rho hhalf
  filter_upwards
    [hbound,
    eventually_pairedEtaLeadingCoefficientRatioNearSharp_cutoffs rho,
    eventually_pairedEtaLeadingLogGapMomentNearSharpFiniteLower_pos rho]
      with N hN hcutoffs hlower
  exact
    (pairedEtaLeadingCoefficientRatioNearSharpEnclosureUpper_le_one_add_selfSlack_iff
      rho N hcutoffs.1 hcutoffs.2 hlower).1 hN

/-- At high ordinate, every valid near-sharp upper endpoint gives the explicit
horizontal displacement bound inherited from multiplier coercivity. -/
theorem re_sub_half_le_100_mul_realLog_nearSharpEnclosureUpper_of_eight_le_abs_im
    (rho : NontrivialZetaZero) (N : ℕ)
    (hpartnerCutoff :
      (((analyticZetaZeroMultiplicity rho + 1 : ℕ) : ℝ)) <
        (NontrivialZetaZero.conjugatePartner rho).1.re *
          Real.log (((2 * N + 1 : ℕ) : ℝ)))
    (hrhoCutoff :
      (((analyticZetaZeroMultiplicity rho + 1 : ℕ) : ℝ)) <
        rho.1.re * Real.log (((2 * N + 1 : ℕ) : ℝ)))
    (hlower : 0 < pairedEtaLogLaplaceMomentNearSharpFiniteLower
      (analyticZetaZeroMultiplicity rho) rho.1 N)
    (hhalf : 1 / 2 ≤ rho.1.re) (hy : 8 ≤ |rho.1.im|) :
    rho.1.re - 1 / 2 ≤
      100 * Real.log
        (pairedEtaLeadingCoefficientRatioNearSharpEnclosureUpper rho N) := by
  have hdisplacement :=
    one_over_100_mul_abs_re_sub_half_le_abs_realLog_leadingCoefficient_ratio_of_eight_le_abs_im
      rho hy
  have hratioBound :=
    pairedEtaLeadingCoefficientRatio_exact_le_nearSharpEnclosureUpper
      rho N hpartnerCutoff hrhoCutoff hlower
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
          (pairedEtaLeadingCoefficientRatioNearSharpEnclosureUpper rho N) :=
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

end
end RiemannGaussian
