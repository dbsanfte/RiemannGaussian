import RiemannGaussian.RiemannXiSuzukiPositiveCriticalStripEtaLeadingLogMomentFiniteCenteredResidualFiniteWorkCriticalScaleRigidity

/-!
# Reduction of the finite-work frontier to one square-root prefix bound

The only critical-scale obstruction in the exact finite work is the top
transport

`T_N = m * Delta_N * C_(m-1,N+1)`.

Here `m` is the analytic zero multiplicity, `Delta_N` is the one-step
logarithmic cutoff shift, and `C_(m-1,N+1)` is a literal finite completed
eta-prefix coupling.  Since `(2N+1) * Delta_N -> 2`, the critical
`(2N+1)^(3/2)` bound on `T_N` is exactly equivalent to a
`(2N+1)^(1/2)` bound on that one coupled prefix.

This module proves the equivalence in Lean and packages the resulting global
prefix estimate as a sufficient condition for RH.  The prefix estimate itself
is not proved.
-/

open Complex Filter MeasureTheory Metric Set Topology
open scoped Classical ComplexConjugate ENNReal Interval Topology

namespace RiemannGaussian

noncomputable section

/-- The unique order-`m-1` finite completed eta-prefix coupling left after all
known critical-scale work terms have been removed. -/
def pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidualFiniteWorkTopPrefix
    (rho : NontrivialZetaZero) (N : ℕ) : ℂ :=
  pairedEtaCompletedLeadingLogCutoffCenteredFinitePrefixCoupledMoment
    rho (analyticZetaZeroMultiplicity rho - 1) (N + 1)

/-- Exact factorization of the top transport through the top prefix. -/
theorem
    pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidualFiniteWorkTopTransport_eq_multiplicity_mul_shift_mul_topPrefix
    (rho : NontrivialZetaZero) (N : ℕ) :
    pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidualFiniteWorkTopTransport
        rho N =
      (((analyticZetaZeroMultiplicity rho : ℕ) : ℂ) *
        (pairedEtaLogTailShiftIncrement N : ℂ)) *
        pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidualFiniteWorkTopPrefix
          rho N := by
  rw [
    pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidualFiniteWorkTopTransport_eq]
  rfl

/-- Exact real scale identity.  It exhibits the top work at exponent `3/2`
as a known positive factor times the top prefix at exponent `1/2`. -/
theorem
    oddEndpoint_threeHalves_rpow_mul_norm_topTransport_eq_multiplicity_mul_scaledShift_mul_half_rpow_mul_norm_topPrefix
    (rho : NontrivialZetaZero) (N : ℕ) :
    (((2 * N + 1 : ℕ) : ℝ) ^ (3 / 2 : ℝ)) *
        ‖pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidualFiniteWorkTopTransport
          rho N‖ =
      ((analyticZetaZeroMultiplicity rho : ℕ) : ℝ) *
          (((2 * N + 1 : ℕ) : ℝ) *
            pairedEtaLogTailShiftIncrement N) *
        ((((2 * N + 1 : ℕ) : ℝ) ^ (1 / 2 : ℝ)) *
          ‖pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidualFiniteWorkTopPrefix
            rho N‖) := by
  let m := analyticZetaZeroMultiplicity rho
  let x : ℝ := ((2 * N + 1 : ℕ) : ℝ)
  let delta : ℝ := pairedEtaLogTailShiftIncrement N
  let P : ℂ :=
    pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidualFiniteWorkTopPrefix
      rho N
  have hx : 0 < x := by dsimp [x]; positivity
  have hdelta : 0 < delta := by
    simpa only [delta] using pairedEtaLogTailShiftIncrement_pos N
  have hxpow : x ^ (3 / 2 : ℝ) = x * x ^ (1 / 2 : ℝ) := by
    rw [show (3 / 2 : ℝ) = 1 + 1 / 2 by ring, Real.rpow_add hx,
      Real.rpow_one]
  rw [
    pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidualFiniteWorkTopTransport_eq_multiplicity_mul_shift_mul_topPrefix]
  change x ^ (3 / 2 : ℝ) * ‖(((m : ℕ) : ℂ) * (delta : ℂ)) * P‖ =
    (m : ℝ) * (x * delta) * (x ^ (1 / 2 : ℝ) * ‖P‖)
  rw [norm_mul, norm_mul, norm_natCast, norm_real, Real.norm_eq_abs,
    abs_of_pos hdelta, hxpow]
  ring

/-- The actual remaining local arithmetic statement: the single order-`m-1`
coupled finite prefix is eventually bounded at the square-root scale. -/
def PairedEtaCompletedLeadingLogCutoffCenteredPartnerResidualFiniteWorkTopPrefixCriticalScaleEventuallyBounded
    (rho : NontrivialZetaZero) : Prop :=
  ∃ C : ℝ, ∀ᶠ N : ℕ in atTop,
    (((2 * N + 1 : ℕ) : ℝ) ^ (1 / 2 : ℝ)) *
        ‖pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidualFiniteWorkTopPrefix
          rho N‖ ≤ C

/-- At one zero, critical `3/2` boundedness of the top work is exactly
equivalent to square-root boundedness of its coupled prefix. -/
theorem
    pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidualFiniteWorkTopTransport_criticalScale_eventuallyBounded_iff_topPrefix
    (rho : NontrivialZetaZero) :
    (∃ C : ℝ, ∀ᶠ N : ℕ in atTop,
      (((2 * N + 1 : ℕ) : ℝ) ^ (3 / 2 : ℝ)) *
          ‖pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidualFiniteWorkTopTransport
            rho N‖ ≤ C) ↔
      PairedEtaCompletedLeadingLogCutoffCenteredPartnerResidualFiniteWorkTopPrefixCriticalScaleEventuallyBounded
        rho := by
  let m := analyticZetaZeroMultiplicity rho
  have hmPos : 0 < m := analyticZetaZeroMultiplicity_positive rho
  have hmOne : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hmPos
  constructor
  · rintro ⟨C, htop⟩
    refine ⟨C, ?_⟩
    have hshiftLower :=
      tendsto_oddEndpoint_mul_pairedEtaLogTailShiftIncrement_two.eventually_const_lt
        (by norm_num : (1 : ℝ) < 2)
    filter_upwards [htop, hshiftLower] with N htopN hshiftN
    let x : ℝ := ((2 * N + 1 : ℕ) : ℝ)
    let delta : ℝ := pairedEtaLogTailShiftIncrement N
    let prefixScale : ℝ :=
      x ^ (1 / 2 : ℝ) *
        ‖pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidualFiniteWorkTopPrefix
          rho N‖
    have hprefixNonneg : 0 ≤ prefixScale := by
      dsimp only [prefixScale]
      positivity
    have hfactor : 1 ≤ (m : ℝ) * (x * delta) := by
      calc
        (1 : ℝ) = 1 * 1 := by ring
        _ ≤ (m : ℝ) * (x * delta) :=
          mul_le_mul hmOne hshiftN.le (by norm_num) (by positivity)
    calc
      prefixScale = 1 * prefixScale := by rw [one_mul]
      _ ≤ ((m : ℝ) * (x * delta)) * prefixScale :=
        mul_le_mul_of_nonneg_right hfactor hprefixNonneg
      _ = (((2 * N + 1 : ℕ) : ℝ) ^ (3 / 2 : ℝ)) *
          ‖pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidualFiniteWorkTopTransport
            rho N‖ := by
        symm
        simpa only [m, x, delta, prefixScale] using
          (oddEndpoint_threeHalves_rpow_mul_norm_topTransport_eq_multiplicity_mul_scaledShift_mul_half_rpow_mul_norm_topPrefix
            rho N)
      _ ≤ C := htopN
  · rintro ⟨C, hprefix⟩
    let C' : ℝ := max C 0
    refine ⟨(3 * (m : ℝ)) * C', ?_⟩
    have hshiftUpper :=
      tendsto_oddEndpoint_mul_pairedEtaLogTailShiftIncrement_two.eventually_lt_const
        (by norm_num : (2 : ℝ) < 3)
    filter_upwards [hprefix, hshiftUpper] with N hprefixN hshiftN
    let x : ℝ := ((2 * N + 1 : ℕ) : ℝ)
    let delta : ℝ := pairedEtaLogTailShiftIncrement N
    let prefixScale : ℝ :=
      x ^ (1 / 2 : ℝ) *
        ‖pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidualFiniteWorkTopPrefix
          rho N‖
    have hprefixNonneg : 0 ≤ prefixScale := by
      dsimp only [prefixScale]
      positivity
    have hprefixMax : prefixScale ≤ C' :=
      hprefixN.trans (le_max_left _ _)
    have hfactorUpper : (m : ℝ) * (x * delta) ≤ 3 * (m : ℝ) := by
      calc
        (m : ℝ) * (x * delta) ≤ (m : ℝ) * 3 :=
          mul_le_mul_of_nonneg_left hshiftN.le (by positivity)
        _ = 3 * (m : ℝ) := by ring
    rw [
      oddEndpoint_threeHalves_rpow_mul_norm_topTransport_eq_multiplicity_mul_scaledShift_mul_half_rpow_mul_norm_topPrefix]
    change ((m : ℝ) * (x * delta)) * prefixScale ≤ (3 * (m : ℝ)) * C'
    calc
      ((m : ℝ) * (x * delta)) * prefixScale ≤
          (3 * (m : ℝ)) * prefixScale :=
        mul_le_mul_of_nonneg_right hfactorUpper hprefixNonneg
      _ ≤ (3 * (m : ℝ)) * C' :=
        mul_le_mul_of_nonneg_left hprefixMax (by positivity)

/-- The global square-root top-prefix estimate. -/
def AllPairedEtaCompletedLeadingLogCutoffCenteredPartnerResidualFiniteWorkTopPrefixCriticalScaleEventuallyBounded :
    Prop :=
  ∀ rho : NontrivialZetaZero,
    PairedEtaCompletedLeadingLogCutoffCenteredPartnerResidualFiniteWorkTopPrefixCriticalScaleEventuallyBounded
      rho

/-- The global top-transport and top-prefix bounds are exactly equivalent. -/
theorem
    all_pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidualFiniteWorkTopTransport_criticalScale_eventuallyBounded_iff_topPrefix :
    AllPairedEtaCompletedLeadingLogCutoffCenteredPartnerResidualFiniteWorkTopTransportCriticalScaleEventuallyBounded ↔
      AllPairedEtaCompletedLeadingLogCutoffCenteredPartnerResidualFiniteWorkTopPrefixCriticalScaleEventuallyBounded := by
  constructor
  · intro htop rho
    exact
      (pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidualFiniteWorkTopTransport_criticalScale_eventuallyBounded_iff_topPrefix
        rho).mp (htop rho)
  · intro hprefix rho
    exact
      (pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidualFiniteWorkTopTransport_criticalScale_eventuallyBounded_iff_topPrefix
        rho).mpr (hprefix rho)

/-- The isolated global square-root cancellation estimate for the one explicit
order-`m-1` finite coupled prefix implies Mathlib's Riemann hypothesis. -/
theorem
    riemannHypothesis_of_all_pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidualFiniteWorkTopPrefix_criticalScale_eventuallyBounded
    (hprefix :
      AllPairedEtaCompletedLeadingLogCutoffCenteredPartnerResidualFiniteWorkTopPrefixCriticalScaleEventuallyBounded) :
    RiemannHypothesis := by
  exact
    riemannHypothesis_of_all_pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidualFiniteWorkTopTransport_criticalScale_eventuallyBounded
      (all_pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidualFiniteWorkTopTransport_criticalScale_eventuallyBounded_iff_topPrefix.mpr
        hprefix)

end

end RiemannGaussian
