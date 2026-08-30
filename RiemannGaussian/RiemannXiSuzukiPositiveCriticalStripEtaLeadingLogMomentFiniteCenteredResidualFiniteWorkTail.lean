import RiemannGaussian.RiemannXiSuzukiPositiveCriticalStripEtaLeadingLogMomentFiniteCenteredResidualCriticalScaleRigidity

/-!
# Finite-work tail criterion for the centered eta residual

The closed transport hierarchy gives the exact one-step work
`R_N - R_(N+1)` as one explicit shifted head interval plus a finite sum of
finite eta-prefix couplings.  Here that right-hand side is named and
telescoped over an arbitrary finite range.  Since `R_N -> 0`, its translated
finite work sums converge to the full residual `R_N`.

This produces a concrete sufficient arithmetic estimate for the critical
square-root residual bound: uniformly bound the square-root-scaled sums of
the norms of all finite work tails.  Lean proves that this absolute tail-work
condition gives the global critical-scale bound and therefore RH.  The
tail-work estimate itself is not proved; it is stronger than the signed
telescoping identity and is the new coercive arithmetic target.
-/

open Complex Filter MeasureTheory Metric Set Topology
open scoped Classical ComplexConjugate ENNReal Interval Topology

namespace RiemannGaussian

noncomputable section

/-- The completely finite one-step work in the cutoff-centered completed eta
residual: one shifted head term and the closed lower finite-prefix hierarchy. -/
def pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidualFiniteWork
    (rho : NontrivialZetaZero) (N : ℕ) : ℂ :=
  pairedEtaLogTailCutoffOscillation rho.1.im N *
      pairedEtaCompletedLeadingLogCutoffCenteredShiftedHeadCoupledMoment
        rho (analyticZetaZeroMultiplicity rho) N +
    ∑ j ∈ Finset.range (analyticZetaZeroMultiplicity rho),
      ((((analyticZetaZeroMultiplicity rho).choose j : ℕ) : ℂ) *
        (pairedEtaLogTailShiftIncrement N : ℂ) ^
          (analyticZetaZeroMultiplicity rho - j)) *
        pairedEtaCompletedLeadingLogCutoffCenteredFinitePrefixCoupledMoment
          rho j (N + 1)

/-- The finite work is exactly the consecutive residual difference. -/
theorem pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidual_sub_succ_eq_finiteWork
    (rho : NontrivialZetaZero) (N : ℕ) :
    pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidual rho N -
        pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidual rho (N + 1) =
      pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidualFiniteWork
        rho N := by
  exact
    pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidual_sub_succ_eq_finitePrefixHierarchy
      rho N

/-- Finite work telescopes exactly from cutoff `N` through cutoff `N+L`. -/
theorem sum_range_pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidualFiniteWork_eq_sub
    (rho : NontrivialZetaZero) (N L : ℕ) :
    ∑ q ∈ Finset.range L,
        pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidualFiniteWork
          rho (N + q) =
      pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidual rho N -
        pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidual rho (N + L) := by
  calc
    ∑ q ∈ Finset.range L,
          pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidualFiniteWork
            rho (N + q) =
        ∑ q ∈ Finset.range L,
          (pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidual
              rho (N + q) -
            pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidual
              rho ((N + q) + 1)) := by
      apply Finset.sum_congr rfl
      intro q hq
      exact
        (pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidual_sub_succ_eq_finiteWork
          rho (N + q)).symm
    _ = _ := by
      simpa only [Nat.add_zero, Nat.add_assoc] using
        (Finset.sum_range_sub'
          (fun q : ℕ =>
            pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidual
              rho (N + q)) L)

/-- At every fixed base cutoff, translated finite work sums converge to the
full residual because their terminal residual tends to zero. -/
theorem tendsto_sum_range_pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidualFiniteWork
    (rho : NontrivialZetaZero) (N : ℕ) :
    Tendsto (fun L : ℕ =>
      ∑ q ∈ Finset.range L,
        pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidualFiniteWork
          rho (N + q))
      atTop
      (nhds
        (pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidual rho N)) := by
  have hshift : Tendsto (fun L : ℕ => N + L) atTop atTop := by
    simpa only [Nat.add_comm] using Filter.tendsto_add_atTop_nat N
  have hterminal :=
    (tendsto_pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidual_zero
      rho).comp hshift
  have hconstant : Tendsto (fun _ : ℕ =>
      pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidual rho N)
      atTop
      (nhds
        (pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidual rho N)) :=
    tendsto_const_nhds
  have hdifference := hconstant.sub hterminal
  have hsum := hdifference.congr' (Eventually.of_forall fun L =>
    (sum_range_pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidualFiniteWork_eq_sub
      rho N L).symm)
  simpa only [sub_zero] using hsum

/-- Absolute square-root tail-work control for one nontrivial zero.  The bound
is uniform in the base cutoff and in every finite tail length. -/
def PairedEtaCompletedLeadingLogCutoffCenteredPartnerResidualCriticalTailWorkBound
    (rho : NontrivialZetaZero) : Prop :=
  ∃ C : ℝ, ∀ N L : ℕ,
    (((2 * N + 1 : ℕ) : ℝ) ^ (1 / 2 : ℝ)) *
        (∑ q ∈ Finset.range L,
          ‖pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidualFiniteWork
            rho (N + q)‖) ≤ C

/-- The absolute finite-work tail bound controls the actual residual at the
critical square-root scale. -/
theorem
    pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidual_criticalScale_eventuallyBounded_of_criticalTailWorkBound
    (rho : NontrivialZetaZero)
    (hwork :
      PairedEtaCompletedLeadingLogCutoffCenteredPartnerResidualCriticalTailWorkBound
        rho) :
    ∃ C : ℝ, ∀ᶠ N : ℕ in atTop,
      (((2 * N + 1 : ℕ) : ℝ) ^ (1 / 2 : ℝ)) *
          ‖pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidual rho N‖ ≤ C := by
  rcases hwork with ⟨C, hC⟩
  refine ⟨C, Eventually.of_forall fun N => ?_⟩
  have hsum :=
    tendsto_sum_range_pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidualFiniteWork
      rho N
  have hscaled := Filter.Tendsto.const_mul
    (((2 * N + 1 : ℕ) : ℝ) ^ (1 / 2 : ℝ)) hsum.norm
  apply le_of_tendsto' hscaled
  intro L
  calc
    (((2 * N + 1 : ℕ) : ℝ) ^ (1 / 2 : ℝ)) *
          ‖∑ q ∈ Finset.range L,
            pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidualFiniteWork
              rho (N + q)‖ ≤
        (((2 * N + 1 : ℕ) : ℝ) ^ (1 / 2 : ℝ)) *
          (∑ q ∈ Finset.range L,
            ‖pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidualFiniteWork
              rho (N + q)‖) :=
      mul_le_mul_of_nonneg_left
        (norm_sum_le (Finset.range L)
          (fun q =>
            pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidualFiniteWork
              rho (N + q)))
        (Real.rpow_nonneg (by positivity) _)
    _ ≤ C := hC N L

/-- The global absolute critical tail-work estimate. -/
def AllPairedEtaCompletedLeadingLogCutoffCenteredPartnerResidualCriticalTailWorkBound :
    Prop :=
  ∀ rho : NontrivialZetaZero,
    PairedEtaCompletedLeadingLogCutoffCenteredPartnerResidualCriticalTailWorkBound
      rho

/-- Global absolute tail-work control yields the RH-equivalent critical-scale
residual bound. -/
theorem
    all_pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidual_criticalScale_eventuallyBounded_of_all_criticalTailWorkBound
    (hwork :
      AllPairedEtaCompletedLeadingLogCutoffCenteredPartnerResidualCriticalTailWorkBound) :
    AllPairedEtaCompletedLeadingLogCutoffCenteredPartnerResidualCriticalScaleEventuallyBounded := by
  intro rho
  exact
    pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidual_criticalScale_eventuallyBounded_of_criticalTailWorkBound
      rho (hwork rho)

/-- The explicit global absolute finite-work tail estimate is sufficient for
Mathlib's Riemann hypothesis.  Proving this premise is the open arithmetic
problem. -/
theorem
    riemannHypothesis_of_all_pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidual_criticalTailWorkBound
    (hwork :
      AllPairedEtaCompletedLeadingLogCutoffCenteredPartnerResidualCriticalTailWorkBound) :
    RiemannHypothesis := by
  exact
    riemannHypothesis_of_all_pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidual_criticalScale_eventuallyBounded
      (all_pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidual_criticalScale_eventuallyBounded_of_all_criticalTailWorkBound
        hwork)

end

end RiemannGaussian
