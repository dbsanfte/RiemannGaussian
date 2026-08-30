import RiemannGaussian.RiemannXiSuzukiPositiveCriticalStripEtaLeadingLogMomentFiniteCenteredResidualFiniteWorkSharpAsymptotic

/-!
# Critical-scale rigidity of the exact finite residual work

The sharp signed finite-work asymptotic identifies the correct critical work
scale.  At a hypothetical zero `rho` with `Re rho > 1 / 2`, the reflected
partner exponent is strictly below `1 / 2`, so the norm of the exact finite
work decays like

`(2N+1)^(-(Re rho# + 1))`.

Multiplication by the critical exponent `3 / 2` therefore makes the scaled
work norm diverge to positive infinity.  This module packages the resulting
finite-arithmetic target: eventual boundedness of the explicit one-step work
at scale `(2N+1)^(3/2)` for every nontrivial zero.  Lean proves that this
estimate implies RH.  The estimate itself remains open; this reduction is not
a proof of RH.
-/

open Complex Filter MeasureTheory Metric Set Topology
open scoped Classical ComplexConjugate ENNReal Interval Topology

namespace RiemannGaussian

noncomputable section

/-- At a hypothetical right-half zero, the exact finite work is too large for
the critical `3 / 2` normalization: its normalized norm tends to positive
infinity. -/
theorem
    tendsto_oddEndpoint_threeHalves_rpow_mul_norm_pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidualFiniteWork_atTop_of_half_lt_re
    (rho : NontrivialZetaZero) (hrho : 1 / 2 < rho.1.re) :
    Tendsto (fun N : ℕ =>
      (((2 * N + 1 : ℕ) : ℝ) ^ (3 / 2 : ℝ)) *
        ‖pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidualFiniteWork
          rho N‖)
      atTop atTop := by
  let partner : NontrivialZetaZero :=
    NontrivialZetaZero.conjugatePartner rho
  have hpartnerRate :=
    tendsto_oddEndpoint_partner_add_one_rpow_mul_norm_pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidualFiniteWork
      rho hrho
  have hgap : 0 < (3 / 2 : ℝ) - (partner.1.re + 1) := by
    have hpartnerRe : partner.1.re = 1 - rho.1.re := by
      simp [partner, NontrivialZetaZero.conjugatePartner_coe]
    rw [hpartnerRe]
    linarith
  have hbase : Tendsto (fun N : ℕ => (2 : ℝ) * N + 1)
      atTop atTop :=
    tendsto_atTop_add_const_right atTop 1
      ((tendsto_natCast_atTop_atTop (R := ℝ)).const_mul_atTop (by norm_num))
  have hfactor : Tendsto (fun N : ℕ =>
      ((2 * N + 1 : ℕ) : ℝ) ^
        ((3 / 2 : ℝ) - (partner.1.re + 1)))
      atTop atTop := by
    convert (tendsto_rpow_atTop hgap).comp hbase using 1
    funext N
    norm_num
  have hlimitPos :
      0 <
        ‖pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidualFiniteWorkComplexSharpLimit
          rho‖ :=
    norm_pos_iff.mpr
      (pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidualFiniteWorkComplexSharpLimit_ne_zero
        rho)
  have hproduct := hfactor.atTop_mul_pos hlimitPos hpartnerRate
  convert hproduct using 1
  funext N
  let x : ℝ := ((2 * N + 1 : ℕ) : ℝ)
  have hx : 0 < x := by dsimp [x]; positivity
  symm
  change x ^ ((3 / 2 : ℝ) - (partner.1.re + 1)) *
      (x ^ (partner.1.re + 1) *
        ‖pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidualFiniteWork
          rho N‖) =
    x ^ (3 / 2 : ℝ) *
      ‖pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidualFiniteWork
        rho N‖
  rw [← mul_assoc, ← Real.rpow_add hx]
  congr 2
  ring

/-- Consequently no eventual finite upper bound can hold at the critical
work scale for a right-half off-line zero. -/
theorem
    not_exists_eventually_oddEndpoint_threeHalves_rpow_mul_norm_pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidualFiniteWork_le_of_half_lt_re
    (rho : NontrivialZetaZero) (hrho : 1 / 2 < rho.1.re) :
    ¬ ∃ C : ℝ, ∀ᶠ N : ℕ in atTop,
      (((2 * N + 1 : ℕ) : ℝ) ^ (3 / 2 : ℝ)) *
          ‖pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidualFiniteWork
            rho N‖ ≤ C := by
  rintro ⟨C, hupper⟩
  have hlower :=
    (tendsto_oddEndpoint_threeHalves_rpow_mul_norm_pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidualFiniteWork_atTop_of_half_lt_re
      rho hrho).eventually_gt_atTop C
  obtain ⟨N, hle, hlt⟩ := (hupper.and hlower).exists
  exact (not_lt_of_ge hle hlt)

/-- The global finite-arithmetic work estimate exposed by the sharp
asymptotic: at every nontrivial zero, the exact one-step work is eventually
bounded after the universal critical normalization `(2N+1)^(3/2)`. -/
def AllPairedEtaCompletedLeadingLogCutoffCenteredPartnerResidualFiniteWorkCriticalScaleEventuallyBounded :
    Prop :=
  ∀ rho : NontrivialZetaZero, ∃ C : ℝ, ∀ᶠ N : ℕ in atTop,
    (((2 * N + 1 : ℕ) : ℝ) ^ (3 / 2 : ℝ)) *
        ‖pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidualFiniteWork
          rho N‖ ≤ C

/-- Global critical-scale boundedness of the exact finite work forces every
nontrivial zero onto the critical line. -/
theorem
    nontrivialZetaZero_re_eq_half_of_all_pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidualFiniteWork_criticalScale_eventuallyBounded
    (hbounded :
      AllPairedEtaCompletedLeadingLogCutoffCenteredPartnerResidualFiniteWorkCriticalScaleEventuallyBounded)
    (rho : NontrivialZetaZero) :
    rho.1.re = 1 / 2 := by
  by_contra hne
  rcases lt_or_gt_of_ne hne with hleft | hright
  · have hpartnerRight :
        1 / 2 < (NontrivialZetaZero.conjugatePartner rho).1.re := by
      have h : 1 / 2 < 1 - rho.1.re := by linarith
      simpa [NontrivialZetaZero.conjugatePartner_coe] using h
    exact
      (not_exists_eventually_oddEndpoint_threeHalves_rpow_mul_norm_pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidualFiniteWork_le_of_half_lt_re
        (NontrivialZetaZero.conjugatePartner rho) hpartnerRight)
        (hbounded (NontrivialZetaZero.conjugatePartner rho))
  · exact
      (not_exists_eventually_oddEndpoint_threeHalves_rpow_mul_norm_pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidualFiniteWork_le_of_half_lt_re
        rho hright) (hbounded rho)

/-- The explicit global critical-scale finite-work estimate implies Mathlib's
Riemann hypothesis.  Proving this estimate from the finite head-plus-prefix
formula is the open arithmetic problem. -/
theorem
    riemannHypothesis_of_all_pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidualFiniteWork_criticalScale_eventuallyBounded
    (hbounded :
      AllPairedEtaCompletedLeadingLogCutoffCenteredPartnerResidualFiniteWorkCriticalScaleEventuallyBounded) :
    RiemannHypothesis := by
  rw [riemannHypothesis_iff_spectralCoordinate_real]
  intro s hs hnontrivial hone
  let rho : NontrivialZetaZero := ⟨s, hs, hnontrivial, hone⟩
  exact (zetaSpectralCoordinate_im_eq_zero_iff s).2
    (nontrivialZetaZero_re_eq_half_of_all_pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidualFiniteWork_criticalScale_eventuallyBounded
      hbounded rho)

end

end RiemannGaussian
