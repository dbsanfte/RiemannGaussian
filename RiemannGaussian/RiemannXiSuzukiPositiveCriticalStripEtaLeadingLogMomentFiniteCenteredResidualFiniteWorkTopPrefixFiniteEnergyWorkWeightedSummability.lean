import RiemannGaussian.RiemannXiSuzukiPositiveCriticalStripEtaLeadingLogMomentFiniteCenteredResidualFiniteWorkTopPrefixFiniteEnergyWorkSummability

/-!
# Critical first moment of finite eta energy work

The preceding module proves that the signed finite energy work
`J_N = E_N - E_(N+1)` is absolutely summable at every nontrivial zero.  That
unweighted fact cannot detect RH.  This module identifies the first weight at
which the same literal arithmetic work does detect the critical line.

A general checked tail lemma shows that summability of
`(2N+1) * |J_N|`, together with the exact `HasSum` reconstruction of `E_N`,
forces `(2N+1) * |E_N| -> 0`.  On the other hand, the nonnegative amplitude
imbalance is pointwise at most `|E_N|`, and the existing sharp complementary
tail asymptotics make its endpoint scaling diverge at every off-critical zero.
This contradiction proves that the weighted work series is summable exactly
on the critical line.  Universal first-moment summability is therefore
equivalent to RH.

This is a reduction, not a proof of the arithmetic direction: no theorem here
asserts the critical first moment is universally finite.
-/

open Complex Filter MeasureTheory Metric Set Topology
open scoped Classical ComplexConjugate ENNReal Interval Topology

namespace RiemannGaussian

noncomputable section

/-- A summable positive-odd-endpoint first moment forces every reconstructed
series tail to be little-oh of the reciprocal endpoint. -/
theorem tendsto_oddEndpoint_mul_norm_of_hasSum_tails_of_summable_weighted_norm
    {f E : ℕ → ℝ}
    (htail : ∀ N : ℕ, HasSum (fun q : ℕ ↦ f (N + q)) (E N))
    (hweighted : Summable (fun N : ℕ ↦
      ((2 * N + 1 : ℕ) : ℝ) * ‖f N‖)) :
    Tendsto (fun N : ℕ ↦
      ((2 * N + 1 : ℕ) : ℝ) * ‖E N‖) atTop (nhds 0) := by
  let g : ℕ → ℝ := fun N ↦
    ((2 * N + 1 : ℕ) : ℝ) * ‖f N‖
  have hnorm : Summable (fun N : ℕ ↦ ‖f N‖) := by
    apply hweighted.of_nonneg_of_le
    · exact fun N ↦ norm_nonneg (f N)
    · intro N
      have hone : (1 : ℝ) ≤ ((2 * N + 1 : ℕ) : ℝ) := by
        exact_mod_cast (show 1 ≤ 2 * N + 1 by omega)
      nlinarith [norm_nonneg (f N)]
  have htailWeighted : Tendsto (fun N : ℕ ↦
      ∑' q : ℕ,
        ((2 * (N + q) + 1 : ℕ) : ℝ) * ‖f (N + q)‖)
      atTop (nhds 0) := by
    have h := tendsto_sum_nat_add g
    apply h.congr'
    filter_upwards with N
    apply tsum_congr
    intro q
    simp only [g]
    rw [Nat.add_comm q N]
  apply squeeze_zero'
  · exact Eventually.of_forall fun N ↦
      mul_nonneg (by positivity) (norm_nonneg (E N))
  · apply Eventually.of_forall
    intro N
    have hnormShift : Summable (fun q : ℕ ↦ ‖f (N + q)‖) := by
      have h := (summable_nat_add_iff N).2 hnorm
      exact h.congr fun q ↦ by rw [Nat.add_comm]
    have hweightedShift : Summable (fun q : ℕ ↦
        ((2 * (N + q) + 1 : ℕ) : ℝ) * ‖f (N + q)‖) := by
      have h := (summable_nat_add_iff N).2 hweighted
      exact h.congr fun q ↦ by
        rw [Nat.add_comm q N]
    have hnormTail : ‖E N‖ ≤ ∑' q : ℕ, ‖f (N + q)‖ :=
      (htail N).norm_le_of_bounded hnormShift.hasSum (fun _ ↦ le_rfl)
    calc
      ((2 * N + 1 : ℕ) : ℝ) * ‖E N‖ ≤
          ((2 * N + 1 : ℕ) : ℝ) *
            (∑' q : ℕ, ‖f (N + q)‖) :=
        mul_le_mul_of_nonneg_left hnormTail (by positivity)
      _ = ∑' q : ℕ,
          ((2 * N + 1 : ℕ) : ℝ) * ‖f (N + q)‖ := by
        rw [hnormShift.tsum_mul_left]
      _ ≤ ∑' q : ℕ,
          ((2 * (N + q) + 1 : ℕ) : ℝ) * ‖f (N + q)‖ := by
        apply Summable.tsum_le_tsum
        · intro q
          apply mul_le_mul_of_nonneg_right _ (norm_nonneg (f (N + q)))
          exact_mod_cast (show 2 * N + 1 ≤ 2 * (N + q) + 1 by omega)
        · exact hnormShift.mul_left (((2 * N + 1 : ℕ) : ℝ))
        · exact hweightedShift
  · exact htailWeighted

/-- The squared finite amplitude mismatch is pointwise bounded by the
absolute signed finite energy difference. -/
theorem topPrefixAmplitudeImbalance_le_abs_finiteEnergyDifference
    (rho : NontrivialZetaZero) (N : ℕ) :
    pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidualFiniteWorkTopPrefixAmplitudeImbalance
        rho N ≤
      |pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidualFiniteWorkTopPrefixFiniteEnergyDifference
        rho N| := by
  let a : ℝ :=
    pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidualFiniteWorkTopPrefixFinitePartnerAmplitude
      rho N
  let b : ℝ :=
    pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidualFiniteWorkTopPrefixFiniteConjugateAmplitude
      rho N
  have ha : 0 ≤ a := by
    simpa only [a] using topPrefixFinitePartnerAmplitude_nonneg rho N
  have hb : 0 ≤ b := by
    simpa only [b] using topPrefixFiniteConjugateAmplitude_nonneg rho N
  have habs : |a - b| ≤ a + b := by
    simpa only [abs_of_nonneg ha, abs_of_nonneg hb] using abs_sub a b
  rw [topPrefixAmplitudeImbalance_eq_sq_finiteAmplitudeDifference]
  unfold
    pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidualFiniteWorkTopPrefixFiniteAmplitudeDifference
    pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidualFiniteWorkTopPrefixFiniteEnergyDifference
  change (a - b) ^ 2 ≤ |a ^ 2 - b ^ 2|
  calc
    (a - b) ^ 2 = |a - b| ^ 2 := (sq_abs (a - b)).symm
    _ ≤ |a - b| * (a + b) := by
      rw [pow_two]
      exact mul_le_mul_of_nonneg_left habs (abs_nonneg (a - b))
    _ = |(a - b) * (a + b)| := by
      rw [abs_mul, abs_of_nonneg (add_nonneg ha hb)]
    _ = |a ^ 2 - b ^ 2| := by
      congr 1
      ring

/-- The exact endpoint-scaled amplitude imbalance diverges at every
off-critical zero, in either half of the critical strip. -/
theorem
    tendsto_oddEndpoint_mul_topPrefixAmplitudeImbalance_atTop_of_re_ne_half
    (rho : NontrivialZetaZero) (hrho : rho.1.re ≠ 1 / 2) :
    Tendsto (fun N : ℕ ↦
      ((2 * N + 1 : ℕ) : ℝ) *
        pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidualFiniteWorkTopPrefixAmplitudeImbalance
          rho N)
      atTop atTop := by
  rcases lt_or_gt_of_ne hrho with hleft | hright
  · let partner := NontrivialZetaZero.conjugatePartner rho
    have hpartner : 1 / 2 < partner.1.re := by
      have hpartnerRe : partner.1.re = 1 - rho.1.re := by
        simp [partner, NontrivialZetaZero.conjugatePartner_coe]
      rw [hpartnerRe]
      linarith
    have h :=
      tendsto_oddEndpoint_mul_topPrefixAmplitudeImbalance_atTop_of_half_lt_re
        partner hpartner
    apply h.congr'
    filter_upwards with N
    rw [topPrefixAmplitudeImbalance_conjugatePartner rho N]
  · exact
      tendsto_oddEndpoint_mul_topPrefixAmplitudeImbalance_atTop_of_half_lt_re
        rho hright

/-- At every off-critical zero, the endpoint-scaled absolute signed finite
energy difference diverges. -/
theorem tendsto_oddEndpoint_mul_abs_topPrefixFiniteEnergyDifference_atTop_of_re_ne_half
    (rho : NontrivialZetaZero) (hrho : rho.1.re ≠ 1 / 2) :
    Tendsto (fun N : ℕ ↦
      ((2 * N + 1 : ℕ) : ℝ) *
        |pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidualFiniteWorkTopPrefixFiniteEnergyDifference
          rho N|)
      atTop atTop := by
  have hdiv :=
    tendsto_oddEndpoint_mul_topPrefixAmplitudeImbalance_atTop_of_re_ne_half
      rho hrho
  rw [Filter.tendsto_atTop] at hdiv ⊢
  intro b
  filter_upwards [hdiv b] with N hN
  exact hN.trans (mul_le_mul_of_nonneg_left
    (topPrefixAmplitudeImbalance_le_abs_finiteEnergyDifference rho N)
    (by positivity))

/-- On the critical line the signed finite energy difference vanishes at
every cutoff. -/
theorem topPrefixFiniteEnergyDifference_eq_zero_of_re_eq_half
    (rho : NontrivialZetaZero) (hrho : rho.1.re = 1 / 2) (N : ℕ) :
    pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidualFiniteWorkTopPrefixFiniteEnergyDifference
        rho N = 0 := by
  have himbalance :=
    topPrefixAmplitudeImbalance_eq_zero_of_re_eq_half rho hrho N
  rw [topPrefixAmplitudeImbalance_eq_sq_finiteAmplitudeDifference] at himbalance
  have hdifference :
      pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidualFiniteWorkTopPrefixFiniteAmplitudeDifference
          rho N = 0 := by
    nlinarith [sq_nonneg
      (pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidualFiniteWorkTopPrefixFiniteAmplitudeDifference
        rho N)]
  rw [topPrefixFiniteEnergyDifference_eq_amplitudeDifference_mul_total,
    hdifference, zero_mul]

/-- The positive-odd-endpoint first moment of the absolute finite energy work
is summable exactly on the critical line. -/
theorem summable_oddEndpoint_mul_abs_topPrefixFiniteEnergyWork_iff_re_eq_half
    (rho : NontrivialZetaZero) :
    Summable (fun N : ℕ ↦
      ((2 * N + 1 : ℕ) : ℝ) *
        |pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidualFiniteWorkTopPrefixFiniteEnergyWork
          rho N|) ↔
      rho.1.re = 1 / 2 := by
  constructor
  · intro hweighted
    have hweightedNorm : Summable (fun N : ℕ ↦
        ((2 * N + 1 : ℕ) : ℝ) *
          ‖pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidualFiniteWorkTopPrefixFiniteEnergyWork
            rho N‖) := by
      simpa only [Real.norm_eq_abs] using hweighted
    have hdecay :=
      tendsto_oddEndpoint_mul_norm_of_hasSum_tails_of_summable_weighted_norm
        (f := fun N : ℕ ↦
          pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidualFiniteWorkTopPrefixFiniteEnergyWork
            rho N)
        (E := fun N : ℕ ↦
          pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidualFiniteWorkTopPrefixFiniteEnergyDifference
            rho N)
        (hasSum_topPrefixFiniteEnergyWork rho) hweightedNorm
    by_contra hne
    have hdiv :=
      tendsto_oddEndpoint_mul_abs_topPrefixFiniteEnergyDifference_atTop_of_re_ne_half
        rho hne
    have hsmall : ∀ᶠ N : ℕ in atTop,
        ((2 * N + 1 : ℕ) : ℝ) *
          |pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidualFiniteWorkTopPrefixFiniteEnergyDifference
            rho N| < 1 := by
      simpa only [Real.norm_eq_abs] using
        hdecay.eventually_lt_const zero_lt_one
    have hlarge : ∀ᶠ N : ℕ in atTop,
        1 ≤ ((2 * N + 1 : ℕ) : ℝ) *
          |pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidualFiniteWorkTopPrefixFiniteEnergyDifference
            rho N| :=
      Filter.tendsto_atTop.1 hdiv 1
    rcases (hsmall.and hlarge).exists with ⟨N, hs, hl⟩
    exact (not_lt_of_ge hl) hs
  · intro hrho
    have hzero : (fun N : ℕ ↦
        ((2 * N + 1 : ℕ) : ℝ) *
          |pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidualFiniteWorkTopPrefixFiniteEnergyWork
            rho N|) = fun _ ↦ 0 := by
      funext N
      unfold
        pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidualFiniteWorkTopPrefixFiniteEnergyWork
      rw [topPrefixFiniteEnergyDifference_eq_zero_of_re_eq_half rho hrho N,
        topPrefixFiniteEnergyDifference_eq_zero_of_re_eq_half rho hrho (N + 1)]
      norm_num
    rw [hzero]
    exact summable_zero

/-- The critical first-moment work criterion is exactly the existing
normalized-energy square-summability criterion at each zero. -/
theorem
    summable_oddEndpoint_mul_abs_topPrefixFiniteEnergyWork_iff_summable_sq_normalizedFiniteEnergyDefect
    (rho : NontrivialZetaZero) :
    Summable (fun N : ℕ ↦
      ((2 * N + 1 : ℕ) : ℝ) *
        |pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidualFiniteWorkTopPrefixFiniteEnergyWork
          rho N|) ↔
      Summable (fun N : ℕ ↦
        pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidualFiniteWorkTopPrefixNormalizedFiniteEnergyDefect
          rho N ^ 2) := by
  rw [summable_oddEndpoint_mul_abs_topPrefixFiniteEnergyWork_iff_re_eq_half,
    summable_sq_topPrefixNormalizedFiniteEnergyDefect_iff_re_eq_half]

/-- Universal critical first-moment summability for the literal finite eta
energy work. -/
def AllPairedEtaCompletedLeadingLogCutoffCenteredPartnerResidualFiniteWorkTopPrefixFiniteEnergyWorkFirstMomentSummable :
    Prop :=
  ∀ rho : NontrivialZetaZero,
    Summable (fun N : ℕ ↦
      ((2 * N + 1 : ℕ) : ℝ) *
        |pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidualFiniteWorkTopPrefixFiniteEnergyWork
          rho N|)

/-- Universal first-moment summability of the explicit finite eta energy work
is equivalent to the Riemann hypothesis.  The arithmetic direction remains
open. -/
theorem
    riemannHypothesis_iff_all_topPrefixFiniteEnergyWork_firstMoment_summable :
    RiemannHypothesis ↔
      AllPairedEtaCompletedLeadingLogCutoffCenteredPartnerResidualFiniteWorkTopPrefixFiniteEnergyWorkFirstMomentSummable := by
  constructor
  · intro hRH rho
    apply
      (summable_oddEndpoint_mul_abs_topPrefixFiniteEnergyWork_iff_re_eq_half rho).2
    have him : (zetaSpectralCoordinate rho.1).im = 0 :=
      (riemannHypothesis_iff_spectralCoordinate_real.mp hRH)
        rho.1 rho.2.1 rho.2.2.1 rho.2.2.2
    exact (zetaSpectralCoordinate_im_eq_zero_iff rho.1).1 him
  · intro hsummable
    rw [riemannHypothesis_iff_spectralCoordinate_real]
    intro s hs hnontrivial hone
    let rho : NontrivialZetaZero := ⟨s, hs, hnontrivial, hone⟩
    apply (zetaSpectralCoordinate_im_eq_zero_iff s).2
    exact
      (summable_oddEndpoint_mul_abs_topPrefixFiniteEnergyWork_iff_re_eq_half
        rho).1 (hsummable rho)

end

end RiemannGaussian
