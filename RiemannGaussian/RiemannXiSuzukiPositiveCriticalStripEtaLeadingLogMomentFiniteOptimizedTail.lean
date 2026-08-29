import RiemannGaussian.RiemannXiSuzukiPositiveCriticalStripEtaLeadingLogMomentFiniteCompletedResidual

/-!
# Cutoff-optimized bounds for finite eta moment tails

The fixed-`theta` support-tail bound decays like
`(2N+1)^(-(1-theta)*sigma)`.  A fixed split deliberately sacrifices part of
the true horizontal exponent.  This module chooses the split at each cutoff:

`theta = (k+1) / (sigma * log (2N+1))`.

Once `k+1 < sigma * log (2N+1)`, this lies strictly between zero and one.
Substitution into the checked general bound gives the substantially sharper
envelope

`exp (-sigma*log(2N+1) + (k+1)) * k! *
  (log(2N+1)/(k+1))^(k+1)`.

Thus the full exponent `sigma` is recovered, at the cost of only a fixed
logarithmic power.  The result is propagated to the finite phase-sensitive
lower certificate and to the completed complex partner residual.
-/

open Complex Filter MeasureTheory Metric Set Topology
open scoped Classical ComplexConjugate ENNReal Interval Topology

namespace RiemannGaussian

noncomputable section

/-- The cutoff-dependent exponential split recovering the full horizontal
tail exponent. -/
def pairedEtaLogLaplaceMomentBalancedTheta
    (k : ℕ) (sigma : ℝ) (N : ℕ) : ℝ :=
  ((k + 1 : ℕ) : ℝ) /
    (sigma * Real.log (((2 * N + 1 : ℕ) : ℝ)))

/-- The near-sharp elementary tail envelope obtained from the balanced
cutoff-dependent split. -/
def pairedEtaLogLaplaceMomentNearSharpTailUpper
    (k : ℕ) (sigma : ℝ) (N : ℕ) : ℝ :=
  Real.exp
      (-sigma * Real.log (((2 * N + 1 : ℕ) : ℝ)) +
        ((k + 1 : ℕ) : ℝ)) *
    ((k.factorial : ℝ) *
      (Real.log (((2 * N + 1 : ℕ) : ℝ)) /
        ((k + 1 : ℕ) : ℝ)) ^ (k + 1))

/-- Past the explicit cutoff threshold, the balanced split is positive. -/
theorem pairedEtaLogLaplaceMomentBalancedTheta_pos
    (k N : ℕ) {sigma : ℝ}
    (hcutoff : ((k + 1 : ℕ) : ℝ) <
      sigma * Real.log (((2 * N + 1 : ℕ) : ℝ))) :
    0 < pairedEtaLogLaplaceMomentBalancedTheta k sigma N := by
  unfold pairedEtaLogLaplaceMomentBalancedTheta
  exact div_pos (by positivity) (lt_trans (by positivity) hcutoff)

/-- Past the explicit cutoff threshold, the balanced split is strictly less
than one. -/
theorem pairedEtaLogLaplaceMomentBalancedTheta_lt_one
    (k N : ℕ) {sigma : ℝ}
    (hcutoff : ((k + 1 : ℕ) : ℝ) <
      sigma * Real.log (((2 * N + 1 : ℕ) : ℝ))) :
    pairedEtaLogLaplaceMomentBalancedTheta k sigma N < 1 := by
  unfold pairedEtaLogLaplaceMomentBalancedTheta
  exact (div_lt_one (lt_trans (by positivity) hcutoff)).2 hcutoff

/-- Substituting the balanced split into the general tail envelope gives the
near-sharp closed form with full exponent `sigma`. -/
theorem pairedEtaLogLaplaceMomentTailUpper_balancedTheta_eq_nearSharp
    (k N : ℕ) {sigma : ℝ}
    (hsigma : 0 < sigma)
    (hcutoff : ((k + 1 : ℕ) : ℝ) <
      sigma * Real.log (((2 * N + 1 : ℕ) : ℝ))) :
    pairedEtaLogLaplaceMomentTailUpper k sigma
        (pairedEtaLogLaplaceMomentBalancedTheta k sigma N) N =
      pairedEtaLogLaplaceMomentNearSharpTailUpper k sigma N := by
  let a : ℝ := Real.log (2 * (N : ℝ) + 1)
  let d : ℝ := (k : ℝ) + 1
  have hd : 0 < d := by positivity
  have hcutoff' : d < sigma * a := by
    simpa [a, d, Nat.cast_add, Nat.cast_mul] using hcutoff
  have hsigmaA : 0 < sigma * a := lt_trans hd hcutoff'
  have ha : 0 < a := by
    rcases (mul_pos_iff.mp hsigmaA) with h | h
    · exact h.2
    · exact (not_lt_of_ge hsigma.le h.1).elim
  have hbase : d / (sigma * a) * sigma = d / a := by
    field_simp [hsigma.ne', ha.ne']
  unfold pairedEtaLogLaplaceMomentTailUpper
    pairedEtaLogLaplaceMomentBalancedTheta
    pairedEtaLogLaplaceMomentNearSharpTailUpper
  simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one]
  change Real.exp (-(1 - d / (sigma * a)) * sigma * a) *
      ((k.factorial : ℝ) / (d / (sigma * a) * sigma) ^ (k + 1)) =
    Real.exp (-sigma * a + d) *
      ((k.factorial : ℝ) * (a / d) ^ (k + 1))
  rw [hbase]
  congr 1
  · congr 1
    field_simp [hsigma.ne', ha.ne']
    ring
  · rw [div_eq_mul_inv, ← inv_pow]
    congr 1
    field_simp [ha.ne', hd.ne']

/-- Past the explicit cutoff threshold, the literal complex support tail has
the near-sharp full-exponent bound. -/
theorem norm_integral_pairedEtaLogLaplaceMoment_tail_le_nearSharp
    (k : ℕ) {s : ℂ} (hs : 0 < s.re) (N : ℕ)
    (hcutoff : ((k + 1 : ℕ) : ℝ) <
      s.re * Real.log (((2 * N + 1 : ℕ) : ℝ))) :
    ‖∫ t : ℝ, (t : ℂ) ^ k * Complex.exp (-s * t)
        ∂pairedEtaLogTailMeasure N‖ ≤
      pairedEtaLogLaplaceMomentNearSharpTailUpper k s.re N := by
  let theta := pairedEtaLogLaplaceMomentBalancedTheta k s.re N
  have htheta : 0 < theta :=
    pairedEtaLogLaplaceMomentBalancedTheta_pos k N hcutoff
  have hthetaOne : theta < 1 :=
    pairedEtaLogLaplaceMomentBalancedTheta_lt_one k N hcutoff
  calc
    ‖∫ t : ℝ, (t : ℂ) ^ k * Complex.exp (-s * t)
          ∂pairedEtaLogTailMeasure N‖ ≤
        pairedEtaLogLaplaceMomentTailUpper k s.re theta N :=
      norm_integral_pairedEtaLogLaplaceMoment_tail_le
        k hs htheta hthetaOne N
    _ = pairedEtaLogLaplaceMomentNearSharpTailUpper k s.re N :=
      pairedEtaLogLaplaceMomentTailUpper_balancedTheta_eq_nearSharp
        k N hs hcutoff

/-- The finite complex prefix approximates the full support moment at the
near-sharp full horizontal exponent. -/
theorem norm_pairedEtaLogLaplaceMomentPartialSum_sub_le_nearSharp
    (k : ℕ) {s : ℂ} (hs : 0 < s.re) (N : ℕ)
    (hcutoff : ((k + 1 : ℕ) : ℝ) <
      s.re * Real.log (((2 * N + 1 : ℕ) : ℝ))) :
    ‖pairedEtaLogLaplaceMomentPartialSum k s N -
        pairedEtaLogLaplaceMoment k s‖ ≤
      pairedEtaLogLaplaceMomentNearSharpTailUpper k s.re N := by
  let theta := pairedEtaLogLaplaceMomentBalancedTheta k s.re N
  have htheta : 0 < theta :=
    pairedEtaLogLaplaceMomentBalancedTheta_pos k N hcutoff
  have hthetaOne : theta < 1 :=
    pairedEtaLogLaplaceMomentBalancedTheta_lt_one k N hcutoff
  calc
    ‖pairedEtaLogLaplaceMomentPartialSum k s N -
          pairedEtaLogLaplaceMoment k s‖ ≤
        pairedEtaLogLaplaceMomentTailUpper k s.re theta N :=
      norm_pairedEtaLogLaplaceMomentPartialSum_sub_le_tailUpper
        k hs htheta hthetaOne N
    _ = pairedEtaLogLaplaceMomentNearSharpTailUpper k s.re N :=
      pairedEtaLogLaplaceMomentTailUpper_balancedTheta_eq_nearSharp
        k N hs hcutoff

/-- The phase-sensitive finite lower certificate using the near-sharp tail
envelope. -/
def pairedEtaLogLaplaceMomentNearSharpFiniteLower
    (k : ℕ) (s : ℂ) (N : ℕ) : ℝ :=
  max 0 (‖pairedEtaLogLaplaceMomentPartialSum k s N‖ -
    pairedEtaLogLaplaceMomentNearSharpTailUpper k s.re N)

/-- Past the explicit cutoff threshold, the near-sharp finite certificate is
a valid lower bound for the complete moment norm. -/
theorem pairedEtaLogLaplaceMomentNearSharpFiniteLower_le_norm
    (k : ℕ) {s : ℂ} (hs : 0 < s.re) (N : ℕ)
    (hcutoff : ((k + 1 : ℕ) : ℝ) <
      s.re * Real.log (((2 * N + 1 : ℕ) : ℝ))) :
    pairedEtaLogLaplaceMomentNearSharpFiniteLower k s N ≤
      ‖pairedEtaLogLaplaceMoment k s‖ := by
  unfold pairedEtaLogLaplaceMomentNearSharpFiniteLower
  apply max_le
  · exact norm_nonneg _
  · have hreverse := norm_sub_norm_le
      (pairedEtaLogLaplaceMomentPartialSum k s N)
      (pairedEtaLogLaplaceMoment k s)
    have htail :=
      norm_pairedEtaLogLaplaceMomentPartialSum_sub_le_nearSharp
        k hs N hcutoff
    linarith

/-- At a nontrivial zero, the near-sharp finite certificate bounds the exact
leading gap-moment defect from below. -/
theorem pairedEtaLeadingLogGapMomentNearSharpFiniteLower_le_norm_defect
    (rho : NontrivialZetaZero) (N : ℕ)
    (hcutoff :
      (((analyticZetaZeroMultiplicity rho + 1 : ℕ) : ℝ)) <
        rho.1.re * Real.log (((2 * N + 1 : ℕ) : ℝ))) :
    pairedEtaLogLaplaceMomentNearSharpFiniteLower
        (analyticZetaZeroMultiplicity rho) rho.1 N ≤
      ‖pairedEtaLeadingLogGapMomentDefect rho‖ := by
  rw [pairedEtaLeadingLogGapMomentDefect_eq_logLaplaceMoment]
  exact pairedEtaLogLaplaceMomentNearSharpFiniteLower_le_norm
    (analyticZetaZeroMultiplicity rho)
    (NontrivialZetaZero.zero_lt_re rho) N hcutoff

/-- A generic completion-weighted residual estimate from any two bounds on
the complementary finite-prefix errors. -/
theorem norm_pairedEtaCompletedLeadingLogFinitePartnerResidual_le_of_errors
    (rho : NontrivialZetaZero) (N : ℕ) {partnerUpper rhoUpper : ℝ}
    (hpartner :
      ‖pairedEtaLogLaplaceMomentPartialSum
          (analyticZetaZeroMultiplicity rho)
          (NontrivialZetaZero.conjugatePartner rho).1 N -
        pairedEtaLogLaplaceMoment
          (analyticZetaZeroMultiplicity rho)
          (NontrivialZetaZero.conjugatePartner rho).1‖ ≤ partnerUpper)
    (hrho :
      ‖pairedEtaLogLaplaceMomentPartialSum
          (analyticZetaZeroMultiplicity rho) rho.1 N -
        pairedEtaLogLaplaceMoment
          (analyticZetaZeroMultiplicity rho) rho.1‖ ≤ rhoUpper) :
    ‖pairedEtaCompletedLeadingLogFinitePartnerResidual rho N‖ ≤
      pairedEtaCompletionSpectralWeight
          (NontrivialZetaZero.conjugatePartner rho) * partnerUpper +
        pairedEtaCompletionSpectralWeight rho * rhoUpper := by
  rw [pairedEtaCompletedLeadingLogFinitePartnerResidual_eq_errors]
  calc
    ‖pairedEtaXiCompletionFactor
            (NontrivialZetaZero.conjugatePartner rho).1 *
            (NontrivialZetaZero.conjugatePartner rho).1 *
            (pairedEtaLogLaplaceMomentPartialSum
                (analyticZetaZeroMultiplicity rho)
                (NontrivialZetaZero.conjugatePartner rho).1 N -
              pairedEtaLogLaplaceMoment
                (analyticZetaZeroMultiplicity rho)
                (NontrivialZetaZero.conjugatePartner rho).1) -
          (-1 : ℂ) ^ (analyticZetaZeroMultiplicity rho) *
            starRingEnd ℂ
              (pairedEtaXiCompletionFactor rho.1 * rho.1 *
                (pairedEtaLogLaplaceMomentPartialSum
                    (analyticZetaZeroMultiplicity rho) rho.1 N -
                  pairedEtaLogLaplaceMoment
                    (analyticZetaZeroMultiplicity rho) rho.1))‖ ≤
        ‖pairedEtaXiCompletionFactor
            (NontrivialZetaZero.conjugatePartner rho).1 *
            (NontrivialZetaZero.conjugatePartner rho).1 *
            (pairedEtaLogLaplaceMomentPartialSum
                (analyticZetaZeroMultiplicity rho)
                (NontrivialZetaZero.conjugatePartner rho).1 N -
              pairedEtaLogLaplaceMoment
                (analyticZetaZeroMultiplicity rho)
                (NontrivialZetaZero.conjugatePartner rho).1)‖ +
          ‖(-1 : ℂ) ^ (analyticZetaZeroMultiplicity rho) *
            starRingEnd ℂ
              (pairedEtaXiCompletionFactor rho.1 * rho.1 *
                (pairedEtaLogLaplaceMomentPartialSum
                    (analyticZetaZeroMultiplicity rho) rho.1 N -
                  pairedEtaLogLaplaceMoment
                    (analyticZetaZeroMultiplicity rho) rho.1))‖ :=
      norm_sub_le _ _
    _ = pairedEtaCompletionSpectralWeight
            (NontrivialZetaZero.conjugatePartner rho) *
          ‖pairedEtaLogLaplaceMomentPartialSum
              (analyticZetaZeroMultiplicity rho)
              (NontrivialZetaZero.conjugatePartner rho).1 N -
            pairedEtaLogLaplaceMoment
              (analyticZetaZeroMultiplicity rho)
              (NontrivialZetaZero.conjugatePartner rho).1‖ +
        pairedEtaCompletionSpectralWeight rho *
          ‖pairedEtaLogLaplaceMomentPartialSum
              (analyticZetaZeroMultiplicity rho) rho.1 N -
            pairedEtaLogLaplaceMoment
              (analyticZetaZeroMultiplicity rho) rho.1‖ := by
      simp only [pairedEtaCompletionSpectralWeight, norm_mul, norm_pow,
        norm_neg, norm_one, one_pow, one_mul, norm_conj]
    _ ≤ pairedEtaCompletionSpectralWeight
            (NontrivialZetaZero.conjugatePartner rho) * partnerUpper +
        pairedEtaCompletionSpectralWeight rho * rhoUpper := by
      exact add_le_add
        (mul_le_mul_of_nonneg_left hpartner
          (pairedEtaCompletionSpectralWeight_pos
            (NontrivialZetaZero.conjugatePartner rho)).le)
        (mul_le_mul_of_nonneg_left hrho
          (pairedEtaCompletionSpectralWeight_pos rho).le)

/-- The completion-weighted sum of the two near-sharp complementary tail
envelopes. -/
def pairedEtaCompletedLeadingLogFinitePartnerResidualNearSharpUpper
    (rho : NontrivialZetaZero) (N : ℕ) : ℝ :=
  pairedEtaCompletionSpectralWeight
      (NontrivialZetaZero.conjugatePartner rho) *
      pairedEtaLogLaplaceMomentNearSharpTailUpper
        (analyticZetaZeroMultiplicity rho)
        (NontrivialZetaZero.conjugatePartner rho).1.re N +
    pairedEtaCompletionSpectralWeight rho *
      pairedEtaLogLaplaceMomentNearSharpTailUpper
        (analyticZetaZeroMultiplicity rho) rho.1.re N

/-- Once both explicit cutoff thresholds hold, the complex completed partner
residual obeys the near-sharp full-exponent two-tail bound. -/
theorem norm_pairedEtaCompletedLeadingLogFinitePartnerResidual_le_nearSharp
    (rho : NontrivialZetaZero) (N : ℕ)
    (hpartnerCutoff :
      (((analyticZetaZeroMultiplicity rho + 1 : ℕ) : ℝ)) <
        (NontrivialZetaZero.conjugatePartner rho).1.re *
          Real.log (((2 * N + 1 : ℕ) : ℝ)))
    (hrhoCutoff :
      (((analyticZetaZeroMultiplicity rho + 1 : ℕ) : ℝ)) <
        rho.1.re * Real.log (((2 * N + 1 : ℕ) : ℝ))) :
    ‖pairedEtaCompletedLeadingLogFinitePartnerResidual rho N‖ ≤
      pairedEtaCompletedLeadingLogFinitePartnerResidualNearSharpUpper
        rho N := by
  unfold pairedEtaCompletedLeadingLogFinitePartnerResidualNearSharpUpper
  exact norm_pairedEtaCompletedLeadingLogFinitePartnerResidual_le_of_errors
    rho N
    (norm_pairedEtaLogLaplaceMomentPartialSum_sub_le_nearSharp
      (analyticZetaZeroMultiplicity rho)
      (NontrivialZetaZero.zero_lt_re
        (NontrivialZetaZero.conjugatePartner rho)) N hpartnerCutoff)
    (norm_pairedEtaLogLaplaceMomentPartialSum_sub_le_nearSharp
      (analyticZetaZeroMultiplicity rho)
      (NontrivialZetaZero.zero_lt_re rho) N hrhoCutoff)

/-- For every positive horizontal parameter, the balanced-split cutoff
threshold holds at all sufficiently large arithmetic truncations. -/
theorem eventually_pairedEtaLogLaplaceMoment_nearSharp_cutoff
    (k : ℕ) {sigma : ℝ} (hsigma : 0 < sigma) :
    ∀ᶠ N : ℕ in atTop,
      ((k + 1 : ℕ) : ℝ) <
        sigma * Real.log (((2 * N + 1 : ℕ) : ℝ)) := by
  have hbase : Tendsto (fun N : ℕ ↦ ((2 * N + 1 : ℕ) : ℝ))
      atTop atTop := by
    convert tendsto_atTop_add_const_right atTop 1
      ((tendsto_natCast_atTop_atTop (R := ℝ)).const_mul_atTop
        (by norm_num : (0 : ℝ) < 2)) using 1
    funext N
    norm_num
  have hscaled : Tendsto (fun N : ℕ ↦
      sigma * Real.log (((2 * N + 1 : ℕ) : ℝ))) atTop atTop :=
    (Real.tendsto_log_atTop.comp hbase).const_mul_atTop' hsigma
  exact hscaled.eventually_gt_atTop (((k + 1 : ℕ) : ℝ))

/-- The cutoff-optimized envelope tends to zero.  It keeps the full
horizontal exponent `sigma`; the remaining fixed logarithmic power is
absorbed by exponential decay. -/
theorem tendsto_pairedEtaLogLaplaceMomentNearSharpTailUpper_zero
    (k : ℕ) {sigma : ℝ} (hsigma : 0 < sigma) :
    Tendsto (fun N : ℕ ↦
      pairedEtaLogLaplaceMomentNearSharpTailUpper k sigma N)
      atTop (nhds 0) := by
  let d : ℝ := ((k + 1 : ℕ) : ℝ)
  have hd : d ≠ 0 := by
    dsimp [d]
    positivity
  have hbase : Tendsto (fun N : ℕ ↦ ((2 * N + 1 : ℕ) : ℝ))
      atTop atTop := by
    convert tendsto_atTop_add_const_right atTop 1
      ((tendsto_natCast_atTop_atTop (R := ℝ)).const_mul_atTop
        (by norm_num : (0 : ℝ) < 2)) using 1
    funext N
    norm_num
  have hscaled : Tendsto (fun N : ℕ ↦
      sigma * Real.log (((2 * N + 1 : ℕ) : ℝ))) atTop atTop :=
    (Real.tendsto_log_atTop.comp hbase).const_mul_atTop' hsigma
  have hdecay :=
    (Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero (k + 1)).comp hscaled
  have hconstant : Tendsto (fun _ : ℕ ↦
      Real.exp d * (k.factorial : ℝ) /
        (sigma ^ (k + 1) * d ^ (k + 1))) atTop
      (nhds (Real.exp d * (k.factorial : ℝ) /
        (sigma ^ (k + 1) * d ^ (k + 1)))) :=
    tendsto_const_nhds
  have hproduct := hconstant.mul hdecay
  convert hproduct using 1
  · funext N
    dsimp [d]
    unfold pairedEtaLogLaplaceMomentNearSharpTailUpper
    simp only [Nat.cast_add, Nat.cast_mul,
      Nat.cast_ofNat, Nat.cast_one]
    rw [Real.exp_add, div_pow, mul_pow]
    field_simp [hsigma.ne', hd]
  · simp

/-- The cutoff-optimized finite lower certificates converge to the exact
norm of the complete complex support moment. -/
theorem tendsto_pairedEtaLogLaplaceMomentNearSharpFiniteLower
    (k : ℕ) {s : ℂ} (hs : 0 < s.re) :
    Tendsto (fun N : ℕ ↦
      pairedEtaLogLaplaceMomentNearSharpFiniteLower k s N)
      atTop (nhds ‖pairedEtaLogLaplaceMoment k s‖) := by
  have hprefix := (tendsto_pairedEtaLogLaplaceMomentPartialSum k hs).norm
  have htail :=
    tendsto_pairedEtaLogLaplaceMomentNearSharpTailUpper_zero k hs
  have hzero : Tendsto (fun _ : ℕ ↦ (0 : ℝ)) atTop (nhds 0) :=
    tendsto_const_nhds
  have hlower := hzero.max (hprefix.sub htail)
  simpa [pairedEtaLogLaplaceMomentNearSharpFiniteLower,
    max_eq_right (norm_nonneg (pairedEtaLogLaplaceMoment k s))] using hlower

/-- At a nontrivial zero, the cutoff-optimized finite lower certificates are
eventually valid lower bounds for the exact leading defect norm. -/
theorem eventually_pairedEtaLeadingLogGapMomentNearSharpFiniteLower_le_norm
    (rho : NontrivialZetaZero) :
    ∀ᶠ N : ℕ in atTop,
      pairedEtaLogLaplaceMomentNearSharpFiniteLower
          (analyticZetaZeroMultiplicity rho) rho.1 N ≤
        ‖pairedEtaLeadingLogGapMomentDefect rho‖ := by
  filter_upwards
    [eventually_pairedEtaLogLaplaceMoment_nearSharp_cutoff
      (analyticZetaZeroMultiplicity rho)
      (NontrivialZetaZero.zero_lt_re rho)] with N hcutoff
  exact pairedEtaLeadingLogGapMomentNearSharpFiniteLower_le_norm_defect
    rho N hcutoff

/-- At every nontrivial zero, the cutoff-optimized finite lower certificates
converge to the exact nonzero leading gap-defect norm. -/
theorem tendsto_pairedEtaLeadingLogGapMomentNearSharpFiniteLower
    (rho : NontrivialZetaZero) :
    Tendsto (fun N : ℕ ↦
      pairedEtaLogLaplaceMomentNearSharpFiniteLower
        (analyticZetaZeroMultiplicity rho) rho.1 N)
      atTop (nhds ‖pairedEtaLeadingLogGapMomentDefect rho‖) := by
  rw [pairedEtaLeadingLogGapMomentDefect_eq_logLaplaceMoment]
  exact tendsto_pairedEtaLogLaplaceMomentNearSharpFiniteLower
    (analyticZetaZeroMultiplicity rho)
    (NontrivialZetaZero.zero_lt_re rho)

/-- Consequently, every leading defect has eventually strictly positive
cutoff-optimized finite phase-sensitive lower certificates. -/
theorem eventually_pairedEtaLeadingLogGapMomentNearSharpFiniteLower_pos
    (rho : NontrivialZetaZero) :
    ∀ᶠ N : ℕ in atTop,
      0 < pairedEtaLogLaplaceMomentNearSharpFiniteLower
        (analyticZetaZeroMultiplicity rho) rho.1 N := by
  exact Filter.Tendsto.eventually_const_lt
    (norm_pos_iff.mpr (pairedEtaLeadingLogGapMomentDefect_ne_zero rho))
    (tendsto_pairedEtaLeadingLogGapMomentNearSharpFiniteLower rho)

/-- The completion-weighted sum of the two cutoff-optimized complementary
tail envelopes tends to zero. -/
theorem
    tendsto_pairedEtaCompletedLeadingLogFinitePartnerResidualNearSharpUpper_zero
    (rho : NontrivialZetaZero) :
    Tendsto (fun N : ℕ ↦
      pairedEtaCompletedLeadingLogFinitePartnerResidualNearSharpUpper rho N)
      atTop (nhds 0) := by
  have hpartnerTail :=
    tendsto_pairedEtaLogLaplaceMomentNearSharpTailUpper_zero
      (analyticZetaZeroMultiplicity rho)
      (NontrivialZetaZero.zero_lt_re
        (NontrivialZetaZero.conjugatePartner rho))
  have hrhoTail :=
    tendsto_pairedEtaLogLaplaceMomentNearSharpTailUpper_zero
      (analyticZetaZeroMultiplicity rho)
      (NontrivialZetaZero.zero_lt_re rho)
  have hpartnerWeight : Tendsto
      (fun _ : ℕ ↦ pairedEtaCompletionSpectralWeight
        (NontrivialZetaZero.conjugatePartner rho)) atTop
      (nhds (pairedEtaCompletionSpectralWeight
        (NontrivialZetaZero.conjugatePartner rho))) :=
    tendsto_const_nhds
  have hrhoWeight : Tendsto
      (fun _ : ℕ ↦ pairedEtaCompletionSpectralWeight rho) atTop
      (nhds (pairedEtaCompletionSpectralWeight rho)) :=
    tendsto_const_nhds
  simpa only [pairedEtaCompletedLeadingLogFinitePartnerResidualNearSharpUpper,
    mul_zero, add_zero] using
    (hpartnerWeight.mul hpartnerTail).add (hrhoWeight.mul hrhoTail)

/-- The full phase-sensitive completed partner residual tends to zero under
the cutoff-optimized, full-horizontal-exponent envelope. -/
theorem
    tendsto_pairedEtaCompletedLeadingLogFinitePartnerResidual_zero_of_nearSharp
    (rho : NontrivialZetaZero) :
    Tendsto (fun N : ℕ ↦
      pairedEtaCompletedLeadingLogFinitePartnerResidual rho N)
      atTop (nhds 0) := by
  apply squeeze_zero_norm'
    (show ∀ᶠ N : ℕ in atTop,
      ‖pairedEtaCompletedLeadingLogFinitePartnerResidual rho N‖ ≤
        pairedEtaCompletedLeadingLogFinitePartnerResidualNearSharpUpper
          rho N by
      filter_upwards
        [eventually_pairedEtaLogLaplaceMoment_nearSharp_cutoff
          (analyticZetaZeroMultiplicity rho)
          (NontrivialZetaZero.zero_lt_re
            (NontrivialZetaZero.conjugatePartner rho)),
        eventually_pairedEtaLogLaplaceMoment_nearSharp_cutoff
          (analyticZetaZeroMultiplicity rho)
          (NontrivialZetaZero.zero_lt_re rho)] with N hpartner hrho
      exact
        norm_pairedEtaCompletedLeadingLogFinitePartnerResidual_le_nearSharp
          rho N hpartner hrho)
  exact
    tendsto_pairedEtaCompletedLeadingLogFinitePartnerResidualNearSharpUpper_zero
      rho

end

end RiemannGaussian
