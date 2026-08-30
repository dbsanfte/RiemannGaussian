import RiemannGaussian.RiemannXiSuzukiPositiveCriticalStripEtaLeadingLogMomentFiniteCenteredResidualFiniteWorkTopPrefixComponentGram

/-!
# Sharp complementary-amplitude asymptotics at the top-prefix frontier

The top-prefix Gram frontier has been reduced to the difference between two
positive component magnitudes.  Here the existing sharp centered-tail
asymptotic is transported through the exact component identifications.

At every nontrivial zero, each component has its own strictly positive sharp
limit after normalization by the corresponding complementary endpoint power.
At a hypothetical right-half zero, the partner component is slower.  Scaling
both magnitudes by that slower power makes the conjugate-original component
vanish and leaves the partner's explicit positive constant.  Thus the
amplitude imbalance itself, with no phase information, carries the complete
off-line obstruction.

This diagnoses the remaining scale; it does not prove the universal amplitude
balance estimate.
-/

open Complex Filter MeasureTheory Metric Set Topology
open scoped Classical ComplexConjugate ENNReal Interval Topology

namespace RiemannGaussian

noncomputable section

/-- The sharp positive limiting magnitude of the reflected-partner component. -/
def pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidualFiniteWorkTopPrefixPartnerAmplitudeSharpLimit
    (rho : NontrivialZetaZero) : ℝ :=
  pairedEtaCompletionSpectralWeight
      (NontrivialZetaZero.conjugatePartner rho) *
    ‖((((analyticZetaZeroMultiplicity rho - 1).factorial : ℕ) : ℂ) *
      ((NontrivialZetaZero.conjugatePartner rho).1 ^
        (analyticZetaZeroMultiplicity rho - 1 + 1))⁻¹ / 2)‖

/-- The sharp positive limiting magnitude of the conjugate-original
component. -/
def pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidualFiniteWorkTopPrefixConjugateAmplitudeSharpLimit
    (rho : NontrivialZetaZero) : ℝ :=
  pairedEtaCompletionSpectralWeight rho *
    ‖((((analyticZetaZeroMultiplicity rho - 1).factorial : ℕ) : ℂ) *
      (rho.1 ^ (analyticZetaZeroMultiplicity rho - 1 + 1))⁻¹ / 2)‖

/-- The partner-component sharp constant is strictly positive. -/
theorem
    topPrefixPartnerAmplitudeSharpLimit_pos
    (rho : NontrivialZetaZero) :
    0 <
      pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidualFiniteWorkTopPrefixPartnerAmplitudeSharpLimit
        rho := by
  unfold
    pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidualFiniteWorkTopPrefixPartnerAmplitudeSharpLimit
  exact mul_pos
    (pairedEtaCompletionSpectralWeight_pos
      (NontrivialZetaZero.conjugatePartner rho))
    (pairedEtaCenteredTailAsymptoticValue_norm_pos
      (analyticZetaZeroMultiplicity rho - 1)
      (NontrivialZetaZero.zero_lt_re
        (NontrivialZetaZero.conjugatePartner rho)))

/-- The conjugate-component sharp constant is strictly positive. -/
theorem
    topPrefixConjugateAmplitudeSharpLimit_pos
    (rho : NontrivialZetaZero) :
    0 <
      pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidualFiniteWorkTopPrefixConjugateAmplitudeSharpLimit
        rho := by
  unfold
    pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidualFiniteWorkTopPrefixConjugateAmplitudeSharpLimit
  exact mul_pos
    (pairedEtaCompletionSpectralWeight_pos rho)
    (pairedEtaCenteredTailAsymptoticValue_norm_pos
      (analyticZetaZeroMultiplicity rho - 1)
      (NontrivialZetaZero.zero_lt_re rho))

/-- After normalization by the partner exponent at the actual tail endpoint
`2N+3`, the partner-component magnitude has its explicit positive limit. -/
theorem
    tendsto_succOddEndpoint_partner_rpow_mul_norm_topPrefixPartnerComponent
    (rho : NontrivialZetaZero) :
    Tendsto (fun N : ℕ =>
      (((2 * (N + 1) + 1 : ℕ) : ℝ) ^
          (NontrivialZetaZero.conjugatePartner rho).1.re) *
        ‖pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidualFiniteWorkTopPrefixPartnerComponent
          rho N‖)
      atTop
      (nhds
        (pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidualFiniteWorkTopPrefixPartnerAmplitudeSharpLimit
          rho)) := by
  let partner := NontrivialZetaZero.conjugatePartner rho
  let k := analyticZetaZeroMultiplicity rho - 1
  have hshift : Tendsto (fun N : ℕ => N + 1) atTop atTop :=
    Filter.tendsto_add_atTop_nat 1
  have htail :=
    (tendsto_oddEndpoint_rpow_mul_norm_pairedEtaLogLaplaceMomentCutoffCenteredTail
      k (NontrivialZetaZero.zero_lt_re partner)).comp hshift
  have hweighted := Filter.Tendsto.const_mul
    (pairedEtaCompletionSpectralWeight partner) htail
  convert hweighted using 1
  · funext N
    rw [norm_topPrefixPartnerComponent_eq_completionWeight_mul_norm_partnerTail]
    simp only [Function.comp_apply, partner, k]
    ring
  · unfold
      pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidualFiniteWorkTopPrefixPartnerAmplitudeSharpLimit
    rfl

/-- After normalization by the original exponent at `2N+3`, the
conjugate-original component magnitude has its explicit positive limit. -/
theorem
    tendsto_succOddEndpoint_rho_rpow_mul_norm_topPrefixConjugateComponent
    (rho : NontrivialZetaZero) :
    Tendsto (fun N : ℕ =>
      (((2 * (N + 1) + 1 : ℕ) : ℝ) ^ rho.1.re) *
        ‖pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidualFiniteWorkTopPrefixConjugateComponent
          rho N‖)
      atTop
      (nhds
        (pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidualFiniteWorkTopPrefixConjugateAmplitudeSharpLimit
          rho)) := by
  let k := analyticZetaZeroMultiplicity rho - 1
  have hshift : Tendsto (fun N : ℕ => N + 1) atTop atTop :=
    Filter.tendsto_add_atTop_nat 1
  have htail :=
    (tendsto_oddEndpoint_rpow_mul_norm_pairedEtaLogLaplaceMomentCutoffCenteredTail
      k (NontrivialZetaZero.zero_lt_re rho)).comp hshift
  have hweighted := Filter.Tendsto.const_mul
    (pairedEtaCompletionSpectralWeight rho) htail
  convert hweighted using 1
  · funext N
    rw [norm_topPrefixConjugateComponent_eq_completionWeight_mul_norm_rhoTail]
    simp only [Function.comp_apply, k]
    ring
  · unfold
      pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidualFiniteWorkTopPrefixConjugateAmplitudeSharpLimit
    rfl

/-- The actual successor odd endpoint tends to positive infinity. -/
theorem tendsto_succOddEndpoint_atTop :
    Tendsto (fun N : ℕ => ((2 * (N + 1) + 1 : ℕ) : ℝ)) atTop atTop := by
  convert tendsto_atTop_add_const_right atTop 3
    ((tendsto_natCast_atTop_atTop (R := ℝ)).const_mul_atTop
      (by norm_num : (0 : ℝ) < 2)) using 1
  funext N
  push_cast
  ring

private theorem tendsto_oddEndpoint_div_succOddEndpoint_one :
    Tendsto (fun N : ℕ =>
      ((2 * N + 1 : ℕ) : ℝ) /
        ((2 * (N + 1) + 1 : ℕ) : ℝ))
      atTop (nhds 1) := by
  have hbase : Tendsto (fun N : ℕ => ((2 * N + 1 : ℕ) : ℝ))
      atTop atTop := by
    convert tendsto_atTop_add_const_right atTop 1
      ((tendsto_natCast_atTop_atTop (R := ℝ)).const_mul_atTop
        (by norm_num : (0 : ℝ) < 2)) using 1
    funext N
    norm_num
  have hinv : Tendsto (fun N : ℕ =>
      (((2 * N + 1 : ℕ) : ℝ))⁻¹) atTop (nhds 0) :=
    tendsto_inv_atTop_zero.comp hbase
  have hden : Tendsto (fun N : ℕ =>
      1 + 2 * (((2 * N + 1 : ℕ) : ℝ))⁻¹) atTop (nhds 1) := by
    simpa only [mul_zero, add_zero] using
      tendsto_const_nhds.add (Filter.Tendsto.const_mul 2 hinv)
  have hinvden := hden.inv₀ (by norm_num)
  simpa using hinvden.congr' (by
    filter_upwards with N
    have hx : 0 < (2 * (N : ℝ) + 1) := by positivity
    push_cast
    field_simp [hx.ne', (by positivity : 2 * (N : ℝ) + 3 ≠ 0)]
    ring)

/-- At a right-half off-line zero, the conjugate-original component vanishes
when measured at the slower partner exponent. -/
theorem
    tendsto_succOddEndpoint_partner_rpow_mul_norm_topPrefixConjugateComponent_zero_of_half_lt_re
    (rho : NontrivialZetaZero) (hrho : 1 / 2 < rho.1.re) :
    Tendsto (fun N : ℕ =>
      (((2 * (N + 1) + 1 : ℕ) : ℝ) ^
          (NontrivialZetaZero.conjugatePartner rho).1.re) *
        ‖pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidualFiniteWorkTopPrefixConjugateComponent
          rho N‖)
      atTop (nhds 0) := by
  let partner := NontrivialZetaZero.conjugatePartner rho
  have hgap : 0 < rho.1.re - partner.1.re := by
    have hpartnerRe : partner.1.re = 1 - rho.1.re := by
      simp [partner, NontrivialZetaZero.conjugatePartner_coe]
    rw [hpartnerRe]
    linarith
  have hdecay : Tendsto (fun N : ℕ =>
      (((2 * (N + 1) + 1 : ℕ) : ℝ) ^ (-(rho.1.re - partner.1.re))))
      atTop (nhds 0) :=
    (tendsto_rpow_neg_atTop hgap).comp tendsto_succOddEndpoint_atTop
  have hfast :=
    tendsto_succOddEndpoint_rho_rpow_mul_norm_topPrefixConjugateComponent rho
  have hproduct := hdecay.mul hfast
  simpa only [zero_mul] using hproduct.congr'
    (Eventually.of_forall fun N => by
      let y : ℝ := ((2 * (N + 1) + 1 : ℕ) : ℝ)
      let Q : ℝ :=
        ‖pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidualFiniteWorkTopPrefixConjugateComponent
          rho N‖
      have hy : 0 < y := by
        dsimp only [y]
        positivity
      change y ^ (-(rho.1.re - partner.1.re)) *
          (y ^ rho.1.re * Q) =
        y ^ partner.1.re * Q
      rw [← mul_assoc, ← Real.rpow_add hy]
      congr 2
      ring)

/-- At a right-half off-line zero, the slower-normalized signed amplitude
difference converges to the explicit strictly positive partner constant. -/
theorem
    tendsto_succOddEndpoint_partner_rpow_mul_topPrefixComponentNormDifference_of_half_lt_re
    (rho : NontrivialZetaZero) (hrho : 1 / 2 < rho.1.re) :
    Tendsto (fun N : ℕ =>
      (((2 * (N + 1) + 1 : ℕ) : ℝ) ^
          (NontrivialZetaZero.conjugatePartner rho).1.re) *
        (‖pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidualFiniteWorkTopPrefixPartnerComponent
            rho N‖ -
          ‖pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidualFiniteWorkTopPrefixConjugateComponent
            rho N‖))
      atTop
      (nhds
        (pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidualFiniteWorkTopPrefixPartnerAmplitudeSharpLimit
          rho)) := by
  have hpartner :=
    tendsto_succOddEndpoint_partner_rpow_mul_norm_topPrefixPartnerComponent rho
  have hconjugate :=
    tendsto_succOddEndpoint_partner_rpow_mul_norm_topPrefixConjugateComponent_zero_of_half_lt_re
      rho hrho
  have hdiff := hpartner.sub hconjugate
  simpa only [sub_zero] using hdiff.congr'
    (Eventually.of_forall fun N => by ring)

/-- Squaring the preceding signed limit gives the sharp positive asymptotic
of the amplitude imbalance at twice the partner exponent. -/
theorem
    tendsto_succOddEndpoint_two_mul_partner_rpow_mul_topPrefixAmplitudeImbalance_of_half_lt_re
    (rho : NontrivialZetaZero) (hrho : 1 / 2 < rho.1.re) :
    Tendsto (fun N : ℕ =>
      (((2 * (N + 1) + 1 : ℕ) : ℝ) ^
          (2 * (NontrivialZetaZero.conjugatePartner rho).1.re)) *
        pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidualFiniteWorkTopPrefixAmplitudeImbalance
          rho N)
      atTop
      (nhds
        ((pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidualFiniteWorkTopPrefixPartnerAmplitudeSharpLimit
          rho) ^ 2)) := by
  have hsq :=
    (tendsto_succOddEndpoint_partner_rpow_mul_topPrefixComponentNormDifference_of_half_lt_re
      rho hrho).pow 2
  apply hsq.congr'
  filter_upwards with N
  let y : ℝ := ((2 * (N + 1) + 1 : ℕ) : ℝ)
  let d : ℝ :=
    ‖pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidualFiniteWorkTopPrefixPartnerComponent
        rho N‖ -
      ‖pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidualFiniteWorkTopPrefixConjugateComponent
        rho N‖
  have hy : 0 < y := by
    dsimp only [y]
    positivity
  unfold
    pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidualFiniteWorkTopPrefixAmplitudeImbalance
  change (y ^ (NontrivialZetaZero.conjugatePartner rho).1.re * d) ^ 2 =
    y ^ (2 * (NontrivialZetaZero.conjugatePartner rho).1.re) * d ^ 2
  rw [mul_pow, show 2 * (NontrivialZetaZero.conjugatePartner rho).1.re =
      (NontrivialZetaZero.conjugatePartner rho).1.re +
        (NontrivialZetaZero.conjugatePartner rho).1.re by ring,
    Real.rpow_add hy]
  ring

/-- The same sharp positive amplitude-imbalance limit holds with the frontier
endpoint `2N+1`, rather than the literal successor tail endpoint `2N+3`. -/
theorem
    tendsto_oddEndpoint_two_mul_partner_rpow_mul_topPrefixAmplitudeImbalance_of_half_lt_re
    (rho : NontrivialZetaZero) (hrho : 1 / 2 < rho.1.re) :
    Tendsto (fun N : ℕ =>
      (((2 * N + 1 : ℕ) : ℝ) ^
          (2 * (NontrivialZetaZero.conjugatePartner rho).1.re)) *
        pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidualFiniteWorkTopPrefixAmplitudeImbalance
          rho N)
      atTop
      (nhds
        ((pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidualFiniteWorkTopPrefixPartnerAmplitudeSharpLimit
          rho) ^ 2)) := by
  let exponent : ℝ :=
    2 * (NontrivialZetaZero.conjugatePartner rho).1.re
  have hratioPow : Tendsto (fun N : ℕ =>
      (((2 * N + 1 : ℕ) : ℝ) /
          ((2 * (N + 1) + 1 : ℕ) : ℝ)) ^ exponent)
      atTop (nhds 1) := by
    have hcontinuous :=
      (Real.continuousAt_rpow_const 1 exponent (Or.inl one_ne_zero)).tendsto
    convert hcontinuous.comp tendsto_oddEndpoint_div_succOddEndpoint_one using 1
    · funext N
      rfl
    · rw [Real.one_rpow]
  have hsucc :=
    tendsto_succOddEndpoint_two_mul_partner_rpow_mul_topPrefixAmplitudeImbalance_of_half_lt_re
      rho hrho
  have hproduct := hratioPow.mul hsucc
  simpa only [one_mul] using hproduct.congr'
    (Eventually.of_forall fun N => by
      let x : ℝ := ((2 * N + 1 : ℕ) : ℝ)
      let y : ℝ := ((2 * (N + 1) + 1 : ℕ) : ℝ)
      let A : ℝ :=
        pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidualFiniteWorkTopPrefixAmplitudeImbalance
          rho N
      have hx : 0 < x := by
        dsimp only [x]
        positivity
      have hy : 0 < y := by
        dsimp only [y]
        positivity
      change (x / y) ^ exponent * (y ^ exponent * A) =
        x ^ exponent * A
      rw [Real.div_rpow hx.le hy.le]
      field_simp [(Real.rpow_pos_of_pos hy exponent).ne'])

/-- At a hypothetical right-half zero, the exact endpoint-scaled amplitude
imbalance diverges.  Thus the remaining universal `O(1)` amplitude target is
incompatible with every such zero for a proved sharp-rate reason. -/
theorem
    tendsto_oddEndpoint_mul_topPrefixAmplitudeImbalance_atTop_of_half_lt_re
    (rho : NontrivialZetaZero) (hrho : 1 / 2 < rho.1.re) :
    Tendsto (fun N : ℕ =>
      ((2 * N + 1 : ℕ) : ℝ) *
        pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidualFiniteWorkTopPrefixAmplitudeImbalance
          rho N)
      atTop atTop := by
  let partner := NontrivialZetaZero.conjugatePartner rho
  have hpartnerRe : partner.1.re = 1 - rho.1.re := by
    simp [partner, NontrivialZetaZero.conjugatePartner_coe]
  have hgap : 0 < 1 - 2 * partner.1.re := by
    rw [hpartnerRe]
    linarith
  have hbase : Tendsto (fun N : ℕ => ((2 * N + 1 : ℕ) : ℝ))
      atTop atTop := by
    convert tendsto_atTop_add_const_right atTop 1
      ((tendsto_natCast_atTop_atTop (R := ℝ)).const_mul_atTop
        (by norm_num : (0 : ℝ) < 2)) using 1
    funext N
    norm_num
  have hfactor : Tendsto (fun N : ℕ =>
      (((2 * N + 1 : ℕ) : ℝ) ^ (1 - 2 * partner.1.re)))
      atTop atTop :=
    (tendsto_rpow_atTop hgap).comp hbase
  have hnormalized :=
    tendsto_oddEndpoint_two_mul_partner_rpow_mul_topPrefixAmplitudeImbalance_of_half_lt_re
      rho hrho
  have hlimitPos :
      0 <
        (pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidualFiniteWorkTopPrefixPartnerAmplitudeSharpLimit
          rho) ^ 2 :=
    pow_pos (topPrefixPartnerAmplitudeSharpLimit_pos rho) 2
  have hproduct := hfactor.atTop_mul_pos hlimitPos hnormalized
  apply hproduct.congr'
  filter_upwards with N
  let x : ℝ := ((2 * N + 1 : ℕ) : ℝ)
  let A : ℝ :=
    pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidualFiniteWorkTopPrefixAmplitudeImbalance
      rho N
  have hx : 0 < x := by
    dsimp only [x]
    positivity
  change x ^ (1 - 2 * partner.1.re) *
      (x ^ (2 * partner.1.re) * A) = x * A
  rw [← mul_assoc, ← Real.rpow_add hx]
  have hexponent : 1 - 2 * partner.1.re + 2 * partner.1.re = 1 := by
    ring
  rw [hexponent, Real.rpow_one]

end

end RiemannGaussian
