import RiemannGaussian.RiemannXiSuzukiPositiveCriticalStripEtaLeadingLogMomentFiniteCenteredResidualFiniteWorkTopPrefixFiniteEnergyArithmeticTransport

/-!
# Absolute summability of finite eta energy work

The arithmetic increment formula gains a full endpoint power at every cutoff.
Indeed, the new head interval has width smaller than the logarithmic cutoff
shift, while every transported lower-order prefix carries a strictly positive
power of that same shift.  The already proved limit

`(2N+1) * (log (2N+3) - log (2N+1)) -> 2`

therefore supplies a summable odd-endpoint power majorant for every individual
finite-prefix increment at a nontrivial zero.

Lean propagates this `ell^1` estimate through both completion-weighted
components.  Since the successor finite terms tend to zero, the increment
energies and increment--successor fluxes are also absolutely summable.  The
signed finite energy work is consequently absolutely summable, upgrading its
ordered telescoping limit to a genuine `HasSum` reconstruction at every base
cutoff.  No zero-location hypothesis is used.
-/

open Complex Filter MeasureTheory Metric Set Topology
open scoped Classical ComplexConjugate ENNReal Interval Topology

namespace RiemannGaussian

noncomputable section

/-- The translated first support interval has at most its width to the
`k+1` power as its order-`k` Laplace moment. -/
theorem norm_pairedEtaShiftedLogHeadLaplaceMoment_le
    (k : ℕ) {s : ℂ} (hs : 0 < s.re) (N : ℕ) :
    ‖pairedEtaShiftedLogHeadLaplaceMoment k s N‖ ≤
      pairedEtaShiftedLogHeadWidth N ^ (k + 1) := by
  let w : ℝ := pairedEtaShiftedLogHeadWidth N
  have hw : 0 < w := by
    simpa only [w] using pairedEtaShiftedLogHeadWidth_pos N
  rw [pairedEtaShiftedLogHeadLaplaceMoment,
    pairedEtaShiftedLogHeadMeasure_eq_restrict_Ioc]
  have hbound : ∀ᵐ u : ℝ ∂volume.restrict (Ioc 0 w),
      ‖(u : ℂ) ^ k * Complex.exp (-s * u)‖ ≤ w ^ k := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with u hu
    rw [norm_mul, norm_pow, norm_real, Real.norm_eq_abs, abs_of_pos hu.1,
      Complex.norm_exp]
    have hexp : Real.exp ((-s * (u : ℂ)).re) ≤ 1 := by
      have hre : (-s * (u : ℂ)).re = -s.re * u := by
        simp [Complex.mul_re]
      rw [hre]
      exact Real.exp_le_one_iff.mpr (mul_nonpos_of_nonpos_of_nonneg
        (neg_nonpos.mpr hs.le) hu.1.le)
    exact (mul_le_of_le_one_right (pow_nonneg hu.1.le k) hexp).trans
      (pow_le_pow_left₀ hu.1.le hu.2 k)
  change ‖∫ u : ℝ, (u : ℂ) ^ k * Complex.exp (-s * u)
      ∂volume.restrict (Ioc 0 w)‖ ≤ w ^ (k + 1)
  calc
    ‖∫ u : ℝ, (u : ℂ) ^ k * Complex.exp (-s * u)
          ∂volume.restrict (Ioc 0 w)‖ ≤
        w ^ k * (volume.restrict (Ioc 0 w)).real univ :=
      norm_integral_le_of_norm_le_const hbound
    _ = w ^ (k + 1) := by
      rw [measureReal_restrict_apply_univ,
        Real.volume_real_Ioc_of_le hw.le]
      ring
    _ = pairedEtaShiftedLogHeadWidth N ^ (k + 1) := by rfl

/-- The absolute-coordinate head contribution gains at least `k+1` powers
of the one-step logarithmic shift. -/
theorem norm_pairedEtaLogLaplaceMomentCutoffCenteredHead_le
    (k : ℕ) {s : ℂ} (hs : 0 < s.re) (N : ℕ) :
    ‖pairedEtaLogLaplaceMomentCutoffCenteredHead k s N‖ ≤
      (((2 * N + 1 : ℕ) : ℝ) ^ (-s.re)) *
        pairedEtaLogTailShiftIncrement N ^ (k + 1) := by
  let x : ℝ := ((2 * N + 1 : ℕ) : ℝ)
  have hx : 0 < x := by
    dsimp only [x]
    positivity
  have hhead := norm_pairedEtaShiftedLogHeadLaplaceMoment_le k hs N
  have hwidth : pairedEtaShiftedLogHeadWidth N ^ (k + 1) ≤
      pairedEtaLogTailShiftIncrement N ^ (k + 1) :=
    pow_le_pow_left₀ (pairedEtaShiftedLogHeadWidth_pos N).le
      (pairedEtaShiftedLogHeadWidth_lt_shiftIncrement N).le _
  unfold pairedEtaLogLaplaceMomentCutoffCenteredHead
  rw [norm_mul, Complex.norm_exp]
  have hre :
      (-s * (pairedEtaLogTailCutoff N : ℂ)).re =
        -s.re * pairedEtaLogTailCutoff N := by
    simp [Complex.mul_re]
  rw [hre, show pairedEtaLogTailCutoff N = Real.log x by rfl]
  have hexp : Real.exp (-s.re * Real.log x) = x ^ (-s.re) := by
    rw [Real.rpow_def_of_pos hx]
    congr 1
    ring
  rw [hexp]
  exact mul_le_mul_of_nonneg_left (hhead.trans hwidth)
    (Real.rpow_nonneg hx.le _)

/-- A positive power of the one-step logarithmic shift adds that full power
to the summable endpoint exponent. -/
theorem summable_oddEndpoint_rpow_neg_mul_pairedEtaLogTailShiftIncrement_pow
    {sigma : ℝ} (hsigma : 0 < sigma) {d : ℕ} (hd : 0 < d) :
    Summable (fun N : ℕ ↦
      (((2 * N + 1 : ℕ) : ℝ) ^ (-sigma)) *
        pairedEtaLogTailShiftIncrement N ^ d) := by
  have hdReal : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hp : 1 < sigma + (d : ℝ) := by linarith
  have hbase : Summable (fun N : ℕ ↦
      (((2 * N + 1 : ℕ) : ℝ) ^ (-(sigma + (d : ℝ))))) :=
    (summable_oddEndpoint_rpow_neg_iff (sigma + (d : ℝ))).2 hp
  have hmajor : Summable (fun N : ℕ ↦
      (3 : ℝ) ^ d *
        (((2 * N + 1 : ℕ) : ℝ) ^ (-(sigma + (d : ℝ))))) :=
    hbase.mul_left ((3 : ℝ) ^ d)
  apply hmajor.of_norm_bounded_eventually_nat
  have hscale : ∀ᶠ N : ℕ in atTop,
      ((2 * N + 1 : ℕ) : ℝ) * pairedEtaLogTailShiftIncrement N < 3 :=
    tendsto_oddEndpoint_mul_pairedEtaLogTailShiftIncrement_two.eventually_lt_const
      (by norm_num)
  filter_upwards [hscale] with N hN
  let x : ℝ := ((2 * N + 1 : ℕ) : ℝ)
  let delta : ℝ := pairedEtaLogTailShiftIncrement N
  have hx : 0 < x := by
    dsimp only [x]
    positivity
  have hdelta : 0 < delta := by
    simpa only [delta] using pairedEtaLogTailShiftIncrement_pos N
  have hpow : (x * delta) ^ d ≤ (3 : ℝ) ^ d :=
    pow_le_pow_left₀ (mul_nonneg hx.le hdelta.le) hN.le d
  have hxcombine :
      x ^ (d : ℝ) * x ^ (-(sigma + (d : ℝ))) = x ^ (-sigma) := by
    rw [← Real.rpow_add hx]
    congr 1
    ring
  have hidentity :
      x ^ (-sigma) * delta ^ d =
        (x * delta) ^ d * x ^ (-(sigma + (d : ℝ))) := by
    calc
      x ^ (-sigma) * delta ^ d =
          (x ^ (d : ℝ) * x ^ (-(sigma + (d : ℝ)))) * delta ^ d := by
        rw [hxcombine]
      _ = (x ^ d * delta ^ d) * x ^ (-(sigma + (d : ℝ))) := by
        rw [Real.rpow_natCast]
        ring
      _ = (x * delta) ^ d * x ^ (-(sigma + (d : ℝ))) := by
        rw [mul_pow]
  change ‖x ^ (-sigma) * delta ^ d‖ ≤
    (3 : ℝ) ^ d * x ^ (-(sigma + (d : ℝ)))
  rw [Real.norm_eq_abs, abs_of_nonneg
    (mul_nonneg (Real.rpow_nonneg hx.le _) (pow_nonneg hdelta.le _)),
    hidentity]
  exact mul_le_mul_of_nonneg_right hpow (Real.rpow_nonneg hx.le _)

/-- The newly exposed cutoff head is an absolutely summable complex
sequence throughout the positive half-plane. -/
theorem summable_pairedEtaLogLaplaceMomentCutoffCenteredHead
    (k : ℕ) {s : ℂ} (hs : 0 < s.re) :
    Summable (fun N : ℕ ↦
      pairedEtaLogLaplaceMomentCutoffCenteredHead k s N) := by
  apply
    (summable_oddEndpoint_rpow_neg_mul_pairedEtaLogTailShiftIncrement_pow
      hs (Nat.succ_pos k)).of_norm_bounded
  exact fun N ↦ norm_pairedEtaLogLaplaceMomentCutoffCenteredHead_le k hs N

/-- At a zero, a positive shift power times any lower centered finite prefix
is absolutely summable. -/
theorem
    summable_pairedEtaLogTailShiftIncrement_pow_mul_cutoffCenteredPartialSum_of_lt_multiplicity
    (rho : NontrivialZetaZero) {j d : ℕ}
    (hj : j < analyticZetaZeroMultiplicity rho) (hd : 0 < d) :
    Summable (fun N : ℕ ↦
      (pairedEtaLogTailShiftIncrement N : ℂ) ^ d *
        pairedEtaLogLaplaceMomentCutoffCenteredPartialSum j rho.1 (N + 1)) := by
  let sigma : ℝ := rho.1.re
  let C : ℝ := (j.factorial : ℝ) / sigma ^ (j + 1)
  have hsigma : 0 < sigma := by
    simpa only [sigma] using NontrivialZetaZero.zero_lt_re rho
  have hC : 0 ≤ C := by
    dsimp only [C]
    positivity
  have hmodel : Summable (fun N : ℕ ↦
      C * ((((2 * N + 1 : ℕ) : ℝ) ^ (-sigma)) *
        pairedEtaLogTailShiftIncrement N ^ d)) :=
    (summable_oddEndpoint_rpow_neg_mul_pairedEtaLogTailShiftIncrement_pow
      hsigma hd).mul_left C
  apply hmodel.of_norm_bounded
  intro N
  let x : ℝ := ((2 * N + 1 : ℕ) : ℝ)
  let y : ℝ := ((2 * (N + 1) + 1 : ℕ) : ℝ)
  let delta : ℝ := pairedEtaLogTailShiftIncrement N
  have hx : 0 < x := by dsimp only [x]; positivity
  have hxy : x ≤ y := by
    dsimp only [x, y]
    norm_num
  have hdelta : 0 < delta := by
    simpa only [delta] using pairedEtaLogTailShiftIncrement_pos N
  have hrpow : y ^ (-sigma) ≤ x ^ (-sigma) :=
    Real.rpow_le_rpow_of_nonpos hx hxy (by linarith)
  have hpartial :
      ‖pairedEtaLogLaplaceMomentCutoffCenteredPartialSum j rho.1 (N + 1)‖ =
        ‖pairedEtaLogLaplaceMomentCutoffCenteredTail j rho.1 (N + 1)‖ := by
    have hzero :=
      pairedEtaLogLaplaceMomentCutoffCenteredTail_eq_neg_partial_of_lt_multiplicity
        rho hj (N + 1)
    have hnorm := congrArg norm hzero
    simpa only [norm_neg] using hnorm.symm
  have htail := norm_pairedEtaLogLaplaceMomentCutoffCenteredTail_le
    j hsigma (N + 1)
  rw [pairedEtaLogLaplaceMomentCenteredTailUpper_eq_rpow] at htail
  change ‖(delta : ℂ) ^ d *
      pairedEtaLogLaplaceMomentCutoffCenteredPartialSum j rho.1 (N + 1)‖ ≤
    C * (x ^ (-sigma) * delta ^ d)
  rw [norm_mul, norm_pow, norm_real, Real.norm_eq_abs,
    abs_of_pos hdelta, hpartial]
  calc
    delta ^ d *
          ‖pairedEtaLogLaplaceMomentCutoffCenteredTail j rho.1 (N + 1)‖ ≤
        delta ^ d * (y ^ (-sigma) * C) :=
      mul_le_mul_of_nonneg_left (by simpa only [sigma, C, y] using htail)
        (pow_nonneg hdelta.le _)
    _ ≤ delta ^ d * (x ^ (-sigma) * C) :=
      mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_right hrpow hC)
        (pow_nonneg hdelta.le _)
    _ = C * (x ^ (-sigma) * delta ^ d) := by ring

/-- Every individual arithmetic finite-prefix work below the zero
multiplicity is absolutely summable over all cutoffs. -/
theorem summable_pairedEtaLogLaplaceMomentCutoffCenteredFiniteWork_of_lt_multiplicity
    (rho : NontrivialZetaZero) {k : ℕ}
    (hk : k < analyticZetaZeroMultiplicity rho) :
    Summable (fun N : ℕ ↦
      pairedEtaLogLaplaceMomentCutoffCenteredFiniteWork k rho.1 N) := by
  have hhead := summable_pairedEtaLogLaplaceMomentCutoffCenteredHead k
    (NontrivialZetaZero.zero_lt_re rho)
  have hlower : Summable (fun N : ℕ ↦
      ∑ j ∈ Finset.range k,
        (((k.choose j : ℕ) : ℂ) *
          (pairedEtaLogTailShiftIncrement N : ℂ) ^ (k - j) *
          pairedEtaLogLaplaceMomentCutoffCenteredPartialSum j rho.1
            (N + 1))) := by
    apply summable_sum
    intro j hj
    have hjk : j < k := Finset.mem_range.mp hj
    have hjm : j < analyticZetaZeroMultiplicity rho := hjk.trans hk
    have hd : 0 < k - j := by omega
    have hterm :=
      summable_pairedEtaLogTailShiftIncrement_pow_mul_cutoffCenteredPartialSum_of_lt_multiplicity
        rho hjm hd
    exact (hterm.mul_left (((k.choose j : ℕ) : ℂ))).congr fun N ↦ by
      ring
  simpa only [pairedEtaLogLaplaceMomentCutoffCenteredFiniteWork] using
    hhead.neg.add hlower

/-- The completed reflected-partner arithmetic increments form an absolutely
summable complex series. -/
theorem summable_topPrefixFinitePartnerArithmeticIncrement
    (rho : NontrivialZetaZero) :
    Summable (fun N : ℕ ↦
      pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidualFiniteWorkTopPrefixFinitePartnerArithmeticIncrement
        rho N) := by
  let partner := NontrivialZetaZero.conjugatePartner rho
  let k := analyticZetaZeroMultiplicity rho - 1
  have hk : k < analyticZetaZeroMultiplicity partner := by
    dsimp only [k, partner]
    rw [analyticZetaZeroMultiplicity_conjugatePartner]
    have hm := analyticZetaZeroMultiplicity_positive rho
    omega
  have hwork :=
    summable_pairedEtaLogLaplaceMomentCutoffCenteredFiniteWork_of_lt_multiplicity
      partner hk
  have hshift := (summable_nat_add_iff 1).2 hwork
  exact
    (hshift.mul_left
      (pairedEtaXiCompletionFactor partner.1 * partner.1)).congr fun N ↦ by
        rfl

/-- The completed conjugate-original arithmetic increments form an
absolutely summable complex series. -/
theorem summable_topPrefixFiniteConjugateArithmeticIncrement
    (rho : NontrivialZetaZero) :
    Summable (fun N : ℕ ↦
      pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidualFiniteWorkTopPrefixFiniteConjugateArithmeticIncrement
        rho N) := by
  let k := analyticZetaZeroMultiplicity rho - 1
  have hk : k < analyticZetaZeroMultiplicity rho := by
    dsimp only [k]
    have hm := analyticZetaZeroMultiplicity_positive rho
    omega
  have hwork :=
    summable_pairedEtaLogLaplaceMomentCutoffCenteredFiniteWork_of_lt_multiplicity
      rho hk
  have hshift := (summable_nat_add_iff 1).2 hwork
  have hweighted :=
    hshift.mul_left (pairedEtaXiCompletionFactor rho.1 * rho.1)
  exact
    (hweighted.star.mul_left
      ((-1 : ℂ) ^ analyticZetaZeroMultiplicity rho)).congr fun N ↦ by
        rfl

/-- The named partner increments are absolutely summable. -/
theorem summable_topPrefixFinitePartnerIncrement
    (rho : NontrivialZetaZero) :
    Summable (fun N : ℕ ↦
      pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidualFiniteWorkTopPrefixFinitePartnerIncrement
        rho N) :=
  (summable_topPrefixFinitePartnerArithmeticIncrement rho).congr fun N ↦
    (topPrefixFinitePartnerIncrement_eq_arithmeticIncrement rho N).symm

/-- The named conjugate-original increments are absolutely summable. -/
theorem summable_topPrefixFiniteConjugateIncrement
    (rho : NontrivialZetaZero) :
    Summable (fun N : ℕ ↦
      pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidualFiniteWorkTopPrefixFiniteConjugateIncrement
        rho N) :=
  (summable_topPrefixFiniteConjugateArithmeticIncrement rho).congr fun N ↦
    (topPrefixFiniteConjugateIncrement_eq_arithmeticIncrement rho N).symm

/-- Multiplying an absolutely summable norm by a second norm tending to zero
preserves summability. -/
theorem summable_norm_mul_of_summable_left_of_tendsto_norm_zero
    {f g : ℕ → ℂ} (hf : Summable f)
    (hg : Tendsto (fun N : ℕ ↦ ‖g N‖) atTop (nhds 0)) :
    Summable (fun N : ℕ ↦ ‖f N‖ * ‖g N‖) := by
  apply hf.norm.of_norm_bounded_eventually_nat
  have hsmall : ∀ᶠ N : ℕ in atTop, ‖g N‖ < 1 :=
    hg.eventually_lt_const zero_lt_one
  filter_upwards [hsmall] with N hN
  rw [Real.norm_eq_abs, abs_of_nonneg
    (mul_nonneg (norm_nonneg _) (norm_nonneg _))]
  simpa only [mul_one] using
    mul_le_mul_of_nonneg_left hN.le (norm_nonneg (f N))

/-- The squared complex norms of an absolutely summable complex series are
summable. -/
theorem summable_complexNormSq_of_summable {f : ℕ → ℂ}
    (hf : Summable f) :
    Summable (fun N : ℕ ↦ Complex.normSq (f N)) := by
  have hnormZero : Tendsto (fun N : ℕ ↦ ‖f N‖) atTop (nhds 0) := by
    simpa only [norm_zero] using hf.tendsto_atTop_zero.norm
  have hproduct :=
    summable_norm_mul_of_summable_left_of_tendsto_norm_zero hf
      hnormZero
  simpa only [Complex.normSq_eq_norm_sq, pow_two] using hproduct

/-- The absolute signed finite energy work is summable at every nontrivial
zero, without a zero-location hypothesis. -/
theorem summable_abs_topPrefixFiniteEnergyWork
    (rho : NontrivialZetaZero) :
    Summable (fun N : ℕ ↦
      |pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidualFiniteWorkTopPrefixFiniteEnergyWork
        rho N|) := by
  let pInc : ℕ → ℂ := fun N ↦
    pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidualFiniteWorkTopPrefixFinitePartnerIncrement
      rho N
  let qInc : ℕ → ℂ := fun N ↦
    pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidualFiniteWorkTopPrefixFiniteConjugateIncrement
      rho N
  let pTerm : ℕ → ℂ := fun N ↦
    pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidualFiniteWorkTopPrefixFinitePartnerTerm
      rho (N + 1)
  let qTerm : ℕ → ℂ := fun N ↦
    pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidualFiniteWorkTopPrefixFiniteConjugateTerm
      rho (N + 1)
  have hpInc : Summable pInc := by
    simpa only [pInc] using summable_topPrefixFinitePartnerIncrement rho
  have hqInc : Summable qInc := by
    simpa only [qInc] using summable_topPrefixFiniteConjugateIncrement rho
  have hshift : Tendsto (fun N : ℕ ↦ N + 1) atTop atTop :=
    Filter.tendsto_add_atTop_nat 1
  have hpTerm : Tendsto (fun N : ℕ ↦ ‖pTerm N‖) atTop (nhds 0) := by
    have h := (tendsto_topPrefixFinitePartnerAmplitude_zero rho).comp hshift
    simpa [pTerm, Function.comp_def,
      norm_topPrefixFinitePartnerTerm_eq_finitePartnerAmplitude]
      using h
  have hqTerm : Tendsto (fun N : ℕ ↦ ‖qTerm N‖) atTop (nhds 0) := by
    have h := (tendsto_topPrefixFiniteConjugateAmplitude_zero rho).comp hshift
    simpa [qTerm, Function.comp_def,
      norm_topPrefixFiniteConjugateTerm_eq_finiteConjugateAmplitude]
      using h
  have hpSq : Summable (fun N : ℕ ↦ Complex.normSq (pInc N)) :=
    summable_complexNormSq_of_summable hpInc
  have hqSq : Summable (fun N : ℕ ↦ Complex.normSq (qInc N)) :=
    summable_complexNormSq_of_summable hqInc
  have hpFlux : Summable (fun N : ℕ ↦ ‖pInc N‖ * ‖pTerm N‖) :=
    summable_norm_mul_of_summable_left_of_tendsto_norm_zero hpInc hpTerm
  have hqFlux : Summable (fun N : ℕ ↦ ‖qInc N‖ * ‖qTerm N‖) :=
    summable_norm_mul_of_summable_left_of_tendsto_norm_zero hqInc hqTerm
  have hmajor : Summable (fun N : ℕ ↦
      Complex.normSq (pInc N) + Complex.normSq (qInc N) +
        2 * (‖pInc N‖ * ‖pTerm N‖ + ‖qInc N‖ * ‖qTerm N‖)) :=
    (hpSq.add hqSq).add ((hpFlux.add hqFlux).mul_left 2)
  apply hmajor.of_nonneg_of_le
  · exact fun N ↦ abs_nonneg _
  · intro N
    simpa only [pInc, qInc, pTerm, qTerm] using
      abs_topPrefixFiniteEnergyWork_le_increment_energy_add_flux rho N

/-- Absolute summability promotes the finite ordered telescope to a genuine
series reconstruction of the signed finite eta energy at every base cutoff. -/
theorem hasSum_topPrefixFiniteEnergyWork
    (rho : NontrivialZetaZero) (N : ℕ) :
    HasSum (fun q : ℕ ↦
      pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidualFiniteWorkTopPrefixFiniteEnergyWork
        rho (N + q))
      (pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidualFiniteWorkTopPrefixFiniteEnergyDifference
        rho N) := by
  have habs : Summable (fun q : ℕ ↦
      |pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidualFiniteWorkTopPrefixFiniteEnergyWork
        rho (N + q)|) := by
    have h :=
      (summable_nat_add_iff N).2 (summable_abs_topPrefixFiniteEnergyWork rho)
    exact h.congr fun q ↦ by rw [Nat.add_comm]
  have hnorm : Summable (fun q : ℕ ↦
      ‖pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidualFiniteWorkTopPrefixFiniteEnergyWork
        rho (N + q)‖) := by
    simpa only [Real.norm_eq_abs] using habs
  exact (hasSum_iff_tendsto_nat_of_summable_norm hnorm).2
    (tendsto_sum_range_topPrefixFiniteEnergyWork rho N)

/-- Dividing the absolutely convergent reconstruction by the fixed total
amplitude recovers the normalized finite energy defect as a genuine series. -/
theorem hasSum_topPrefixFiniteEnergyWork_div_total
    (rho : NontrivialZetaZero) (N : ℕ) :
    HasSum (fun q : ℕ ↦
      pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidualFiniteWorkTopPrefixFiniteEnergyWork
          rho (N + q) /
        pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidualFiniteWorkTopPrefixFiniteTotalAmplitude
          rho N)
      (pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidualFiniteWorkTopPrefixNormalizedFiniteEnergyDefect
        rho N) := by
  have h := (hasSum_topPrefixFiniteEnergyWork rho N).div_const
    (pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidualFiniteWorkTopPrefixFiniteTotalAmplitude
      rho N)
  simpa only [
    pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidualFiniteWorkTopPrefixNormalizedFiniteEnergyDefect]
    using h

end

end RiemannGaussian
