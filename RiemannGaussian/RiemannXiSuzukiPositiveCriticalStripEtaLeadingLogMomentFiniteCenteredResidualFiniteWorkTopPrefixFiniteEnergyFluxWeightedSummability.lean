import RiemannGaussian.RiemannXiSuzukiPositiveCriticalStripEtaLeadingLogMomentFiniteCenteredResidualFiniteWorkTopPrefixFiniteEnergyWorkWeightedSummability

/-!
# Critical first moment of the finite eta energy flux

The exact cutoff transport law splits the finite energy work as

`J_N = I_N + F_N`,

where `I_N` is the signed energy of the two component increments and `F_N`
is their cross flux against the successor finite terms.  This module proves
that the first weighted absolute moment of `I_N` is finite at every
nontrivial zero, without any zero-location hypothesis.

The proof uses the full extra endpoint power in each explicit arithmetic
increment.  After squaring, one factor of the logarithmic cutoff shift absorbs
the odd-endpoint weight, while the remaining positive shift power gives a
summable majorant throughout the critical strip.  Finite-sum energy estimates
then propagate this fact through the complete head-plus-lower-prefix work.

Consequently the critical first moment of the total work is summable exactly
when the first moment of the successor flux is summable.  Combined with the
previous exact criterion, flux first-moment summability is equivalent to the
critical-line equation at each zero, and universally equivalent to RH.  This
is a genuine isolation of the remaining term, not a proof of its open
arithmetic estimate.
-/

open Complex Filter MeasureTheory Metric Set Topology
open scoped Classical ComplexConjugate ENNReal Interval Topology

namespace RiemannGaussian

noncomputable section

/-- Squaring a shifted endpoint-power model makes its odd-endpoint first
moment summable.  One shift factor absorbs the weight and at least one
positive shift power remains. -/
theorem
    summable_oddEndpoint_mul_sq_rpow_neg_mul_pairedEtaLogTailShiftIncrement_pow
    {sigma : ℝ} (hsigma : 0 < sigma) {d : ℕ} (hd : 0 < d) :
    Summable (fun N : ℕ ↦
      ((2 * N + 1 : ℕ) : ℝ) *
        (((((2 * N + 1 : ℕ) : ℝ) ^ (-sigma)) *
          pairedEtaLogTailShiftIncrement N ^ d) ^ 2)) := by
  have htwoSigma : 0 < 2 * sigma := by linarith
  have hdegree : 0 < 2 * d - 1 := by omega
  have hbase :=
    summable_oddEndpoint_rpow_neg_mul_pairedEtaLogTailShiftIncrement_pow
      htwoSigma hdegree
  have hmajor : Summable (fun N : ℕ ↦
      (3 : ℝ) *
        (((2 * N + 1 : ℕ) : ℝ) ^ (-(2 * sigma)) *
          pairedEtaLogTailShiftIncrement N ^ (2 * d - 1))) :=
    hbase.mul_left 3
  apply hmajor.of_norm_bounded_eventually_nat
  have hscale : ∀ᶠ N : ℕ in atTop,
      ((2 * N + 1 : ℕ) : ℝ) * pairedEtaLogTailShiftIncrement N < 3 :=
    tendsto_oddEndpoint_mul_pairedEtaLogTailShiftIncrement_two.eventually_lt_const
      (by norm_num)
  filter_upwards [hscale] with N hN
  let x : ℝ := ((2 * N + 1 : ℕ) : ℝ)
  let delta : ℝ := pairedEtaLogTailShiftIncrement N
  have hx : 0 < x := by dsimp only [x]; positivity
  have hdelta : 0 < delta := by
    simpa only [delta] using pairedEtaLogTailShiftIncrement_pos N
  have hrpowSq : (x ^ (-sigma)) ^ 2 = x ^ (-(2 * sigma)) := by
    rw [← Real.rpow_natCast]
    rw [← Real.rpow_mul hx.le]
    congr 1
    norm_num
    ring
  have hdeltaSq : (delta ^ d) ^ 2 =
      delta * delta ^ (2 * d - 1) := by
    rw [← pow_mul]
    rw [show d * 2 = 1 + (2 * d - 1) by omega, pow_add]
    simp
  have hidentity :
      x * (x ^ (-sigma) * delta ^ d) ^ 2 =
        (x * delta) *
          (x ^ (-(2 * sigma)) * delta ^ (2 * d - 1)) := by
    rw [mul_pow, hrpowSq, hdeltaSq]
    ring
  change ‖x * (x ^ (-sigma) * delta ^ d) ^ 2‖ ≤
    3 * (x ^ (-(2 * sigma)) * delta ^ (2 * d - 1))
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity), hidentity]
  exact mul_le_mul_of_nonneg_right hN.le (by positivity)

/-- The newly exposed cutoff head has a summable endpoint-weighted squared
norm throughout the positive half-plane. -/
theorem
    summable_oddEndpoint_mul_normSq_pairedEtaLogLaplaceMomentCutoffCenteredHead
    (k : ℕ) {s : ℂ} (hs : 0 < s.re) :
    Summable (fun N : ℕ ↦
      ((2 * N + 1 : ℕ) : ℝ) *
        Complex.normSq
          (pairedEtaLogLaplaceMomentCutoffCenteredHead k s N)) := by
  have hmodel :=
    summable_oddEndpoint_mul_sq_rpow_neg_mul_pairedEtaLogTailShiftIncrement_pow
      hs (Nat.succ_pos k)
  apply hmodel.of_nonneg_of_le
  · exact fun N ↦ mul_nonneg (by positivity) (Complex.normSq_nonneg _)
  · intro N
    rw [Complex.normSq_eq_norm_sq]
    have hbound :=
      norm_pairedEtaLogLaplaceMomentCutoffCenteredHead_le k hs N
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    exact pow_le_pow_left₀ (norm_nonneg _) hbound 2

/-- Quantitative endpoint-power bound for a shifted lower centered prefix at
a zero, retaining the exact positive shift power. -/
theorem
    norm_pairedEtaLogTailShiftIncrement_pow_mul_cutoffCenteredPartialSum_le
    (rho : NontrivialZetaZero) {j d : ℕ}
    (hj : j < analyticZetaZeroMultiplicity rho) (N : ℕ) :
    ‖(pairedEtaLogTailShiftIncrement N : ℂ) ^ d *
        pairedEtaLogLaplaceMomentCutoffCenteredPartialSum j rho.1 (N + 1)‖ ≤
      ((j.factorial : ℝ) / rho.1.re ^ (j + 1)) *
        (((2 * N + 1 : ℕ) : ℝ) ^ (-rho.1.re) *
          pairedEtaLogTailShiftIncrement N ^ d) := by
  let sigma : ℝ := rho.1.re
  let C : ℝ := (j.factorial : ℝ) / sigma ^ (j + 1)
  let x : ℝ := ((2 * N + 1 : ℕ) : ℝ)
  let y : ℝ := ((2 * (N + 1) + 1 : ℕ) : ℝ)
  let delta : ℝ := pairedEtaLogTailShiftIncrement N
  have hsigma : 0 < sigma := by
    simpa only [sigma] using NontrivialZetaZero.zero_lt_re rho
  have hC : 0 ≤ C := by dsimp only [C]; positivity
  have hx : 0 < x := by dsimp only [x]; positivity
  have hxy : x ≤ y := by dsimp only [x, y]; norm_num
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

/-- Every lower centered-prefix transport term has summable
endpoint-weighted squared norm below the exact zero multiplicity. -/
theorem
    summable_oddEndpoint_mul_normSq_pairedEtaLogTailShiftIncrement_pow_mul_cutoffCenteredPartialSum_of_lt_multiplicity
    (rho : NontrivialZetaZero) {j d : ℕ}
    (hj : j < analyticZetaZeroMultiplicity rho) (hd : 0 < d) :
    Summable (fun N : ℕ ↦
      ((2 * N + 1 : ℕ) : ℝ) *
        Complex.normSq
          ((pairedEtaLogTailShiftIncrement N : ℂ) ^ d *
            pairedEtaLogLaplaceMomentCutoffCenteredPartialSum j rho.1
              (N + 1))) := by
  let C : ℝ := (j.factorial : ℝ) / rho.1.re ^ (j + 1)
  have hmodel :=
    summable_oddEndpoint_mul_sq_rpow_neg_mul_pairedEtaLogTailShiftIncrement_pow
      (NontrivialZetaZero.zero_lt_re rho) hd
  have hmajor : Summable (fun N : ℕ ↦
      C ^ 2 *
        (((2 * N + 1 : ℕ) : ℝ) *
          (((((2 * N + 1 : ℕ) : ℝ) ^ (-rho.1.re)) *
            pairedEtaLogTailShiftIncrement N ^ d) ^ 2))) :=
    hmodel.mul_left (C ^ 2)
  apply hmajor.of_nonneg_of_le
  · exact fun N ↦ mul_nonneg (by positivity) (Complex.normSq_nonneg _)
  · intro N
    rw [Complex.normSq_eq_norm_sq]
    have hbound :=
      norm_pairedEtaLogTailShiftIncrement_pow_mul_cutoffCenteredPartialSum_le
        rho (d := d) hj N
    have hsquare := pow_le_pow_left₀ (norm_nonneg _) hbound 2
    calc
      ((2 * N + 1 : ℕ) : ℝ) *
          ‖(pairedEtaLogTailShiftIncrement N : ℂ) ^ d *
            pairedEtaLogLaplaceMomentCutoffCenteredPartialSum j rho.1
              (N + 1)‖ ^ 2 ≤
        ((2 * N + 1 : ℕ) : ℝ) *
          (C *
            (((2 * N + 1 : ℕ) : ℝ) ^ (-rho.1.re) *
              pairedEtaLogTailShiftIncrement N ^ d)) ^ 2 :=
        mul_le_mul_of_nonneg_left hsquare (by positivity)
      _ = C ^ 2 *
          (((2 * N + 1 : ℕ) : ℝ) *
            (((((2 * N + 1 : ℕ) : ℝ) ^ (-rho.1.re)) *
              pairedEtaLogTailShiftIncrement N ^ d) ^ 2)) := by ring

/-- Weighted squared-norm summability is stable under pointwise addition of
complex sequences. -/
theorem summable_weight_mul_complexNormSq_add
    {w : ℕ → ℝ} (hw : ∀ N, 0 ≤ w N) {f g : ℕ → ℂ}
    (hf : Summable (fun N : ℕ ↦ w N * Complex.normSq (f N)))
    (hg : Summable (fun N : ℕ ↦ w N * Complex.normSq (g N))) :
    Summable (fun N : ℕ ↦ w N * Complex.normSq (f N + g N)) := by
  have hmajor : Summable (fun N : ℕ ↦
      2 * (w N * Complex.normSq (f N) +
        w N * Complex.normSq (g N))) :=
    (hf.add hg).mul_left 2
  apply hmajor.of_nonneg_of_le
  · exact fun N ↦ mul_nonneg (hw N) (Complex.normSq_nonneg _)
  · intro N
    simp only [Complex.normSq_eq_norm_sq]
    have hadd : ‖f N + g N‖ ≤ ‖f N‖ + ‖g N‖ := norm_add_le _ _
    have hsquare : ‖f N + g N‖ ^ 2 ≤ (‖f N‖ + ‖g N‖) ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) hadd 2
    have htwo : (‖f N‖ + ‖g N‖) ^ 2 ≤
        2 * (‖f N‖ ^ 2 + ‖g N‖ ^ 2) := by
      nlinarith [sq_nonneg (‖f N‖ - ‖g N‖)]
    calc
      w N * ‖f N + g N‖ ^ 2 ≤
          w N * (‖f N‖ + ‖g N‖) ^ 2 :=
        mul_le_mul_of_nonneg_left hsquare (hw N)
      _ ≤ w N * (2 * (‖f N‖ ^ 2 + ‖g N‖ ^ 2)) :=
        mul_le_mul_of_nonneg_left htwo (hw N)
      _ = 2 * (w N * ‖f N‖ ^ 2 + w N * ‖g N‖ ^ 2) := by ring

/-- Weighted squared-norm summability is stable under a fixed finite sum of
complex sequences. -/
theorem summable_weight_mul_complexNormSq_finset_sum
    {ι : Type*} [DecidableEq ι] {w : ℕ → ℝ} (hw : ∀ N, 0 ≤ w N)
    (s : Finset ι) (f : ι → ℕ → ℂ)
    (hf : ∀ i ∈ s,
      Summable (fun N : ℕ ↦ w N * Complex.normSq (f i N))) :
    Summable (fun N : ℕ ↦
      w N * Complex.normSq (∑ i ∈ s, f i N)) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
      have haSum := hf a (Finset.mem_insert_self a s)
      have hsSum := ih (fun i hi ↦ hf i (Finset.mem_insert_of_mem hi))
      have h := summable_weight_mul_complexNormSq_add hw haSum hsSum
      simpa only [Finset.sum_insert ha] using h

/-- Every explicit centered finite work below the zero multiplicity has a
summable endpoint-weighted squared norm. -/
theorem
    summable_oddEndpoint_mul_normSq_pairedEtaLogLaplaceMomentCutoffCenteredFiniteWork_of_lt_multiplicity
    (rho : NontrivialZetaZero) {k : ℕ}
    (hk : k < analyticZetaZeroMultiplicity rho) :
    Summable (fun N : ℕ ↦
      ((2 * N + 1 : ℕ) : ℝ) *
        Complex.normSq
          (pairedEtaLogLaplaceMomentCutoffCenteredFiniteWork k rho.1 N)) := by
  let w : ℕ → ℝ := fun N ↦ ((2 * N + 1 : ℕ) : ℝ)
  have hw : ∀ N, 0 ≤ w N := fun N ↦ by dsimp only [w]; positivity
  have hheadRaw :=
    summable_oddEndpoint_mul_normSq_pairedEtaLogLaplaceMomentCutoffCenteredHead
      k (NontrivialZetaZero.zero_lt_re rho)
  have hhead : Summable (fun N : ℕ ↦
      w N * Complex.normSq
        (-pairedEtaLogLaplaceMomentCutoffCenteredHead k rho.1 N)) := by
    simpa only [w, Complex.normSq_neg] using hheadRaw
  have hlower : Summable (fun N : ℕ ↦
      w N * Complex.normSq
        (∑ j ∈ Finset.range k,
          (((k.choose j : ℕ) : ℂ) *
            (pairedEtaLogTailShiftIncrement N : ℂ) ^ (k - j) *
            pairedEtaLogLaplaceMomentCutoffCenteredPartialSum j rho.1
              (N + 1)))) := by
    apply summable_weight_mul_complexNormSq_finset_sum hw
    intro j hj
    have hjk : j < k := Finset.mem_range.mp hj
    have hjm : j < analyticZetaZeroMultiplicity rho := hjk.trans hk
    have hd : 0 < k - j := by omega
    have hbase :=
      summable_oddEndpoint_mul_normSq_pairedEtaLogTailShiftIncrement_pow_mul_cutoffCenteredPartialSum_of_lt_multiplicity
        rho hjm hd
    have hscaled :=
      hbase.mul_left (Complex.normSq (((k.choose j : ℕ) : ℂ)))
    apply hscaled.congr
    intro N
    simp only [Complex.normSq_mul, w]
    ring
  have h := summable_weight_mul_complexNormSq_add hw hhead hlower
  simpa only [w,
    pairedEtaLogLaplaceMomentCutoffCenteredFiniteWork] using h

/-- Shifting a complex sequence forward by one preserves its odd-endpoint
weighted squared-norm summability. -/
theorem summable_oddEndpoint_mul_complexNormSq_nat_add_one {f : ℕ → ℂ}
    (hf : Summable (fun N : ℕ ↦
      ((2 * N + 1 : ℕ) : ℝ) * Complex.normSq (f N))) :
    Summable (fun N : ℕ ↦
      ((2 * N + 1 : ℕ) : ℝ) * Complex.normSq (f (N + 1))) := by
  have hlarge := (summable_nat_add_iff 1).2 hf
  apply hlarge.of_nonneg_of_le
  · exact fun N ↦ mul_nonneg (by positivity) (Complex.normSq_nonneg _)
  · intro N
    apply mul_le_mul_of_nonneg_right _ (Complex.normSq_nonneg _)
    norm_num

/-- The completed reflected-partner arithmetic increments have summable
odd-endpoint weighted squared norms. -/
theorem summable_oddEndpoint_mul_normSq_topPrefixFinitePartnerArithmeticIncrement
    (rho : NontrivialZetaZero) :
    Summable (fun N : ℕ ↦
      ((2 * N + 1 : ℕ) : ℝ) *
        Complex.normSq
          (pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidualFiniteWorkTopPrefixFinitePartnerArithmeticIncrement
            rho N)) := by
  let partner := NontrivialZetaZero.conjugatePartner rho
  let k := analyticZetaZeroMultiplicity rho - 1
  let C : ℂ := pairedEtaXiCompletionFactor partner.1 * partner.1
  have hk : k < analyticZetaZeroMultiplicity partner := by
    dsimp only [k, partner]
    rw [analyticZetaZeroMultiplicity_conjugatePartner]
    have hm := analyticZetaZeroMultiplicity_positive rho
    omega
  have hwork :=
    summable_oddEndpoint_mul_normSq_pairedEtaLogLaplaceMomentCutoffCenteredFiniteWork_of_lt_multiplicity
      partner hk
  have hshift := summable_oddEndpoint_mul_complexNormSq_nat_add_one hwork
  have hscaled := hshift.mul_left (Complex.normSq C)
  apply hscaled.congr
  intro N
  unfold
    pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidualFiniteWorkTopPrefixFinitePartnerArithmeticIncrement
  simp only [C, partner, k, Complex.normSq_mul]
  ring

/-- The completed conjugate-original arithmetic increments have summable
odd-endpoint weighted squared norms. -/
theorem summable_oddEndpoint_mul_normSq_topPrefixFiniteConjugateArithmeticIncrement
    (rho : NontrivialZetaZero) :
    Summable (fun N : ℕ ↦
      ((2 * N + 1 : ℕ) : ℝ) *
        Complex.normSq
          (pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidualFiniteWorkTopPrefixFiniteConjugateArithmeticIncrement
            rho N)) := by
  let k := analyticZetaZeroMultiplicity rho - 1
  let C : ℂ := pairedEtaXiCompletionFactor rho.1 * rho.1
  have hk : k < analyticZetaZeroMultiplicity rho := by
    dsimp only [k]
    have hm := analyticZetaZeroMultiplicity_positive rho
    omega
  have hwork :=
    summable_oddEndpoint_mul_normSq_pairedEtaLogLaplaceMomentCutoffCenteredFiniteWork_of_lt_multiplicity
      rho hk
  have hshift := summable_oddEndpoint_mul_complexNormSq_nat_add_one hwork
  have hscaled := hshift.mul_left (Complex.normSq C)
  apply hscaled.congr
  intro N
  have hparity : Complex.normSq
      ((-1 : ℂ) ^ analyticZetaZeroMultiplicity rho) = 1 := by
    rw [Complex.normSq_eq_norm_sq, norm_pow, norm_neg, norm_one, one_pow]
    norm_num
  unfold
    pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidualFiniteWorkTopPrefixFiniteConjugateArithmeticIncrement
  simp only [C, k, Complex.normSq_mul, Complex.normSq_conj, hparity]
  ring

/-- The named reflected-partner increments have summable odd-endpoint
weighted squared norms. -/
theorem summable_oddEndpoint_mul_normSq_topPrefixFinitePartnerIncrement
    (rho : NontrivialZetaZero) :
    Summable (fun N : ℕ ↦
      ((2 * N + 1 : ℕ) : ℝ) *
        Complex.normSq
          (pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidualFiniteWorkTopPrefixFinitePartnerIncrement
            rho N)) := by
  simpa only [topPrefixFinitePartnerIncrement_eq_arithmeticIncrement] using
    summable_oddEndpoint_mul_normSq_topPrefixFinitePartnerArithmeticIncrement rho

/-- The named conjugate-original increments have summable odd-endpoint
weighted squared norms. -/
theorem summable_oddEndpoint_mul_normSq_topPrefixFiniteConjugateIncrement
    (rho : NontrivialZetaZero) :
    Summable (fun N : ℕ ↦
      ((2 * N + 1 : ℕ) : ℝ) *
        Complex.normSq
          (pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidualFiniteWorkTopPrefixFiniteConjugateIncrement
            rho N)) := by
  simpa only [topPrefixFiniteConjugateIncrement_eq_arithmeticIncrement] using
    summable_oddEndpoint_mul_normSq_topPrefixFiniteConjugateArithmeticIncrement rho

/-- The first weighted absolute moment of the signed component-increment
energy is finite at every nontrivial zero. -/
theorem summable_oddEndpoint_mul_abs_topPrefixFiniteIncrementEnergyDifference
    (rho : NontrivialZetaZero) :
    Summable (fun N : ℕ ↦
      ((2 * N + 1 : ℕ) : ℝ) *
        |pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidualFiniteWorkTopPrefixFiniteIncrementEnergyDifference
          rho N|) := by
  have hp := summable_oddEndpoint_mul_normSq_topPrefixFinitePartnerIncrement rho
  have hq := summable_oddEndpoint_mul_normSq_topPrefixFiniteConjugateIncrement rho
  apply (hp.add hq).of_nonneg_of_le
  · exact fun N ↦ mul_nonneg (by positivity) (abs_nonneg _)
  · intro N
    have hbound := abs_topPrefixFiniteIncrementEnergyDifference_le rho N
    calc
      ((2 * N + 1 : ℕ) : ℝ) *
          |pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidualFiniteWorkTopPrefixFiniteIncrementEnergyDifference
            rho N| ≤
        ((2 * N + 1 : ℕ) : ℝ) *
          (Complex.normSq
              (pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidualFiniteWorkTopPrefixFinitePartnerIncrement
                rho N) +
            Complex.normSq
              (pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidualFiniteWorkTopPrefixFiniteConjugateIncrement
                rho N)) :=
        mul_le_mul_of_nonneg_left hbound (by positivity)
      _ =
          ((2 * N + 1 : ℕ) : ℝ) *
              Complex.normSq
                (pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidualFiniteWorkTopPrefixFinitePartnerIncrement
                  rho N) +
            ((2 * N + 1 : ℕ) : ℝ) *
              Complex.normSq
                (pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidualFiniteWorkTopPrefixFiniteConjugateIncrement
                  rho N) := by ring

/-- Since the component-increment energy already has a finite first moment,
the successor flux has a finite first moment exactly when the total energy
work does. -/
theorem
    summable_oddEndpoint_mul_abs_topPrefixFiniteEnergyFlux_iff_work
    (rho : NontrivialZetaZero) :
    Summable (fun N : ℕ ↦
      ((2 * N + 1 : ℕ) : ℝ) *
        |pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidualFiniteWorkTopPrefixFiniteEnergyFlux
          rho N|) ↔
      Summable (fun N : ℕ ↦
        ((2 * N + 1 : ℕ) : ℝ) *
          |pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidualFiniteWorkTopPrefixFiniteEnergyWork
            rho N|) := by
  let w : ℕ → ℝ := fun N ↦ ((2 * N + 1 : ℕ) : ℝ)
  let inc : ℕ → ℝ := fun N ↦
    pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidualFiniteWorkTopPrefixFiniteIncrementEnergyDifference
      rho N
  let flux : ℕ → ℝ := fun N ↦
    pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidualFiniteWorkTopPrefixFiniteEnergyFlux
      rho N
  let work : ℕ → ℝ := fun N ↦
    pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidualFiniteWorkTopPrefixFiniteEnergyWork
      rho N
  have hw : ∀ N, 0 ≤ w N := fun N ↦ by dsimp only [w]; positivity
  have habs_iff_signed (f : ℕ → ℝ) :
      Summable (fun N : ℕ ↦ w N * |f N|) ↔
        Summable (fun N : ℕ ↦ w N * f N) := by
    constructor
    · intro habs
      apply Summable.of_norm
      exact habs.congr fun N ↦ by
        rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hw N)]
    · intro hsigned
      have hnorm := summable_norm_iff.mpr hsigned
      exact hnorm.congr fun N ↦ by
        rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hw N)]
  have hincAbs : Summable (fun N : ℕ ↦ w N * |inc N|) := by
    simpa only [w, inc] using
      summable_oddEndpoint_mul_abs_topPrefixFiniteIncrementEnergyDifference rho
  have hinc : Summable (fun N : ℕ ↦ w N * inc N) :=
    (habs_iff_signed inc).1 hincAbs
  have hwork : ∀ N, work N = inc N + flux N := by
    intro N
    simpa only [work, inc, flux] using
      topPrefixFiniteEnergyWork_eq_incrementEnergyDifference_add_flux rho N
  change Summable (fun N : ℕ ↦ w N * |flux N|) ↔
    Summable (fun N : ℕ ↦ w N * |work N|)
  rw [habs_iff_signed flux, habs_iff_signed work]
  constructor
  · intro hflux
    exact (hinc.add hflux).congr fun N ↦ by rw [hwork N]; ring
  · intro hworkSum
    exact (hworkSum.sub hinc).congr fun N ↦ by rw [hwork N]; ring

/-- The critical first moment of the literal successor flux is summable
exactly for zeros on the critical line.  The arithmetic direction remains
open. -/
theorem summable_oddEndpoint_mul_abs_topPrefixFiniteEnergyFlux_iff_re_eq_half
    (rho : NontrivialZetaZero) :
    Summable (fun N : ℕ ↦
      ((2 * N + 1 : ℕ) : ℝ) *
        |pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidualFiniteWorkTopPrefixFiniteEnergyFlux
          rho N|) ↔
      rho.1.re = 1 / 2 := by
  rw [summable_oddEndpoint_mul_abs_topPrefixFiniteEnergyFlux_iff_work,
    summable_oddEndpoint_mul_abs_topPrefixFiniteEnergyWork_iff_re_eq_half]

/-- Universal first-moment summability for the literal successor cross flux
in the finite eta energy transport. -/
def AllPairedEtaCompletedLeadingLogCutoffCenteredPartnerResidualFiniteWorkTopPrefixFiniteEnergyFluxFirstMomentSummable :
    Prop :=
  ∀ rho : NontrivialZetaZero,
    Summable (fun N : ℕ ↦
      ((2 * N + 1 : ℕ) : ℝ) *
        |pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidualFiniteWorkTopPrefixFiniteEnergyFlux
          rho N|)

/-- Universal critical first-moment summability of the explicit successor
flux is equivalent to RH.  The unconditional increment-energy estimate above
shows that this flux, rather than local increment energy, is the entire
remaining obstruction. -/
theorem riemannHypothesis_iff_all_topPrefixFiniteEnergyFlux_firstMoment_summable :
    RiemannHypothesis ↔
      AllPairedEtaCompletedLeadingLogCutoffCenteredPartnerResidualFiniteWorkTopPrefixFiniteEnergyFluxFirstMomentSummable := by
  constructor
  · intro hRH rho
    apply
      (summable_oddEndpoint_mul_abs_topPrefixFiniteEnergyFlux_iff_re_eq_half rho).2
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
      (summable_oddEndpoint_mul_abs_topPrefixFiniteEnergyFlux_iff_re_eq_half
        rho).1 (hsummable rho)

end

end RiemannGaussian
