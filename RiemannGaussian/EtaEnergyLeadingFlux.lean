import RiemannGaussian.RiemannXiSuzukiPositiveCriticalStripEtaLeadingLogMomentFiniteCenteredResidualFiniteWorkTopPrefixFiniteEnergyFluxGram

/-!
# Leading-current isolation for the finite eta energy flux

The exact finite-work expansion contains one term with only one logarithmic
cutoff-shift factor. This module separates that leading term from the new-head
and strict lower-hierarchy remainder. At multiplicity one the new head is the
leading term; at larger multiplicity the leading term is the unique top
lower-order prefix with shift degree one.

Every remainder term has shift degree at least two. Lean combines that extra
degree with the two endpoint-decay factors in its successor pairing to prove
that the remainder flux has an unconditionally summable critical first
absolute moment. Thus the full hard flux has a finite first moment exactly
when its single leading current does. Pointwise at a zero this is equivalent
to the critical-line equation, and universally it is equivalent to RH.

These are exact reductions and unconditional remainder estimates, not an
estimate of the remaining leading current.
-/

open Complex Filter MeasureTheory Metric Set Topology
open scoped Classical ComplexConjugate ENNReal Interval Topology

namespace RiemannGaussian

noncomputable section

/-- The unique slow term in the order-`k` finite work. At order zero it is the negative new head; at successor order it is the top transported lower prefix, carrying exactly one cutoff-shift factor. -/
def pairedEtaLogLaplaceMomentCutoffCenteredFiniteWorkLeading : ℕ → ℂ → ℕ → ℂ
  | 0, s, N => -pairedEtaLogLaplaceMomentCutoffCenteredHead 0 s N
  | k + 1, s, N =>
      ((((k + 1).choose k : ℕ) : ℂ) *
        (pairedEtaLogTailShiftIncrement N : ℂ) ^ ((k + 1) - k) *
        pairedEtaLogLaplaceMomentCutoffCenteredPartialSum k s (N + 1))

/-- At multiplicity order zero, the unique leading finite work is the
negative newly exposed head. -/
theorem pairedEtaLogLaplaceMomentCutoffCenteredFiniteWorkLeading_zero
    (s : ℂ) (N : ℕ) :
    pairedEtaLogLaplaceMomentCutoffCenteredFiniteWorkLeading 0 s N =
      -pairedEtaLogLaplaceMomentCutoffCenteredHead 0 s N := rfl

/-- At successor order, the unique leading finite work is explicitly the
degree-one transport of the immediately lower centered prefix. -/
theorem pairedEtaLogLaplaceMomentCutoffCenteredFiniteWorkLeading_succ
    (k : ℕ) (s : ℂ) (N : ℕ) :
    pairedEtaLogLaplaceMomentCutoffCenteredFiniteWorkLeading (k + 1) s N =
      ((k + 1 : ℕ) : ℂ) * (pairedEtaLogTailShiftIncrement N : ℂ) *
        pairedEtaLogLaplaceMomentCutoffCenteredPartialSum k s (N + 1) := by
  simp [pairedEtaLogLaplaceMomentCutoffCenteredFiniteWorkLeading]

/-- The finite-work remainder after removing its unique slow term. It vanishes at order zero and otherwise consists of the negative head plus the strict lower transported hierarchy. -/
def pairedEtaLogLaplaceMomentCutoffCenteredFiniteWorkRemainder : ℕ → ℂ → ℕ → ℂ
  | 0, _, _ => 0
  | k + 1, s, N =>
      -pairedEtaLogLaplaceMomentCutoffCenteredHead (k + 1) s N +
        ∑ j ∈ Finset.range k,
          ((((k + 1).choose j : ℕ) : ℂ) *
            (pairedEtaLogTailShiftIncrement N : ℂ) ^ ((k + 1) - j) *
            pairedEtaLogLaplaceMomentCutoffCenteredPartialSum j s (N + 1))

/-- Exact decomposition of finite work into its leading and remainder pieces. -/
theorem pairedEtaLogLaplaceMomentCutoffCenteredFiniteWork_eq_leading_add_remainder (k : ℕ) (s : ℂ) (N : ℕ) :
    pairedEtaLogLaplaceMomentCutoffCenteredFiniteWork k s N =
      pairedEtaLogLaplaceMomentCutoffCenteredFiniteWorkLeading k s N + pairedEtaLogLaplaceMomentCutoffCenteredFiniteWorkRemainder k s N := by
  cases k with
  | zero =>
      simp [pairedEtaLogLaplaceMomentCutoffCenteredFiniteWork,
        pairedEtaLogLaplaceMomentCutoffCenteredFiniteWorkLeading, pairedEtaLogLaplaceMomentCutoffCenteredFiniteWorkRemainder]
  | succ k =>
      unfold pairedEtaLogLaplaceMomentCutoffCenteredFiniteWork
      rw [Finset.sum_range_succ]
      simp only [pairedEtaLogLaplaceMomentCutoffCenteredFiniteWorkLeading, pairedEtaLogLaplaceMomentCutoffCenteredFiniteWorkRemainder]
      ring

/-- A shift degree of at least two makes the odd-endpoint weighted product of two positive endpoint decays summable. -/
theorem summable_oddEndpoint_mul_doubleEndpointDecay_mul_shiftIncrement_pow {sigma : ℝ} (hsigma : 0 < sigma)
    {d : ℕ} (hd : 2 ≤ d) :
    Summable (fun N : ℕ ↦
      ((2 * N + 1 : ℕ) : ℝ) *
        (((((2 * N + 1 : ℕ) : ℝ) ^ (-sigma)) *
          pairedEtaLogTailShiftIncrement N ^ d) *
          (((2 * N + 1 : ℕ) : ℝ) ^ (-sigma)))) := by
  have htwoSigma : 0 < 2 * sigma := by linarith
  have hdegree : 0 < d - 1 := by omega
  have hbase :=
    summable_oddEndpoint_rpow_neg_mul_pairedEtaLogTailShiftIncrement_pow
      htwoSigma hdegree
  have hmajor : Summable (fun N : ℕ ↦
      (3 : ℝ) *
        (((2 * N + 1 : ℕ) : ℝ) ^ (-(2 * sigma)) *
          pairedEtaLogTailShiftIncrement N ^ (d - 1))) :=
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
  have hrpow : x ^ (-sigma) * x ^ (-sigma) =
      x ^ (-(2 * sigma)) := by
    rw [← Real.rpow_add hx]
    congr 1
    ring
  have hdeltaPow : delta ^ d = delta * delta ^ (d - 1) := by
    calc
      delta ^ d = delta ^ (d - 1 + 1) := by
        rw [Nat.sub_add_cancel (by omega : 1 ≤ d)]
      _ = delta ^ (d - 1) * delta := by rw [pow_succ]
      _ = delta * delta ^ (d - 1) := mul_comm _ _
  have hidentity :
      x * ((x ^ (-sigma) * delta ^ d) * x ^ (-sigma)) =
        (x * delta) *
          (x ^ (-(2 * sigma)) * delta ^ (d - 1)) := by
    rw [hdeltaPow, ← hrpow]
    ring
  change ‖x * ((x ^ (-sigma) * delta ^ d) * x ^ (-sigma))‖ ≤
    3 * (x ^ (-(2 * sigma)) * delta ^ (d - 1))
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity), hidentity]
  exact mul_le_mul_of_nonneg_right hN.le (by positivity)

/-- Below the zero multiplicity, a successor centered finite prefix is bounded by its factorial constant times the current odd-endpoint decay. -/
theorem norm_pairedEtaLogLaplaceMomentCutoffCenteredPartialSum_le_oddEndpoint_rpow
    (rho : NontrivialZetaZero) {j : ℕ}
    (hj : j < analyticZetaZeroMultiplicity rho) (N : ℕ) :
    ‖pairedEtaLogLaplaceMomentCutoffCenteredPartialSum j rho.1 (N + 1)‖ ≤
      ((j.factorial : ℝ) / rho.1.re ^ (j + 1)) *
        (((2 * N + 1 : ℕ) : ℝ) ^ (-rho.1.re)) := by
  have h :=
    norm_pairedEtaLogTailShiftIncrement_pow_mul_cutoffCenteredPartialSum_le
      rho (d := 0) hj N
  simpa using h

/-- A positive-order cutoff head paired with any successor finite prefix below the zero multiplicity has summable odd-endpoint weighted norm product. -/
theorem summable_oddEndpoint_mul_norm_head_mul_norm_cutoffCenteredPartialSum_of_one_le
    (rho : NontrivialZetaZero) {k j : ℕ}
    (hk : 1 ≤ k) (hj : j < analyticZetaZeroMultiplicity rho) :
    Summable (fun N : ℕ ↦
      ((2 * N + 1 : ℕ) : ℝ) *
        ‖pairedEtaLogLaplaceMomentCutoffCenteredHead k rho.1 N‖ *
        ‖pairedEtaLogLaplaceMomentCutoffCenteredPartialSum j rho.1 (N + 1)‖) := by
  let C : ℝ := (j.factorial : ℝ) / rho.1.re ^ (j + 1)
  have hsigma : 0 < rho.1.re := NontrivialZetaZero.zero_lt_re rho
  have hC : 0 ≤ C := by
    dsimp only [C]
    exact div_nonneg (by positivity) (pow_nonneg hsigma.le _)
  have hmodel := summable_oddEndpoint_mul_doubleEndpointDecay_mul_shiftIncrement_pow (NontrivialZetaZero.zero_lt_re rho)
    (show 2 ≤ k + 1 by omega)
  have hmajor := hmodel.mul_left C
  apply hmajor.of_nonneg_of_le
  · exact fun N ↦ mul_nonneg
      (mul_nonneg (by positivity) (norm_nonneg _)) (norm_nonneg _)
  · intro N
    have hhead := norm_pairedEtaLogLaplaceMomentCutoffCenteredHead_le
      k (NontrivialZetaZero.zero_lt_re rho) N
    have hpartial := norm_pairedEtaLogLaplaceMomentCutoffCenteredPartialSum_le_oddEndpoint_rpow rho hj N
    calc
      ((2 * N + 1 : ℕ) : ℝ) *
          ‖pairedEtaLogLaplaceMomentCutoffCenteredHead k rho.1 N‖ *
          ‖pairedEtaLogLaplaceMomentCutoffCenteredPartialSum j rho.1 (N + 1)‖ ≤
        ((2 * N + 1 : ℕ) : ℝ) *
          (((2 * N + 1 : ℕ) : ℝ) ^ (-rho.1.re) *
            pairedEtaLogTailShiftIncrement N ^ (k + 1)) *
          (C * (((2 * N + 1 : ℕ) : ℝ) ^ (-rho.1.re))) :=
        mul_le_mul
          (mul_le_mul_of_nonneg_left hhead (by positivity)) hpartial
          (norm_nonneg _)
          (mul_nonneg (by positivity)
            (mul_nonneg (Real.rpow_nonneg (by positivity) _)
              (pow_nonneg (pairedEtaLogTailShiftIncrement_pos N).le _)))
      _ = C * (((2 * N + 1 : ℕ) : ℝ) *
          (((((2 * N + 1 : ℕ) : ℝ) ^ (-rho.1.re)) *
            pairedEtaLogTailShiftIncrement N ^ (k + 1)) *
            (((2 * N + 1 : ℕ) : ℝ) ^ (-rho.1.re)))) := by ring

/-- A transported prefix with shift degree at least two paired with a successor prefix has summable odd-endpoint weighted norm product. -/
theorem summable_oddEndpoint_mul_norm_shiftIncrement_pow_partialSum_mul_norm_partialSum
    (rho : NontrivialZetaZero) {j k d : ℕ}
    (hj : j < analyticZetaZeroMultiplicity rho)
    (hk : k < analyticZetaZeroMultiplicity rho) (hd : 2 ≤ d) :
    Summable (fun N : ℕ ↦
      ((2 * N + 1 : ℕ) : ℝ) *
        ‖(pairedEtaLogTailShiftIncrement N : ℂ) ^ d *
          pairedEtaLogLaplaceMomentCutoffCenteredPartialSum j rho.1 (N + 1)‖ *
        ‖pairedEtaLogLaplaceMomentCutoffCenteredPartialSum k rho.1 (N + 1)‖) := by
  let Cj : ℝ := (j.factorial : ℝ) / rho.1.re ^ (j + 1)
  let Ck : ℝ := (k.factorial : ℝ) / rho.1.re ^ (k + 1)
  have hsigma : 0 < rho.1.re := NontrivialZetaZero.zero_lt_re rho
  have hCj : 0 ≤ Cj := by
    dsimp only [Cj]
    exact div_nonneg (by positivity) (pow_nonneg hsigma.le _)
  have hCk : 0 ≤ Ck := by
    dsimp only [Ck]
    exact div_nonneg (by positivity) (pow_nonneg hsigma.le _)
  have hmodel := summable_oddEndpoint_mul_doubleEndpointDecay_mul_shiftIncrement_pow (NontrivialZetaZero.zero_lt_re rho) hd
  have hmajor := hmodel.mul_left (Cj * Ck)
  apply hmajor.of_nonneg_of_le
  · exact fun N ↦ mul_nonneg
      (mul_nonneg (by positivity) (norm_nonneg _)) (norm_nonneg _)
  · intro N
    have hlower :=
      norm_pairedEtaLogTailShiftIncrement_pow_mul_cutoffCenteredPartialSum_le
        rho (d := d) hj N
    have hpartial := norm_pairedEtaLogLaplaceMomentCutoffCenteredPartialSum_le_oddEndpoint_rpow rho hk N
    calc
      ((2 * N + 1 : ℕ) : ℝ) *
          ‖(pairedEtaLogTailShiftIncrement N : ℂ) ^ d *
            pairedEtaLogLaplaceMomentCutoffCenteredPartialSum j rho.1 (N + 1)‖ *
          ‖pairedEtaLogLaplaceMomentCutoffCenteredPartialSum k rho.1 (N + 1)‖ ≤
        ((2 * N + 1 : ℕ) : ℝ) *
          (Cj * ((((2 * N + 1 : ℕ) : ℝ) ^ (-rho.1.re)) *
            pairedEtaLogTailShiftIncrement N ^ d)) *
          (Ck * (((2 * N + 1 : ℕ) : ℝ) ^ (-rho.1.re))) :=
        mul_le_mul
          (mul_le_mul_of_nonneg_left hlower (by positivity)) hpartial
          (norm_nonneg _)
          (mul_nonneg (by positivity)
            (mul_nonneg hCj
              (mul_nonneg (Real.rpow_nonneg (by positivity) _)
                (pow_nonneg (pairedEtaLogTailShiftIncrement_pos N).le _))))
      _ = (Cj * Ck) * (((2 * N + 1 : ℕ) : ℝ) *
          (((((2 * N + 1 : ℕ) : ℝ) ^ (-rho.1.re)) *
            pairedEtaLogTailShiftIncrement N ^ d) *
            (((2 * N + 1 : ℕ) : ℝ) ^ (-rho.1.re)))) := by ring

/-- Weighted norm-product summability is stable under addition in the first complex sequence. -/
theorem summable_weight_mul_norm_add_mul_norm
    {w : ℕ → ℝ} (hw : ∀ N, 0 ≤ w N) {f g h : ℕ → ℂ}
    (hf : Summable (fun N : ℕ ↦ w N * ‖f N‖ * ‖h N‖))
    (hg : Summable (fun N : ℕ ↦ w N * ‖g N‖ * ‖h N‖)) :
    Summable (fun N : ℕ ↦ w N * ‖f N + g N‖ * ‖h N‖) := by
  apply (hf.add hg).of_nonneg_of_le
  · exact fun N ↦ mul_nonneg
      (mul_nonneg (hw N) (norm_nonneg _)) (norm_nonneg _)
  · intro N
    calc
      w N * ‖f N + g N‖ * ‖h N‖ ≤
          w N * (‖f N‖ + ‖g N‖) * ‖h N‖ := by
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left (norm_add_le (f N) (g N)) (hw N))
          (norm_nonneg _)
      _ = w N * ‖f N‖ * ‖h N‖ + w N * ‖g N‖ * ‖h N‖ := by
        ring

/-- Weighted norm-product summability is stable under a fixed finite sum in the first complex sequence. -/
theorem summable_weight_mul_norm_finset_sum_mul_norm
    {ι : Type*} [DecidableEq ι] {w : ℕ → ℝ} (hw : ∀ N, 0 ≤ w N)
    (s : Finset ι) (f : ι → ℕ → ℂ) (h : ℕ → ℂ)
    (hf : ∀ i ∈ s,
      Summable (fun N : ℕ ↦ w N * ‖f i N‖ * ‖h N‖)) :
    Summable (fun N : ℕ ↦ w N * ‖∑ i ∈ s, f i N‖ * ‖h N‖) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
      have haSum := hf a (Finset.mem_insert_self a s)
      have hsSum := ih (fun i hi ↦ hf i (Finset.mem_insert_of_mem hi))
      have hsum := summable_weight_mul_norm_add_mul_norm hw haSum hsSum
      simpa only [Finset.sum_insert ha] using hsum

/-- The finite-work remainder paired with its same-order successor prefix has an unconditionally summable critical weighted norm product. -/
theorem summable_oddEndpoint_mul_norm_finiteWorkRemainder_mul_norm_successorPartialSum
    (rho : NontrivialZetaZero) {k : ℕ}
    (hk : k < analyticZetaZeroMultiplicity rho) :
    Summable (fun N : ℕ ↦
      ((2 * N + 1 : ℕ) : ℝ) * ‖pairedEtaLogLaplaceMomentCutoffCenteredFiniteWorkRemainder k rho.1 N‖ *
        ‖pairedEtaLogLaplaceMomentCutoffCenteredPartialSum k rho.1 (N + 1)‖) := by
  cases k with
  | zero => simp [pairedEtaLogLaplaceMomentCutoffCenteredFiniteWorkRemainder]
  | succ k =>
      let w : ℕ → ℝ := fun N ↦ ((2 * N + 1 : ℕ) : ℝ)
      let top : ℕ → ℂ := fun N ↦
        pairedEtaLogLaplaceMomentCutoffCenteredPartialSum (k + 1) rho.1 (N + 1)
      have hw : ∀ N, 0 ≤ w N := fun N ↦ by dsimp only [w]; positivity
      have hheadRaw := summable_oddEndpoint_mul_norm_head_mul_norm_cutoffCenteredPartialSum_of_one_le rho (k := k + 1) (j := k + 1)
        (by omega) hk
      have hhead : Summable (fun N : ℕ ↦
          w N * ‖-pairedEtaLogLaplaceMomentCutoffCenteredHead (k + 1) rho.1 N‖ *
            ‖top N‖) := by
        simpa only [w, top, norm_neg] using hheadRaw
      have hlower : Summable (fun N : ℕ ↦
          w N *
            ‖∑ j ∈ Finset.range k,
              (((((k + 1).choose j : ℕ) : ℂ) *
                (pairedEtaLogTailShiftIncrement N : ℂ) ^ (k + 1 - j) *
                pairedEtaLogLaplaceMomentCutoffCenteredPartialSum j rho.1
                  (N + 1)))‖ *
            ‖top N‖) := by
        apply summable_weight_mul_norm_finset_sum_mul_norm hw
        intro j hj
        have hjk : j < k := Finset.mem_range.mp hj
        have hjm : j < analyticZetaZeroMultiplicity rho := by omega
        have hd : 2 ≤ k + 1 - j := by omega
        have hbase := summable_oddEndpoint_mul_norm_shiftIncrement_pow_partialSum_mul_norm_partialSum rho (j := j) (k := k + 1)
          (d := k + 1 - j) hjm hk hd
        have hscaled := hbase.mul_left
          ‖((((k + 1).choose j : ℕ) : ℂ))‖
        apply hscaled.congr
        intro N
        simp only [w, top, norm_mul]
        ring
      have hsum := summable_weight_mul_norm_add_mul_norm hw hhead hlower
      simpa only [w, top, pairedEtaLogLaplaceMomentCutoffCenteredFiniteWorkRemainder] using hsum

/-- Forward shifting both complex sequences preserves odd-endpoint weighted norm-product summability. -/
theorem summable_oddEndpoint_mul_norm_mul_norm_nat_add_one {f g : ℕ → ℂ}
    (hf : Summable (fun N : ℕ ↦
      ((2 * N + 1 : ℕ) : ℝ) * ‖f N‖ * ‖g N‖)) :
    Summable (fun N : ℕ ↦
      ((2 * N + 1 : ℕ) : ℝ) * ‖f (N + 1)‖ * ‖g (N + 1)‖) := by
  have hlarge := (summable_nat_add_iff 1).2 hf
  apply hlarge.of_nonneg_of_le
  · exact fun N ↦ mul_nonneg
      (mul_nonneg (by positivity) (norm_nonneg _)) (norm_nonneg _)
  · intro N
    apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
    apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
    norm_num

/-- Completion-weighted leading arithmetic increment for the reflected-partner component. -/
def pairedEtaTopPrefixFinitePartnerLeadingArithmeticIncrement
    (rho : NontrivialZetaZero) (N : ℕ) : ℂ :=
  (pairedEtaXiCompletionFactor
      (NontrivialZetaZero.conjugatePartner rho).1 *
    (NontrivialZetaZero.conjugatePartner rho).1) *
      pairedEtaLogLaplaceMomentCutoffCenteredFiniteWorkLeading (analyticZetaZeroMultiplicity rho - 1)
        (NontrivialZetaZero.conjugatePartner rho).1 (N + 1)

/-- Completion-weighted arithmetic remainder increment for the reflected-partner component. -/
def pairedEtaTopPrefixFinitePartnerRemainderArithmeticIncrement
    (rho : NontrivialZetaZero) (N : ℕ) : ℂ :=
  (pairedEtaXiCompletionFactor
      (NontrivialZetaZero.conjugatePartner rho).1 *
    (NontrivialZetaZero.conjugatePartner rho).1) *
      pairedEtaLogLaplaceMomentCutoffCenteredFiniteWorkRemainder (analyticZetaZeroMultiplicity rho - 1)
        (NontrivialZetaZero.conjugatePartner rho).1 (N + 1)

/-- Parity-adjusted conjugate-original leading arithmetic increment. -/
def pairedEtaTopPrefixFiniteConjugateLeadingArithmeticIncrement
    (rho : NontrivialZetaZero) (N : ℕ) : ℂ :=
  (-1 : ℂ) ^ analyticZetaZeroMultiplicity rho *
    starRingEnd ℂ
      ((pairedEtaXiCompletionFactor rho.1 * rho.1) *
        pairedEtaLogLaplaceMomentCutoffCenteredFiniteWorkLeading (analyticZetaZeroMultiplicity rho - 1) rho.1 (N + 1))

/-- Parity-adjusted conjugate-original arithmetic remainder increment. -/
def pairedEtaTopPrefixFiniteConjugateRemainderArithmeticIncrement
    (rho : NontrivialZetaZero) (N : ℕ) : ℂ :=
  (-1 : ℂ) ^ analyticZetaZeroMultiplicity rho *
    starRingEnd ℂ
      ((pairedEtaXiCompletionFactor rho.1 * rho.1) *
        pairedEtaLogLaplaceMomentCutoffCenteredFiniteWorkRemainder (analyticZetaZeroMultiplicity rho - 1) rho.1 (N + 1))

/-- The reflected-partner arithmetic increment is exactly its leading increment plus its remainder. -/
theorem topPrefixFinitePartnerArithmeticIncrement_eq_leading_add_remainder (rho : NontrivialZetaZero) (N : ℕ) :
    pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidualFiniteWorkTopPrefixFinitePartnerArithmeticIncrement
        rho N =
      pairedEtaTopPrefixFinitePartnerLeadingArithmeticIncrement rho N + pairedEtaTopPrefixFinitePartnerRemainderArithmeticIncrement rho N := by
  unfold
    pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidualFiniteWorkTopPrefixFinitePartnerArithmeticIncrement
    pairedEtaTopPrefixFinitePartnerLeadingArithmeticIncrement pairedEtaTopPrefixFinitePartnerRemainderArithmeticIncrement
  rw [pairedEtaLogLaplaceMomentCutoffCenteredFiniteWork_eq_leading_add_remainder]
  ring

/-- The conjugate-original arithmetic increment is exactly its leading increment plus its remainder. -/
theorem topPrefixFiniteConjugateArithmeticIncrement_eq_leading_add_remainder (rho : NontrivialZetaZero) (N : ℕ) :
    pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidualFiniteWorkTopPrefixFiniteConjugateArithmeticIncrement
        rho N =
      pairedEtaTopPrefixFiniteConjugateLeadingArithmeticIncrement rho N + pairedEtaTopPrefixFiniteConjugateRemainderArithmeticIncrement rho N := by
  unfold
    pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidualFiniteWorkTopPrefixFiniteConjugateArithmeticIncrement
    pairedEtaTopPrefixFiniteConjugateLeadingArithmeticIncrement pairedEtaTopPrefixFiniteConjugateRemainderArithmeticIncrement
  rw [pairedEtaLogLaplaceMomentCutoffCenteredFiniteWork_eq_leading_add_remainder, mul_add, map_add]
  ring

/-- Signed successor energy flux formed only from the two leading arithmetic increments. -/
def pairedEtaTopPrefixFiniteEnergyLeadingFlux (rho : NontrivialZetaZero) (N : ℕ) : ℝ :=
  2 *
    ((pairedEtaTopPrefixFinitePartnerLeadingArithmeticIncrement rho N *
        starRingEnd ℂ
          (pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidualFiniteWorkTopPrefixFinitePartnerTerm
            rho (N + 1))).re -
      (pairedEtaTopPrefixFiniteConjugateLeadingArithmeticIncrement rho N *
        starRingEnd ℂ
          (pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidualFiniteWorkTopPrefixFiniteConjugateTerm
            rho (N + 1))).re)

/-- Signed successor energy flux formed from the two arithmetic remainder increments. -/
def pairedEtaTopPrefixFiniteEnergyRemainderFlux (rho : NontrivialZetaZero) (N : ℕ) : ℝ :=
  2 *
    ((pairedEtaTopPrefixFinitePartnerRemainderArithmeticIncrement rho N *
        starRingEnd ℂ
          (pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidualFiniteWorkTopPrefixFinitePartnerTerm
            rho (N + 1))).re -
      (pairedEtaTopPrefixFiniteConjugateRemainderArithmeticIncrement rho N *
        starRingEnd ℂ
          (pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidualFiniteWorkTopPrefixFiniteConjugateTerm
            rho (N + 1))).re)

/-- The full successor energy flux is exactly the leading flux plus the remainder flux. -/
theorem topPrefixFiniteEnergyFlux_eq_leading_add_remainder (rho : NontrivialZetaZero) (N : ℕ) :
    pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidualFiniteWorkTopPrefixFiniteEnergyFlux
        rho N = pairedEtaTopPrefixFiniteEnergyLeadingFlux rho N + pairedEtaTopPrefixFiniteEnergyRemainderFlux rho N := by
  unfold
    pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidualFiniteWorkTopPrefixFiniteEnergyFlux
    pairedEtaTopPrefixFiniteEnergyLeadingFlux pairedEtaTopPrefixFiniteEnergyRemainderFlux
  rw [topPrefixFinitePartnerIncrement_eq_arithmeticIncrement,
    topPrefixFiniteConjugateIncrement_eq_arithmeticIncrement,
    topPrefixFinitePartnerArithmeticIncrement_eq_leading_add_remainder, topPrefixFiniteConjugateArithmeticIncrement_eq_leading_add_remainder]
  simp only [add_mul, Complex.add_re]
  ring

/-- The completed reflected-partner remainder increment paired with its successor term has a finite critical first moment. -/
theorem summable_oddEndpoint_mul_norm_topPrefixFinitePartnerRemainderIncrement_mul_successorTerm (rho : NontrivialZetaZero) :
    Summable (fun N : ℕ ↦
      ((2 * N + 1 : ℕ) : ℝ) *
        ‖pairedEtaTopPrefixFinitePartnerRemainderArithmeticIncrement rho N‖ *
        ‖pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidualFiniteWorkTopPrefixFinitePartnerTerm
          rho (N + 1)‖) := by
  let partner := NontrivialZetaZero.conjugatePartner rho
  let k := analyticZetaZeroMultiplicity rho - 1
  let C : ℂ := pairedEtaXiCompletionFactor partner.1 * partner.1
  have hk : k < analyticZetaZeroMultiplicity partner := by
    dsimp only [k, partner]
    rw [analyticZetaZeroMultiplicity_conjugatePartner]
    have hm := analyticZetaZeroMultiplicity_positive rho
    omega
  have hraw := summable_oddEndpoint_mul_norm_finiteWorkRemainder_mul_norm_successorPartialSum partner hk
  have hshift := summable_oddEndpoint_mul_norm_mul_norm_nat_add_one (f := fun N ↦ pairedEtaLogLaplaceMomentCutoffCenteredFiniteWorkRemainder k partner.1 N)
    (g := fun N ↦
      pairedEtaLogLaplaceMomentCutoffCenteredPartialSum k partner.1 (N + 1))
    hraw
  have hscaled := hshift.mul_left (‖C‖ ^ 2)
  apply hscaled.congr
  intro N
  unfold pairedEtaTopPrefixFinitePartnerRemainderArithmeticIncrement
    pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidualFiniteWorkTopPrefixFinitePartnerTerm
  simp only [C, partner, k, norm_mul]
  ring

/-- The completed conjugate-original remainder increment paired with its successor term has a finite critical first moment. -/
theorem summable_oddEndpoint_mul_norm_topPrefixFiniteConjugateRemainderIncrement_mul_successorTerm (rho : NontrivialZetaZero) :
    Summable (fun N : ℕ ↦
      ((2 * N + 1 : ℕ) : ℝ) *
        ‖pairedEtaTopPrefixFiniteConjugateRemainderArithmeticIncrement rho N‖ *
        ‖pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidualFiniteWorkTopPrefixFiniteConjugateTerm
          rho (N + 1)‖) := by
  let k := analyticZetaZeroMultiplicity rho - 1
  let C : ℂ := pairedEtaXiCompletionFactor rho.1 * rho.1
  have hk : k < analyticZetaZeroMultiplicity rho := by
    dsimp only [k]
    have hm := analyticZetaZeroMultiplicity_positive rho
    omega
  have hraw := summable_oddEndpoint_mul_norm_finiteWorkRemainder_mul_norm_successorPartialSum rho hk
  have hshift := summable_oddEndpoint_mul_norm_mul_norm_nat_add_one (f := fun N ↦ pairedEtaLogLaplaceMomentCutoffCenteredFiniteWorkRemainder k rho.1 N)
    (g := fun N ↦
      pairedEtaLogLaplaceMomentCutoffCenteredPartialSum k rho.1 (N + 1))
    hraw
  have hscaled := hshift.mul_left (‖C‖ ^ 2)
  apply hscaled.congr
  intro N
  unfold pairedEtaTopPrefixFiniteConjugateRemainderArithmeticIncrement
    pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidualFiniteWorkTopPrefixFiniteConjugateTerm
  simp only [C, k, norm_mul, norm_pow, norm_neg, norm_one, one_pow,
    one_mul, norm_conj]
  ring

/-- The absolute remainder flux is bounded by its two component norm products. -/
theorem abs_topPrefixFiniteEnergyRemainderFlux_le (rho : NontrivialZetaZero) (N : ℕ) :
    |pairedEtaTopPrefixFiniteEnergyRemainderFlux rho N| ≤
      2 *
        (‖pairedEtaTopPrefixFinitePartnerRemainderArithmeticIncrement rho N‖ *
            ‖pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidualFiniteWorkTopPrefixFinitePartnerTerm
              rho (N + 1)‖ +
          ‖pairedEtaTopPrefixFiniteConjugateRemainderArithmeticIncrement rho N‖ *
            ‖pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidualFiniteWorkTopPrefixFiniteConjugateTerm
              rho (N + 1)‖) := by
  let p : ℝ :=
    (pairedEtaTopPrefixFinitePartnerRemainderArithmeticIncrement rho N *
      starRingEnd ℂ
        (pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidualFiniteWorkTopPrefixFinitePartnerTerm
          rho (N + 1))).re
  let q : ℝ :=
    (pairedEtaTopPrefixFiniteConjugateRemainderArithmeticIncrement rho N *
      starRingEnd ℂ
        (pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidualFiniteWorkTopPrefixFiniteConjugateTerm
          rho (N + 1))).re
  have hp : |p| ≤
      ‖pairedEtaTopPrefixFinitePartnerRemainderArithmeticIncrement rho N‖ *
        ‖pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidualFiniteWorkTopPrefixFinitePartnerTerm
          rho (N + 1)‖ := by
    calc
      |p| ≤ ‖pairedEtaTopPrefixFinitePartnerRemainderArithmeticIncrement rho N *
          starRingEnd ℂ
            (pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidualFiniteWorkTopPrefixFinitePartnerTerm
              rho (N + 1))‖ := Complex.abs_re_le_norm _
      _ = _ := by rw [norm_mul, norm_conj]
  have hq : |q| ≤
      ‖pairedEtaTopPrefixFiniteConjugateRemainderArithmeticIncrement rho N‖ *
        ‖pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidualFiniteWorkTopPrefixFiniteConjugateTerm
          rho (N + 1)‖ := by
    calc
      |q| ≤ ‖pairedEtaTopPrefixFiniteConjugateRemainderArithmeticIncrement rho N *
          starRingEnd ℂ
            (pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidualFiniteWorkTopPrefixFiniteConjugateTerm
              rho (N + 1))‖ := Complex.abs_re_le_norm _
      _ = _ := by rw [norm_mul, norm_conj]
  have hpq : |p - q| ≤ |p| + |q| := by
    simpa only [sub_eq_add_neg, abs_neg] using abs_add_le p (-q)
  unfold pairedEtaTopPrefixFiniteEnergyRemainderFlux
  change |2 * (p - q)| ≤ _
  rw [abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
  exact mul_le_mul_of_nonneg_left (hpq.trans (add_le_add hp hq)) (by norm_num)

/-- The arithmetic remainder flux has an unconditionally summable critical first absolute moment. -/
theorem summable_oddEndpoint_mul_abs_topPrefixFiniteEnergyRemainderFlux (rho : NontrivialZetaZero) :
    Summable (fun N : ℕ ↦
      ((2 * N + 1 : ℕ) : ℝ) * |pairedEtaTopPrefixFiniteEnergyRemainderFlux rho N|) := by
  have hp := summable_oddEndpoint_mul_norm_topPrefixFinitePartnerRemainderIncrement_mul_successorTerm rho
  have hq := summable_oddEndpoint_mul_norm_topPrefixFiniteConjugateRemainderIncrement_mul_successorTerm rho
  have hmajor := (hp.add hq).mul_left 2
  apply hmajor.of_nonneg_of_le
  · exact fun N ↦ mul_nonneg (by positivity) (abs_nonneg _)
  · intro N
    have hbound := abs_topPrefixFiniteEnergyRemainderFlux_le rho N
    calc
      ((2 * N + 1 : ℕ) : ℝ) * |pairedEtaTopPrefixFiniteEnergyRemainderFlux rho N| ≤
          ((2 * N + 1 : ℕ) : ℝ) *
            (2 *
              (‖pairedEtaTopPrefixFinitePartnerRemainderArithmeticIncrement rho N‖ *
                  ‖pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidualFiniteWorkTopPrefixFinitePartnerTerm
                    rho (N + 1)‖ +
                ‖pairedEtaTopPrefixFiniteConjugateRemainderArithmeticIncrement rho N‖ *
                  ‖pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidualFiniteWorkTopPrefixFiniteConjugateTerm
                    rho (N + 1)‖)) :=
        mul_le_mul_of_nonneg_left hbound (by positivity)
      _ = 2 *
          (((2 * N + 1 : ℕ) : ℝ) *
              ‖pairedEtaTopPrefixFinitePartnerRemainderArithmeticIncrement rho N‖ *
              ‖pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidualFiniteWorkTopPrefixFinitePartnerTerm
                rho (N + 1)‖ +
            ((2 * N + 1 : ℕ) : ℝ) *
              ‖pairedEtaTopPrefixFiniteConjugateRemainderArithmeticIncrement rho N‖ *
              ‖pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidualFiniteWorkTopPrefixFiniteConjugateTerm
                rho (N + 1)‖) := by ring

/-- Critical first-moment summability of the leading flux is equivalent to that of the full flux because the remainder flux is unconditionally summable. -/
theorem summable_oddEndpoint_mul_abs_topPrefixFiniteEnergyLeadingFlux_iff_flux (rho : NontrivialZetaZero) :
    Summable (fun N : ℕ ↦
      ((2 * N + 1 : ℕ) : ℝ) * |pairedEtaTopPrefixFiniteEnergyLeadingFlux rho N|) ↔
    Summable (fun N : ℕ ↦
      ((2 * N + 1 : ℕ) : ℝ) *
        |pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidualFiniteWorkTopPrefixFiniteEnergyFlux
          rho N|) := by
  let w : ℕ → ℝ := fun N ↦ ((2 * N + 1 : ℕ) : ℝ)
  let leading : ℕ → ℝ := fun N ↦ pairedEtaTopPrefixFiniteEnergyLeadingFlux rho N
  let remainder : ℕ → ℝ := fun N ↦ pairedEtaTopPrefixFiniteEnergyRemainderFlux rho N
  let flux : ℕ → ℝ := fun N ↦
    pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidualFiniteWorkTopPrefixFiniteEnergyFlux
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
  have hremainderAbs : Summable (fun N : ℕ ↦ w N * |remainder N|) := by
    simpa only [w, remainder] using summable_oddEndpoint_mul_abs_topPrefixFiniteEnergyRemainderFlux rho
  have hremainder : Summable (fun N : ℕ ↦ w N * remainder N) :=
    (habs_iff_signed remainder).1 hremainderAbs
  have hflux : ∀ N, flux N = leading N + remainder N := by
    intro N
    simpa only [flux, leading, remainder] using topPrefixFiniteEnergyFlux_eq_leading_add_remainder rho N
  change Summable (fun N : ℕ ↦ w N * |leading N|) ↔
    Summable (fun N : ℕ ↦ w N * |flux N|)
  rw [habs_iff_signed leading, habs_iff_signed flux]
  constructor
  · intro hleading
    exact (hleading.add hremainder).congr fun N ↦ by rw [hflux N]; ring
  · intro hfull
    exact (hfull.sub hremainder).congr fun N ↦ by rw [hflux N]; ring

/-- The single leading-current flux has a finite critical first absolute moment exactly when the zero lies on the critical line. -/
theorem summable_oddEndpoint_mul_abs_topPrefixFiniteEnergyLeadingFlux_iff_re_eq_half (rho : NontrivialZetaZero) :
    Summable (fun N : ℕ ↦
      ((2 * N + 1 : ℕ) : ℝ) * |pairedEtaTopPrefixFiniteEnergyLeadingFlux rho N|) ↔
      rho.1.re = 1 / 2 := by
  rw [summable_oddEndpoint_mul_abs_topPrefixFiniteEnergyLeadingFlux_iff_flux,
    summable_oddEndpoint_mul_abs_topPrefixFiniteEnergyFlux_iff_re_eq_half]

/-- Universal critical first-moment summability of the isolated leading finite-eta energy flux. -/
def AllPairedEtaTopPrefixFiniteEnergyLeadingFluxFirstMomentSummable : Prop :=
  ∀ rho : NontrivialZetaZero,
    Summable (fun N : ℕ ↦
      ((2 * N + 1 : ℕ) : ℝ) * |pairedEtaTopPrefixFiniteEnergyLeadingFlux rho N|)

/-- RH is equivalent to universal critical first-moment summability of the isolated leading finite-eta energy flux. -/
theorem riemannHypothesis_iff_all_topPrefixFiniteEnergyLeadingFlux_firstMoment_summable :
    RiemannHypothesis ↔ AllPairedEtaTopPrefixFiniteEnergyLeadingFluxFirstMomentSummable := by
  constructor
  · intro hRH rho
    apply (summable_oddEndpoint_mul_abs_topPrefixFiniteEnergyLeadingFlux_iff_re_eq_half rho).2
    have him : (zetaSpectralCoordinate rho.1).im = 0 :=
      (riemannHypothesis_iff_spectralCoordinate_real.mp hRH)
        rho.1 rho.2.1 rho.2.2.1 rho.2.2.2
    exact (zetaSpectralCoordinate_im_eq_zero_iff rho.1).1 him
  · intro hsummable
    rw [riemannHypothesis_iff_spectralCoordinate_real]
    intro s hs hnontrivial hone
    let rho : NontrivialZetaZero := ⟨s, hs, hnontrivial, hone⟩
    apply (zetaSpectralCoordinate_im_eq_zero_iff s).2
    exact (summable_oddEndpoint_mul_abs_topPrefixFiniteEnergyLeadingFlux_iff_re_eq_half rho).1 (hsummable rho)

end

end RiemannGaussian
