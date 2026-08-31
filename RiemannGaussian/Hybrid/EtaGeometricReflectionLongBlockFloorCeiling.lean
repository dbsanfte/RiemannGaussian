import RiemannGaussian.Hybrid.EtaGeometricReflectionLongBlockCertificate

/-!
# Long-block ceiling for the pointwise eta reserve floor

The long-block certificate can represent every zero-window coordinate once
the geometric block is large enough.  This module tests whether merely making
that block longer can force the existing explicit reserve floor to cross the
`13/18` or `18/18` threshold.

It cannot.  Lean proves a quantitative mismatch: the transported atom
coercivity is at most a positive coefficient energy times
`M / (2 * q^(M-1))`, whereas the pointwise triangle correlation envelope
retains a positive coefficient-energy floor independent of `M`.  The former
rate tends to zero.  Consequently, uniformly in the block start and over the
complete finite upper zero window, the current coercivity-minus-envelope
lower bound is eventually nonpositive and its nonnegative truncation is
exactly zero.

This is a ceiling for this particular explicit lower-bound method, not for the
actual eta reserve.  It rigorously forces the next frontier upstream: preserve
the signed four-colour aggregate through the window sum instead of applying a
pointwise triangle envelope before aggregation.
-/

open Complex Matrix Finset Filter Topology
open scoped BigOperators Classical ComplexConjugate ComplexOrder Matrix Real

namespace RiemannGaussian

noncomputable section

/-- The squared norm of a critical coordinate tilt is its exact geometric
weight. -/
theorem etaGeometricCriticalCoordinateTilt_norm_sq
    {q M : ℕ} (hq : 0 < q) (j : Fin M) :
    ‖etaGeometricCriticalCoordinateTilt q M j‖ ^ 2 =
      (q : ℝ) ^ (j : ℕ) := by
  unfold etaGeometricCriticalCoordinateTilt
  rw [norm_pow]
  have hbase :
      ‖((q : ℂ) ^ ((1 / 2 : ℝ) : ℂ))‖ ^ 2 = (q : ℝ) := by
    change ‖(((q : ℝ) : ℂ) ^ ((1 / 2 : ℝ) : ℂ))‖ ^ 2 = (q : ℝ)
    rw [Complex.norm_cpow_eq_rpow_re_of_pos (Nat.cast_pos.mpr hq)]
    simp only [Complex.ofReal_re]
    rw [← Real.sqrt_eq_rpow]
    exact Real.sq_sqrt (Nat.cast_nonneg q)
  calc
    (‖((q : ℂ) ^ ((1 / 2 : ℝ) : ℂ))‖ ^ (j : ℕ)) ^ 2 =
        (‖((q : ℂ) ^ ((1 / 2 : ℝ) : ℂ))‖ ^ 2) ^ (j : ℕ) := by
          rw [← pow_mul, ← pow_mul]
          congr 1
          omega
    _ = _ := by rw [hbase]

/-- The final geometric weight is bounded by the full coordinate-tilt
energy. -/
theorem etaGeometricCriticalCoordinateTilt_pow_le_energy
    {q M : ℕ} (hq : 0 < q) (hM : 0 < M) :
    (q : ℝ) ^ (M - 1) ≤ etaGeometricCriticalCoordinateTiltEnergy q M := by
  let j : Fin M := ⟨M - 1, Nat.sub_lt hM (by omega)⟩
  unfold etaGeometricCriticalCoordinateTiltEnergy
    finiteComplexVectorWeightEnergy
  calc
    (q : ℝ) ^ (M - 1) =
        ‖etaGeometricCriticalCoordinateTilt q M j‖ ^ 2 := by
      rw [etaGeometricCriticalCoordinateTilt_norm_sq hq]
    _ ≤ ∑ k, ‖etaGeometricCriticalCoordinateTilt q M k‖ ^ 2 := by
      exact Finset.single_le_sum
        (fun k _hk ↦ sq_nonneg ‖etaGeometricCriticalCoordinateTilt q M k‖)
        (Finset.mem_univ j)

/-- A finite geometric mode in the closed unit disk has squared norm at most
its coordinate count. -/
theorem finiteGeometricModeNormSq_le_card_of_norm_le_one
    (M : ℕ) {z : ℂ} (hz : ‖z‖ ≤ 1) :
    finiteGeometricModeNormSq M z ≤ M := by
  unfold finiteGeometricModeNormSq finiteGeometricPhaseVector
  calc
    ∑ j : Fin M, ‖z ^ (j : ℕ)‖ ^ 2 ≤ ∑ _j : Fin M, (1 : ℝ) := by
      apply Finset.sum_le_sum
      intro j _hj
      rw [norm_pow]
      have hpow : ‖z‖ ^ (j : ℕ) ≤ 1 := pow_le_one₀ (norm_nonneg z) hz
      simpa using
        ((sq_le_sq₀ (pow_nonneg (norm_nonneg z) _) zero_le_one).2 hpow)
    _ = M := by simp

/-- Reciprocal radial coercivity is at most the block dimension on a unit
phase. -/
theorem finiteReciprocalRadialPhaseCoercivity_le_card
    {M : ℕ} (hM : 0 < M) {r : ℝ} (hr : 1 < r)
    (z : ℂ) (hz : ‖z‖ = 1) :
    finiteReciprocalRadialPhaseCoercivity M r z ≤ M := by
  let A := finiteGeometricModeNormSq M ((r : ℂ) * z)
  let B := finiteGeometricModeNormSq M (((r : ℂ)⁻¹) * z)
  have hA : 0 ≤ A := (finiteGeometricModeNormSq_pos hM _).le
  have hB : 0 ≤ B := (finiteGeometricModeNormSq_pos hM _).le
  have hden : 0 < A + B := add_pos
    (finiteGeometricModeNormSq_pos hM _)
    (finiteGeometricModeNormSq_pos hM _)
  have hratio :
      (finiteReciprocalRadialPhaseReserve M r z) / (A + B) ≤ B := by
    apply (div_le_iff₀ hden).2
    unfold finiteReciprocalRadialPhaseReserve
    change A * B - (M : ℝ) ^ 2 ≤ B * (A + B)
    nlinarith [sq_nonneg (M : ℝ), sq_nonneg B]
  have hbaseNorm : ‖((r : ℂ)⁻¹) * z‖ ≤ 1 := by
    rw [norm_mul, norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos
      (zero_lt_one.trans hr), hz, mul_one]
    exact (inv_le_one₀ (zero_lt_one.trans hr)).2 hr.le
  have hBle : B ≤ M := by
    exact finiteGeometricModeNormSq_le_card_of_norm_le_one M hbaseNorm
  exact hratio.trans hBle

/-- The explicit upper-atom coercive floor pays an exponential critical-tilt
denominator and at most a linear dimension numerator. -/
theorem pairedEtaGeometricUpperFrameAtomCoerciveLower_le_card_div_pow
    {q : ℕ} (hq : 1 < q) {T : ℝ}
    (rho : ↑(spectralUpperZetaZeroWindow T)) (n : ℕ)
    {M : ℕ} (hM : 1 < M) :
    pairedEtaGeometricUpperFrameAtomCoerciveLower q rho n M ≤
      (((M : ℝ) / 2) *
          (‖pairedEtaGeometricCompletedPrefixCoefficient q rho.1 n‖ ^ 2 +
            ‖pairedEtaGeometricCompletedPrefixCoefficient q
              (NontrivialZetaZero.conjugatePartner rho.1) n‖ ^ 2)) /
        (q : ℝ) ^ (M - 1) := by
  let C : ℝ :=
    ‖pairedEtaGeometricCompletedPrefixCoefficient q rho.1 n‖ ^ 2 +
      ‖pairedEtaGeometricCompletedPrefixCoefficient q
        (NontrivialZetaZero.conjugatePartner rho.1) n‖ ^ 2
  let κ := finiteReciprocalRadialPhaseCoercivity M
    ‖etaGeometricShiftedMode q (1 / 2) rho.1.val‖
    (etaGeometricNormalizedMode q rho.1.val)
  have hκ : κ ≤ M := by
    exact finiteReciprocalRadialPhaseCoercivity_le_card (by omega)
      (spectralUpperZetaZeroWindow_criticalShiftedMode_radii hq rho).1
      (etaGeometricNormalizedMode q rho.1.val)
      (norm_etaGeometricNormalizedMode hq.le rho.1.val)
  have hκpos : 0 < κ := by
    exact spectralUpperZetaZeroWindow_criticalShiftedReflectionCoercivity_pos
      hq rho hM
  have hC : 0 ≤ C := by
    dsimp only [C]
    positivity
  have hnum : κ / 2 * C ≤ (M : ℝ) / 2 * C := by
    exact mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_right hκ (by norm_num)) hC
  have hpow : 0 < (q : ℝ) ^ (M - 1) := by positivity
  have henergy :
      (q : ℝ) ^ (M - 1) ≤ etaGeometricCriticalCoordinateTiltEnergy q M :=
    etaGeometricCriticalCoordinateTilt_pow_le_energy hq.le (by omega)
  unfold pairedEtaGeometricUpperFrameAtomCoerciveLower
  change (κ / 2 * C) / etaGeometricCriticalCoordinateTiltEnergy q M ≤ _
  exact div_le_div₀ (mul_nonneg (by positivity) hC) hnum hpow henergy

/-- For a fixed zero and block start, the current explicit atom floor tends to
zero with block length. -/
theorem tendsto_pairedEtaGeometricUpperFrameAtomCoerciveLower_atTop
    {q : ℕ} (hq : 1 < q) {T : ℝ}
    (rho : ↑(spectralUpperZetaZeroWindow T)) (n : ℕ) :
    Tendsto (fun M : ℕ ↦
      pairedEtaGeometricUpperFrameAtomCoerciveLower q rho n M)
      atTop (nhds 0) := by
  let C : ℝ :=
    ‖pairedEtaGeometricCompletedPrefixCoefficient q rho.1 n‖ ^ 2 +
      ‖pairedEtaGeometricCompletedPrefixCoefficient q
        (NontrivialZetaZero.conjugatePartner rho.1) n‖ ^ 2
  let g : ℕ → ℝ := fun M ↦
    (((M : ℝ) / 2) * C) / (q : ℝ) ^ (M - 1)
  have hbase : Tendsto (fun M : ℕ ↦ (M : ℝ) / (q : ℝ) ^ M)
      atTop (nhds 0) := by
    simpa only [pow_one] using
      tendsto_pow_const_div_const_pow_of_one_lt 1 (by exact_mod_cast hq)
  have hg : Tendsto g atTop (nhds 0) := by
    have hscaled := hbase.const_mul (((q : ℝ) * C) / 2)
    have hscaled0 : Tendsto
        (fun M : ℕ ↦ ((q : ℝ) * C) / 2 *
          ((M : ℝ) / (q : ℝ) ^ M)) atTop (nhds 0) := by
      simpa using hscaled
    apply hscaled0.congr'
    filter_upwards [eventually_ge_atTop (1 : ℕ)] with M hM
    dsimp only [g]
    have hq0 : (q : ℝ) ≠ 0 := by positivity
    have hpow0 : (q : ℝ) ^ (M - 1) ≠ 0 := pow_ne_zero _ hq0
    have hpowM : (q : ℝ) ^ M =
        (q : ℝ) ^ (M - 1) * q := by
      conv_lhs => rw [show M = (M - 1) + 1 by omega]
      rw [pow_succ]
    rw [hpowM]
    field_simp
  apply squeeze_zero'
  · filter_upwards [eventually_ge_atTop (2 : ℕ)] with M hM
    exact (pairedEtaGeometricUpperFrameAtomCoerciveLower_pos
      hq rho n (by omega)).le
  · filter_upwards [eventually_ge_atTop (2 : ℕ)] with M hM
    exact pairedEtaGeometricUpperFrameAtomCoerciveLower_le_card_div_pow
      hq rho n (by omega)
  · exact hg

/-- The four-colour pointwise triangle correlation envelope is strictly
positive. -/
theorem pairedEtaGeometricUpperReflectionSumCorrelationGapEnvelope_pos
    {q : ℕ} (hq : 1 < q) {T : ℝ}
    (zeta rho : ↑(spectralUpperZetaZeroWindow T))
    (n : ℕ) {ε : ℝ} (hε : 0 < ε) :
    0 < pairedEtaGeometricUpperReflectionSumCorrelationGapEnvelope
      q zeta rho n ε := by
  unfold pairedEtaGeometricUpperReflectionSumCorrelationGapEnvelope
  apply Finset.sum_pos
  · intro i _hi
    apply Finset.sum_pos
    · intro j _hj
      have hzeta :
          pairedEtaGeometricUpperCompletionCoefficientVector q zeta n i ≠ 0 := by
        unfold pairedEtaGeometricUpperCompletionCoefficientVector
        exact pairedEtaGeometricCompletedPrefixCoefficient_ne_zero
          hq.le _ n
      have hrho :
          pairedEtaGeometricUpperCompletionCoefficientVector q rho n j ≠ 0 := by
        unfold pairedEtaGeometricUpperCompletionCoefficientVector
        exact pairedEtaGeometricCompletedPrefixCoefficient_ne_zero
          hq.le _ n
      have hgap := pairedEtaGeometricUpperRawRelativeModeGap_pos
        hq zeta rho i j
      exact mul_pos
        (mul_pos (norm_pos_iff.mpr hzeta) (norm_pos_iff.mpr hrho))
        (div_pos (by linarith) hgap)
    · exact Finset.univ_nonempty
  · exact Finset.univ_nonempty

/-- At fixed start, each pointwise pair floor converges to the negative square
of its fixed correlation envelope. -/
theorem tendsto_pairedEtaGeometricUpperPairReserveGapLower_atTop
    {q : ℕ} (hq : 1 < q) {T : ℝ}
    (zeta rho : ↑(spectralUpperZetaZeroWindow T))
    (n : ℕ) (ε : ℝ) :
    Tendsto (fun M : ℕ ↦
      pairedEtaGeometricUpperPairReserveGapLower q zeta rho n M ε)
      atTop
      (nhds (-pairedEtaGeometricUpperReflectionSumCorrelationGapEnvelope
        q zeta rho n ε ^ 2)) := by
  have hrho :=
    tendsto_pairedEtaGeometricUpperFrameAtomCoerciveLower_atTop hq rho n
  have hzeta :=
    tendsto_pairedEtaGeometricUpperFrameAtomCoerciveLower_atTop hq zeta n
  simpa [pairedEtaGeometricUpperPairReserveGapLower] using
    (hrho.mul hzeta).sub_const
      (pairedEtaGeometricUpperReflectionSumCorrelationGapEnvelope
        q zeta rho n ε ^ 2)

/-- At fixed start, a pointwise pair floor is eventually strictly negative. -/
theorem eventually_pairedEtaGeometricUpperPairReserveGapLower_neg
    {q : ℕ} (hq : 1 < q) {T : ℝ}
    (zeta rho : ↑(spectralUpperZetaZeroWindow T))
    (n : ℕ) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ M in atTop,
      pairedEtaGeometricUpperPairReserveGapLower q zeta rho n M ε < 0 := by
  have hlimit :=
    tendsto_pairedEtaGeometricUpperPairReserveGapLower_atTop hq zeta rho n ε
  have henvelope :=
    pairedEtaGeometricUpperReflectionSumCorrelationGapEnvelope_pos
      hq zeta rho n hε
  exact (tendsto_order.1 hlimit).2 0 (by nlinarith [sq_pos_of_pos henvelope])

/-- At fixed start, the complete weighted upper-window floor is eventually
nonpositive. -/
theorem eventually_pairedEtaGeometricUpperWindowWeightedReserveGapLower_nonpos
    {q : ℕ} (hq : 1 < q) (T : ℝ) (n : ℕ)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ M in atTop,
      pairedEtaGeometricUpperWindowWeightedReserveGapLower
        q T n M ε ≤ 0 := by
  have hpairs : ∀ᶠ M in atTop,
      ∀ rho zeta : ↑(spectralUpperZetaZeroWindow T),
        pairedEtaGeometricUpperPairWeightedReserveGapLower
          q zeta rho n M ε ≤ 0 := by
    apply Filter.eventually_all.mpr
    intro rho
    apply Filter.eventually_all.mpr
    intro zeta
    have hpair := eventually_pairedEtaGeometricUpperPairReserveGapLower_neg
      hq zeta rho n hε
    filter_upwards [hpair] with M hpairM
    unfold pairedEtaGeometricUpperPairWeightedReserveGapLower
    exact mul_nonpos_of_nonneg_of_nonpos
      (mul_nonneg
        (pairedEtaReflectionEvenFrameWeight_pos T (Sum.inr rho)).le
        (pairedEtaReflectionEvenFrameWeight_pos T (Sum.inr zeta)).le)
      hpairM.le
  filter_upwards [hpairs] with M hpairsM
  unfold pairedEtaGeometricUpperWindowWeightedReserveGapLower
  apply Finset.sum_nonpos
  intro rho _hrho
  apply Finset.sum_nonpos
  intro zeta _hzeta
  exact hpairsM rho zeta

/-- At fixed start, the nonnegative truncation of the upper-window floor is
eventually zero. -/
theorem eventually_pairedEtaGeometricUpperWindowNonnegativeReserveGapLower_eq_zero
    {q : ℕ} (hq : 1 < q) (T : ℝ) (n : ℕ)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ M in atTop,
      pairedEtaGeometricUpperWindowNonnegativeReserveGapLower
        q T n M ε = 0 := by
  have hlower :=
    eventually_pairedEtaGeometricUpperWindowWeightedReserveGapLower_nonpos
      hq T n hε
  filter_upwards [hlower] with M hM
  unfold pairedEtaGeometricUpperWindowNonnegativeReserveGapLower
  exact max_eq_left hM

/-- Total of the four positive raw-mode gaps for one ordered upper pair. -/
def pairedEtaGeometricUpperRawRelativeModeGapTotal
    (q : ℕ) {T : ℝ}
    (zeta rho : ↑(spectralUpperZetaZeroWindow T)) : ℝ :=
  ∑ i : Fin 2, ∑ j : Fin 2,
    pairedEtaGeometricUpperRawRelativeModeGap q zeta rho i j

/-- The total of the four raw-mode gaps is strictly positive. -/
theorem pairedEtaGeometricUpperRawRelativeModeGapTotal_pos
    {q : ℕ} (hq : 1 < q) {T : ℝ}
    (zeta rho : ↑(spectralUpperZetaZeroWindow T)) :
    0 < pairedEtaGeometricUpperRawRelativeModeGapTotal q zeta rho := by
  unfold pairedEtaGeometricUpperRawRelativeModeGapTotal
  exact Finset.sum_pos
    (fun i _hi ↦ Finset.sum_pos
      (fun j _hj ↦ pairedEtaGeometricUpperRawRelativeModeGap_pos
        hq zeta rho i j)
      Finset.univ_nonempty)
    Finset.univ_nonempty

/-- Each raw-mode gap is bounded by their common positive total. -/
theorem pairedEtaGeometricUpperRawRelativeModeGap_le_total
    (q : ℕ) {T : ℝ}
    (zeta rho : ↑(spectralUpperZetaZeroWindow T)) (i j : Fin 2) :
    pairedEtaGeometricUpperRawRelativeModeGap q zeta rho i j ≤
      pairedEtaGeometricUpperRawRelativeModeGapTotal q zeta rho := by
  unfold pairedEtaGeometricUpperRawRelativeModeGapTotal
  have hinner :
      pairedEtaGeometricUpperRawRelativeModeGap q zeta rho i j ≤
        ∑ k : Fin 2,
          pairedEtaGeometricUpperRawRelativeModeGap q zeta rho i k := by
    exact Finset.single_le_sum
      (s := Finset.univ)
      (f := fun k : Fin 2 ↦
        pairedEtaGeometricUpperRawRelativeModeGap q zeta rho i k)
      (fun k _hk ↦ by
        unfold pairedEtaGeometricUpperRawRelativeModeGap
        positivity)
      (Finset.mem_univ j)
  have houter :
      (∑ k : Fin 2,
          pairedEtaGeometricUpperRawRelativeModeGap q zeta rho i k) ≤
        ∑ l : Fin 2, ∑ k : Fin 2,
          pairedEtaGeometricUpperRawRelativeModeGap q zeta rho l k := by
    exact Finset.single_le_sum
      (s := Finset.univ)
      (f := fun l : Fin 2 ↦ ∑ k : Fin 2,
        pairedEtaGeometricUpperRawRelativeModeGap q zeta rho l k)
      (fun l _hl ↦ Finset.sum_nonneg fun k _hk ↦ by
        unfold pairedEtaGeometricUpperRawRelativeModeGap
        positivity)
      (Finset.mem_univ i)
  exact hinner.trans houter

/-- Positive coefficient left after replacing every reciprocal raw gap by
the reciprocal of their common finite total. -/
def pairedEtaGeometricUpperGapEnvelopeUniformCoefficient
    (q : ℕ) {T : ℝ}
    (zeta rho : ↑(spectralUpperZetaZeroWindow T)) (ε : ℝ) : ℝ :=
  (2 + ε) / pairedEtaGeometricUpperRawRelativeModeGapTotal q zeta rho

/-- The uniform reciprocal-gap coefficient is strictly positive. -/
theorem pairedEtaGeometricUpperGapEnvelopeUniformCoefficient_pos
    {q : ℕ} (hq : 1 < q) {T : ℝ}
    (zeta rho : ↑(spectralUpperZetaZeroWindow T))
    {ε : ℝ} (hε : 0 < ε) :
    0 < pairedEtaGeometricUpperGapEnvelopeUniformCoefficient
      q zeta rho ε := by
  exact div_pos (by linarith)
    (pairedEtaGeometricUpperRawRelativeModeGapTotal_pos hq zeta rho)

/-- The sum of the two coefficient norms dominates their Euclidean energy
after squaring. -/
theorem sum_sq_norm_pairedEtaGeometricUpperCompletionCoefficientVector_le
    (q : ℕ) {T : ℝ}
    (rho : ↑(spectralUpperZetaZeroWindow T)) (n : ℕ) :
    (∑ i : Fin 2,
        ‖pairedEtaGeometricUpperCompletionCoefficientVector q rho n i‖ ^ 2) ≤
      (∑ i : Fin 2,
        ‖pairedEtaGeometricUpperCompletionCoefficientVector q rho n i‖) ^ 2 := by
  rw [Fin.sum_univ_two, Fin.sum_univ_two]
  nlinarith [mul_nonneg
    (norm_nonneg (pairedEtaGeometricUpperCompletionCoefficientVector q rho n 0))
    (norm_nonneg (pairedEtaGeometricUpperCompletionCoefficientVector q rho n 1))]

/-- The pointwise triangle envelope dominates a product of the two coefficient
norm sums with an explicit positive coefficient independent of block length
and start. -/
theorem pairedEtaGeometricUpperReflectionSumCorrelationGapEnvelope_lower
    {q : ℕ} (hq : 1 < q) {T : ℝ}
    (zeta rho : ↑(spectralUpperZetaZeroWindow T))
    (n : ℕ) {ε : ℝ} (hε : 0 < ε) :
    pairedEtaGeometricUpperGapEnvelopeUniformCoefficient q zeta rho ε *
        (∑ i : Fin 2,
          ‖pairedEtaGeometricUpperCompletionCoefficientVector q zeta n i‖) *
        (∑ j : Fin 2,
          ‖pairedEtaGeometricUpperCompletionCoefficientVector q rho n j‖) ≤
      pairedEtaGeometricUpperReflectionSumCorrelationGapEnvelope
        q zeta rho n ε := by
  let a := pairedEtaGeometricUpperGapEnvelopeUniformCoefficient
    q zeta rho ε
  have ha : 0 ≤ a :=
    (pairedEtaGeometricUpperGapEnvelopeUniformCoefficient_pos
      hq zeta rho hε).le
  have hentry : ∀ i j : Fin 2,
      a ≤ (2 + ε) /
        pairedEtaGeometricUpperRawRelativeModeGap q zeta rho i j := by
    intro i j
    unfold a pairedEtaGeometricUpperGapEnvelopeUniformCoefficient
    exact div_le_div_of_nonneg_left (by linarith)
      (pairedEtaGeometricUpperRawRelativeModeGap_pos hq zeta rho i j)
      (pairedEtaGeometricUpperRawRelativeModeGap_le_total
        q zeta rho i j)
  unfold pairedEtaGeometricUpperReflectionSumCorrelationGapEnvelope
  calc
    a * (∑ i : Fin 2,
          ‖pairedEtaGeometricUpperCompletionCoefficientVector q zeta n i‖) *
        (∑ j : Fin 2,
          ‖pairedEtaGeometricUpperCompletionCoefficientVector q rho n j‖) =
      ∑ i : Fin 2, ∑ j : Fin 2,
          ‖pairedEtaGeometricUpperCompletionCoefficientVector q zeta n i‖ *
          ‖pairedEtaGeometricUpperCompletionCoefficientVector q rho n j‖ * a := by
      simp only [Fin.sum_univ_two]
      ring
    _ ≤ _ := by
      apply Finset.sum_le_sum
      intro i _hi
      apply Finset.sum_le_sum
      intro j _hj
      exact mul_le_mul_of_nonneg_left (hentry i j)
        (mul_nonneg (norm_nonneg _) (norm_nonneg _))

/-- Euclidean energy of the two exact moving completion coefficients. -/
def pairedEtaGeometricUpperCompletionCoefficientEnergy
    (q : ℕ) {T : ℝ}
    (rho : ↑(spectralUpperZetaZeroWindow T)) (n : ℕ) : ℝ :=
  ∑ i : Fin 2,
    ‖pairedEtaGeometricUpperCompletionCoefficientVector q rho n i‖ ^ 2

/-- Every two-colour completion coefficient energy is strictly positive. -/
theorem pairedEtaGeometricUpperCompletionCoefficientEnergy_pos
    {q : ℕ} (hq : 0 < q) {T : ℝ}
    (rho : ↑(spectralUpperZetaZeroWindow T)) (n : ℕ) :
    0 < pairedEtaGeometricUpperCompletionCoefficientEnergy q rho n := by
  unfold pairedEtaGeometricUpperCompletionCoefficientEnergy
  apply Finset.sum_pos
  · intro i _hi
    exact sq_pos_of_pos (norm_pos_iff.mpr (by
      unfold pairedEtaGeometricUpperCompletionCoefficientVector
      exact pairedEtaGeometricCompletedPrefixCoefficient_ne_zero hq _ n))
  · exact Finset.univ_nonempty

/-- The vector energy is exactly the sum of the original and reflected
completion-coefficient energies. -/
theorem pairedEtaGeometricUpperCompletionCoefficientEnergy_eq
    (q : ℕ) {T : ℝ}
    (rho : ↑(spectralUpperZetaZeroWindow T)) (n : ℕ) :
    pairedEtaGeometricUpperCompletionCoefficientEnergy q rho n =
      ‖pairedEtaGeometricCompletedPrefixCoefficient q rho.1 n‖ ^ 2 +
        ‖pairedEtaGeometricCompletedPrefixCoefficient q
          (NontrivialZetaZero.conjugatePartner rho.1) n‖ ^ 2 := by
  unfold pairedEtaGeometricUpperCompletionCoefficientEnergy
    pairedEtaGeometricUpperCompletionCoefficientVector
    pairedEtaGeometricUpperReflectionPairZero
  rw [Fin.sum_univ_two]
  simp [add_comm]

/-- The squared triangle envelope uniformly dominates the product of both
coefficient energies times the squared reciprocal-gap coefficient. -/
theorem pairedEtaGeometricUpperGapEnvelopeUniformCoefficient_sq_mul_energy_le
    {q : ℕ} (hq : 1 < q) {T : ℝ}
    (zeta rho : ↑(spectralUpperZetaZeroWindow T))
    (n : ℕ) {ε : ℝ} (hε : 0 < ε) :
    pairedEtaGeometricUpperGapEnvelopeUniformCoefficient q zeta rho ε ^ 2 *
        pairedEtaGeometricUpperCompletionCoefficientEnergy q zeta n *
        pairedEtaGeometricUpperCompletionCoefficientEnergy q rho n ≤
      pairedEtaGeometricUpperReflectionSumCorrelationGapEnvelope
        q zeta rho n ε ^ 2 := by
  let a := pairedEtaGeometricUpperGapEnvelopeUniformCoefficient
    q zeta rho ε
  let Sz := ∑ i : Fin 2,
    ‖pairedEtaGeometricUpperCompletionCoefficientVector q zeta n i‖
  let Sr := ∑ i : Fin 2,
    ‖pairedEtaGeometricUpperCompletionCoefficientVector q rho n i‖
  let Ez := pairedEtaGeometricUpperCompletionCoefficientEnergy q zeta n
  let Er := pairedEtaGeometricUpperCompletionCoefficientEnergy q rho n
  let E := pairedEtaGeometricUpperReflectionSumCorrelationGapEnvelope
    q zeta rho n ε
  have ha : 0 ≤ a :=
    (pairedEtaGeometricUpperGapEnvelopeUniformCoefficient_pos
      hq zeta rho hε).le
  have hSz : 0 ≤ Sz := Finset.sum_nonneg fun i _hi ↦ norm_nonneg _
  have hSr : 0 ≤ Sr := Finset.sum_nonneg fun i _hi ↦ norm_nonneg _
  have hEz : 0 ≤ Ez := by
    exact (pairedEtaGeometricUpperCompletionCoefficientEnergy_pos
      hq.le zeta n).le
  have hEr : 0 ≤ Er := by
    exact (pairedEtaGeometricUpperCompletionCoefficientEnergy_pos
      hq.le rho n).le
  have hEzSq : Ez ≤ Sz ^ 2 := by
    exact sum_sq_norm_pairedEtaGeometricUpperCompletionCoefficientVector_le
      q zeta n
  have hErSq : Er ≤ Sr ^ 2 := by
    exact sum_sq_norm_pairedEtaGeometricUpperCompletionCoefficientVector_le
      q rho n
  have hprod : Ez * Er ≤ Sz ^ 2 * Sr ^ 2 :=
    mul_le_mul hEzSq hErSq hEr (sq_nonneg Sz)
  have hscaled : a ^ 2 * (Ez * Er) ≤
      a ^ 2 * (Sz ^ 2 * Sr ^ 2) :=
    mul_le_mul_of_nonneg_left hprod (sq_nonneg a)
  have hlower : a * Sz * Sr ≤ E := by
    exact pairedEtaGeometricUpperReflectionSumCorrelationGapEnvelope_lower
      hq zeta rho n hε
  have hE : 0 ≤ E :=
    (pairedEtaGeometricUpperReflectionSumCorrelationGapEnvelope_pos
      hq zeta rho n hε).le
  have hsquare : (a * Sz * Sr) ^ 2 ≤ E ^ 2 :=
    (sq_le_sq₀ (mul_nonneg (mul_nonneg ha hSz) hSr) hE).2 hlower
  change a ^ 2 * Ez * Er ≤ E ^ 2
  calc
    a ^ 2 * Ez * Er = a ^ 2 * (Ez * Er) := by ring
    _ ≤ a ^ 2 * (Sz ^ 2 * Sr ^ 2) := hscaled
    _ = (a * Sz * Sr) ^ 2 := by ring
    _ ≤ E ^ 2 := hsquare

/-- Dimension-over-critical-tilt rate paid by the current pointwise atom
coercivity lower bound. -/
def pairedEtaGeometricLongBlockCoerciveRate (q M : ℕ) : ℝ :=
  (M : ℝ) / (2 * (q : ℝ) ^ (M - 1))

/-- The atom floor is bounded by the long-block decay rate times its exact
two-colour coefficient energy. -/
theorem pairedEtaGeometricUpperFrameAtomCoerciveLower_le_rate_mul_energy
    {q : ℕ} (hq : 1 < q) {T : ℝ}
    (rho : ↑(spectralUpperZetaZeroWindow T)) (n : ℕ)
    {M : ℕ} (hM : 1 < M) :
    pairedEtaGeometricUpperFrameAtomCoerciveLower q rho n M ≤
      pairedEtaGeometricLongBlockCoerciveRate q M *
        pairedEtaGeometricUpperCompletionCoefficientEnergy q rho n := by
  rw [pairedEtaGeometricUpperCompletionCoefficientEnergy_eq]
  have h :=
    pairedEtaGeometricUpperFrameAtomCoerciveLower_le_card_div_pow
      hq rho n hM
  unfold pairedEtaGeometricLongBlockCoerciveRate
  convert h using 1
  ring

/-- The dimension-over-critical-tilt rate tends to zero exponentially. -/
theorem tendsto_pairedEtaGeometricLongBlockCoerciveRate_atTop
    {q : ℕ} (hq : 1 < q) :
    Tendsto (fun M : ℕ ↦ pairedEtaGeometricLongBlockCoerciveRate q M)
      atTop (nhds 0) := by
  have hbase : Tendsto (fun M : ℕ ↦ (M : ℝ) / (q : ℝ) ^ M)
      atTop (nhds 0) := by
    simpa only [pow_one] using
      tendsto_pow_const_div_const_pow_of_one_lt 1 (by exact_mod_cast hq)
  have hscaled := hbase.const_mul ((q : ℝ) / 2)
  have hscaled0 : Tendsto
      (fun M : ℕ ↦ (q : ℝ) / 2 * ((M : ℝ) / (q : ℝ) ^ M))
      atTop (nhds 0) := by
    simpa using hscaled
  apply hscaled0.congr'
  filter_upwards [eventually_ge_atTop (1 : ℕ)] with M hM
  unfold pairedEtaGeometricLongBlockCoerciveRate
  have hq0 : (q : ℝ) ≠ 0 := by positivity
  have hpowM : (q : ℝ) ^ M =
      (q : ℝ) ^ (M - 1) * q := by
    conv_lhs => rw [show M = (M - 1) + 1 by omega]
    rw [pow_succ]
  rw [hpowM]
  field_simp

/-- Uniformly in the block start, the present pointwise
coercivity-minus-triangle-envelope lower bound for one upper pair eventually
becomes strictly negative as the block length grows. -/
theorem eventually_forall_pairedEtaGeometricUpperPairReserveGapLower_neg
    {q : ℕ} (hq : 1 < q) {T : ℝ}
    (zeta rho : ↑(spectralUpperZetaZeroWindow T))
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ M in atTop, ∀ n : ℕ,
      pairedEtaGeometricUpperPairReserveGapLower
        q zeta rho n M ε < 0 := by
  let a := pairedEtaGeometricUpperGapEnvelopeUniformCoefficient
    q zeta rho ε
  have ha : 0 < a :=
    pairedEtaGeometricUpperGapEnvelopeUniformCoefficient_pos
      hq zeta rho hε
  have hrate := tendsto_pairedEtaGeometricLongBlockCoerciveRate_atTop hq
  have hrateLt : ∀ᶠ M in atTop,
      pairedEtaGeometricLongBlockCoerciveRate q M < a :=
    (tendsto_order.1 hrate).2 a ha
  filter_upwards [hrateLt, eventually_ge_atTop (2 : ℕ)] with M hrateM hM n
  let R := pairedEtaGeometricLongBlockCoerciveRate q M
  let Ez := pairedEtaGeometricUpperCompletionCoefficientEnergy q zeta n
  let Er := pairedEtaGeometricUpperCompletionCoefficientEnergy q rho n
  let Lz := pairedEtaGeometricUpperFrameAtomCoerciveLower q zeta n M
  let Lr := pairedEtaGeometricUpperFrameAtomCoerciveLower q rho n M
  let E := pairedEtaGeometricUpperReflectionSumCorrelationGapEnvelope
    q zeta rho n ε
  have hR : 0 ≤ R := by
    unfold R pairedEtaGeometricLongBlockCoerciveRate
    positivity
  have hEz : 0 < Ez :=
    pairedEtaGeometricUpperCompletionCoefficientEnergy_pos hq.le zeta n
  have hEr : 0 < Er :=
    pairedEtaGeometricUpperCompletionCoefficientEnergy_pos hq.le rho n
  have hLzPos : 0 < Lz :=
    pairedEtaGeometricUpperFrameAtomCoerciveLower_pos hq zeta n hM
  have hLrPos : 0 < Lr :=
    pairedEtaGeometricUpperFrameAtomCoerciveLower_pos hq rho n hM
  have hLz : Lz ≤ R * Ez :=
    pairedEtaGeometricUpperFrameAtomCoerciveLower_le_rate_mul_energy
      hq zeta n hM
  have hLr : Lr ≤ R * Er :=
    pairedEtaGeometricUpperFrameAtomCoerciveLower_le_rate_mul_energy
      hq rho n hM
  have hproduct : Lr * Lz ≤ R ^ 2 * (Ez * Er) := by
    calc
      Lr * Lz ≤ (R * Er) * (R * Ez) :=
        mul_le_mul hLr hLz hLzPos.le (mul_nonneg hR hEr.le)
      _ = R ^ 2 * (Ez * Er) := by ring
  have hRsq : R ^ 2 < a ^ 2 :=
    (sq_lt_sq₀ hR ha.le).2 hrateM
  have hstrict : R ^ 2 * (Ez * Er) < a ^ 2 * (Ez * Er) :=
    mul_lt_mul_of_pos_right hRsq (mul_pos hEz hEr)
  have henvelope : a ^ 2 * Ez * Er ≤ E ^ 2 :=
    pairedEtaGeometricUpperGapEnvelopeUniformCoefficient_sq_mul_energy_le
      hq zeta rho n hε
  have hgap : Lr * Lz < E ^ 2 := by
    calc
      Lr * Lz ≤ R ^ 2 * (Ez * Er) := hproduct
      _ < a ^ 2 * (Ez * Er) := hstrict
      _ = a ^ 2 * Ez * Er := by ring
      _ ≤ E ^ 2 := henvelope
  unfold pairedEtaGeometricUpperPairReserveGapLower
  exact sub_neg.mpr hgap

/-- The collapse is simultaneous over the complete finite upper zero window
and uniform in the block start. -/
theorem eventually_forall_pairedEtaGeometricUpperWindowWeightedReserveGapLower_nonpos
    {q : ℕ} (hq : 1 < q) (T : ℝ) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ M in atTop, ∀ n : ℕ,
      pairedEtaGeometricUpperWindowWeightedReserveGapLower
        q T n M ε ≤ 0 := by
  have hpairs : ∀ᶠ M in atTop,
      ∀ rho zeta : ↑(spectralUpperZetaZeroWindow T), ∀ n : ℕ,
        pairedEtaGeometricUpperPairWeightedReserveGapLower
          q zeta rho n M ε ≤ 0 := by
    apply Filter.eventually_all.mpr
    intro rho
    apply Filter.eventually_all.mpr
    intro zeta
    have hpair :=
      eventually_forall_pairedEtaGeometricUpperPairReserveGapLower_neg
        hq zeta rho hε
    filter_upwards [hpair] with M hpairM n
    unfold pairedEtaGeometricUpperPairWeightedReserveGapLower
    exact mul_nonpos_of_nonneg_of_nonpos
      (mul_nonneg
        (pairedEtaReflectionEvenFrameWeight_pos T (Sum.inr rho)).le
        (pairedEtaReflectionEvenFrameWeight_pos T (Sum.inr zeta)).le)
      (hpairM n).le
  filter_upwards [hpairs] with M hpairsM n
  unfold pairedEtaGeometricUpperWindowWeightedReserveGapLower
  apply Finset.sum_nonpos
  intro rho _hrho
  apply Finset.sum_nonpos
  intro zeta _hzeta
  exact hpairsM rho zeta n

/-- Consequently, regardless of the block start, the nonnegative truncation
of the current explicit pointwise floor is identically zero at all sufficiently
large block lengths.  Any successful long-block certificate must preserve
more signed aggregate information than this triangle-envelope reduction. -/
theorem eventually_forall_pairedEtaGeometricUpperWindowNonnegativeReserveGapLower_eq_zero
    {q : ℕ} (hq : 1 < q) (T : ℝ) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ M in atTop, ∀ n : ℕ,
      pairedEtaGeometricUpperWindowNonnegativeReserveGapLower
        q T n M ε = 0 := by
  have hlower :=
    eventually_forall_pairedEtaGeometricUpperWindowWeightedReserveGapLower_nonpos
      hq T hε
  filter_upwards [hlower] with M hM n
  unfold pairedEtaGeometricUpperWindowNonnegativeReserveGapLower
  exact max_eq_left (hM n)

end

end RiemannGaussian
