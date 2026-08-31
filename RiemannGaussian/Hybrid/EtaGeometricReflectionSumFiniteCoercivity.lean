import RiemannGaussian.Hybrid.EtaGeometricReflectionSumCompletionTransport

/-!
# Uniform finite-prefix coercivity for completed eta reflection sums

The limiting reciprocal-radius modes have a strictly positive
determinant-over-trace coercivity constant, but the actual certificate uses
finite normalized eta-prefix columns and coefficients that move with the
cutoff.  Pointwise convergence for fixed coefficients is therefore
insufficient.  This module proves the coefficient-uniform perturbation needed
to close that gap.

First, it develops the exact signed quadratic ledger and determinant-over-
trace lower bound for any two finite complex vectors.  The literal two-column
eta Gram coefficient then converges to the checked positive reciprocal-mode
constant.  Consequently, every sufficiently late prefix pair obeys one common
half-limit lower bound simultaneously for all complex coefficients.

Because that statement is uniform in the coefficients, Lean can substitute
the actual nonzero, cutoff-dependent completion coefficients from the previous
module.  The complex channel recovered from every sufficiently late actual
upper frame atom therefore satisfies an explicit positive norm lower bound and
cannot collapse.  Cross-atom correlation control and certificate aggregation
remain open.
-/

open Complex Matrix Finset Filter Topology
open scoped BigOperators Classical ComplexConjugate ComplexOrder Matrix Real

namespace RiemannGaussian

noncomputable section

/-- Determinant-over-trace coercivity coefficient of two finite complex
vectors. -/
def finiteComplexVectorGramCoercivity
    {m : Type*} [Fintype m] (f b : m → ℂ) : ℝ :=
  (finiteComplexVectorNormSq f * finiteComplexVectorNormSq b -
      ‖star b ⬝ᵥ f‖ ^ 2) /
    (finiteComplexVectorNormSq f + finiteComplexVectorNormSq b)

/-- Exact signed norm-square ledger for an arbitrary complex combination of
two finite vectors. -/
theorem finiteComplexVectorCombination_normSq_eq
    {m : Type*} [Fintype m] (f b : m → ℂ) (c d : ℂ) :
    finiteComplexVectorNormSq (c • f + d • b) =
      ‖c‖ ^ 2 * finiteComplexVectorNormSq f +
        ‖d‖ ^ 2 * finiteComplexVectorNormSq b +
        2 * (star d * c * (star b ⬝ᵥ f)).re := by
  have hselfF := star_dot_self_eq_finiteComplexVectorNormSq f
  have hselfB := star_dot_self_eq_finiteComplexVectorNormSq b
  have hswap :
      star f ⬝ᵥ b = starRingEnd ℂ (star b ⬝ᵥ f) := by
    have h := Matrix.star_dotProduct b f
    have h' := congrArg (starRingEnd ℂ) h
    simpa using h'.symm
  have hstar :
      star (c • f + d • b) =
        star c • star f + star d • star b := by
    ext j
    simp [Pi.star_apply]
  have hdot :
      star (c • f + d • b) ⬝ᵥ (c • f + d • b) =
        star c * c * (finiteComplexVectorNormSq f : ℂ) +
          star d * d * (finiteComplexVectorNormSq b : ℂ) +
          star c * d * starRingEnd ℂ (star b ⬝ᵥ f) +
          star d * c * (star b ⬝ᵥ f) := by
    rw [hstar]
    simp only [add_dotProduct, dotProduct_add, smul_dotProduct,
      dotProduct_smul, hselfF, hselfB, hswap, smul_eq_mul]
    ring
  have hcc : star c * c = (‖c‖ ^ 2 : ℂ) := by
    simpa [Complex.star_def] using Complex.conj_mul' c
  have hdd : star d * d = (‖d‖ ^ 2 : ℂ) := by
    simpa [Complex.star_def] using Complex.conj_mul' d
  have hcross :
      star c * d * starRingEnd ℂ (star b ⬝ᵥ f) +
          star d * c * (star b ⬝ᵥ f) =
        (2 * (star d * c * (star b ⬝ᵥ f)).re : ℝ) := by
    apply Complex.ext
    · simp [Complex.mul_re]
      ring
    · simp [Complex.mul_im]
      ring
  have hcast :
      (finiteComplexVectorNormSq (c • f + d • b) : ℂ) =
        (‖c‖ ^ 2 * finiteComplexVectorNormSq f +
          ‖d‖ ^ 2 * finiteComplexVectorNormSq b +
          2 * (star d * c * (star b ⬝ᵥ f)).re : ℝ) := by
    rw [← star_dot_self_eq_finiteComplexVectorNormSq, hdot,
      hcc, hdd]
    calc
      (‖c‖ ^ 2 : ℂ) * (finiteComplexVectorNormSq f : ℂ) +
            (‖d‖ ^ 2 : ℂ) * (finiteComplexVectorNormSq b : ℂ) +
            star c * d * starRingEnd ℂ (star b ⬝ᵥ f) +
            star d * c * (star b ⬝ᵥ f) =
          (‖c‖ ^ 2 : ℂ) * (finiteComplexVectorNormSq f : ℂ) +
            (‖d‖ ^ 2 : ℂ) * (finiteComplexVectorNormSq b : ℂ) +
            (star c * d * starRingEnd ℂ (star b ⬝ᵥ f) +
              star d * c * (star b ⬝ᵥ f)) := by ring
      _ = _ := by
        rw [hcross]
        push_cast
        ring
  exact_mod_cast hcast

/-- Every two-vector complex combination is bounded below by its Gram
determinant-over-trace coefficient times the coefficient norm square. -/
theorem finiteComplexVectorCombination_gramCoercive
    {m : Type*} [Fintype m] (f b : m → ℂ)
    (htrace : 0 < finiteComplexVectorNormSq f +
      finiteComplexVectorNormSq b) (c d : ℂ) :
    finiteComplexVectorGramCoercivity f b *
        (‖c‖ ^ 2 + ‖d‖ ^ 2) ≤
      finiteComplexVectorNormSq (c • f + d • b) := by
  let A := finiteComplexVectorNormSq f
  let B := finiteComplexVectorNormSq b
  let C := ‖star b ⬝ᵥ f‖
  have hbase := twoByTwoGram_quadratic_lower_bound
    (A := A) (B := B) (C := C) (x := ‖c‖) (y := ‖d‖) htrace
  have hinterference :
      -(‖d‖ * ‖c‖ * C) ≤
        (star d * c * (star b ⬝ᵥ f)).re := by
    have h := (abs_le.mp (Complex.abs_re_le_norm
      (star d * c * (star b ⬝ᵥ f)))).1
    simpa [C, norm_mul, mul_comm, mul_left_comm, mul_assoc] using h
  have hcross :
      A * ‖c‖ ^ 2 + B * ‖d‖ ^ 2 -
          2 * C * ‖c‖ * ‖d‖ ≤
        ‖c‖ ^ 2 * A + ‖d‖ ^ 2 * B +
          2 * (star d * c * (star b ⬝ᵥ f)).re := by
    have hC : 0 ≤ C := norm_nonneg _
    nlinarith
  rw [finiteComplexVectorCombination_normSq_eq]
  unfold finiteComplexVectorGramCoercivity
  change ((A * B - C ^ 2) / (A + B)) *
      (‖c‖ ^ 2 + ‖d‖ ^ 2) ≤ _
  exact hbase.trans hcross

/-- A complex combination of the two normalized finite eta-prefix columns at
a zero and its critical-line reflection. -/
def pairedEtaGeometricCriticalReflectionPrefixCombination
    (q : ℕ) (rho : NontrivialZetaZero) (n M : ℕ)
    (c d : ℂ) : Fin M → ℂ :=
  c • pairedEtaLowerMomentGeometricPhaseNormalizedPrefixVector
      q (1 / 2) rho n M +
    d • pairedEtaLowerMomentGeometricPhaseNormalizedPrefixVector
      q (1 / 2) (NontrivialZetaZero.conjugatePartner rho) n M

/-- Literal determinant-over-trace coefficient of the normalized finite eta
prefix pair at one cutoff block. -/
def pairedEtaGeometricCriticalReflectionPrefixCoercivity
    (q : ℕ) (rho : NontrivialZetaZero) (n M : ℕ) : ℝ :=
  finiteComplexVectorGramCoercivity
    (pairedEtaLowerMomentGeometricPhaseNormalizedPrefixVector
      q (1 / 2) rho n M)
    (pairedEtaLowerMomentGeometricPhaseNormalizedPrefixVector
      q (1 / 2) (NontrivialZetaZero.conjugatePartner rho) n M)

/-- The literal finite-prefix coercivity coefficient converges to the positive
reciprocal-mode coercivity constant. -/
theorem tendsto_pairedEtaGeometricCriticalReflectionPrefixCoercivity
    {q : ℕ} (hqOdd : Odd q) (hq : 1 < q) {T : ℝ}
    (rho : ↥(spectralUpperZetaZeroWindow T))
    (M : ℕ) (hM : 0 < M) :
    Tendsto (fun n : ℕ ↦
      pairedEtaGeometricCriticalReflectionPrefixCoercivity
        q rho.1 n M) atTop
      (nhds (finiteReciprocalRadialPhaseCoercivity M
        ‖etaGeometricShiftedMode q (1 / 2) rho.1.val‖
        (etaGeometricNormalizedMode q rho.1.val))) := by
  have hforward :=
    tendsto_pairedEtaLowerMomentGeometricPhaseNormalizedPrefixNormSq_shifted
      hqOdd hq (1 / 2) rho.1 M
  have hbackward :=
    tendsto_pairedEtaLowerMomentGeometricPhaseNormalizedPrefixNormSq_shifted
      hqOdd hq (1 / 2)
        (NontrivialZetaZero.conjugatePartner rho.1) M
  have hcorrelation :=
    (tendsto_pairedEtaLowerMomentGeometricPhaseNormalizedPrefixCorrelation_shifted
      hqOdd hq (1 / 2) rho.1
        (NontrivialZetaZero.conjugatePartner rho.1) M).norm.pow 2
  have hden :
      finiteGeometricModeNormSq M
          (etaGeometricShiftedMode q (1 / 2) rho.1.val) +
        finiteGeometricModeNormSq M
          (etaGeometricShiftedMode q (1 / 2)
            (NontrivialZetaZero.conjugatePartner rho.1).val) ≠ 0 := by
    positivity [finiteGeometricModeNormSq_pos hM
      (etaGeometricShiftedMode q (1 / 2) rho.1.val),
      finiteGeometricModeNormSq_pos hM
        (etaGeometricShiftedMode q (1 / 2)
          (NontrivialZetaZero.conjugatePartner rho.1).val)]
  have hcorrelationLimit :
      ‖star (finiteGeometricPhaseVector M
          (etaGeometricShiftedMode q (1 / 2)
            (NontrivialZetaZero.conjugatePartner rho.1).val)) ⬝ᵥ
        finiteGeometricPhaseVector M
          (etaGeometricShiftedMode q (1 / 2) rho.1.val)‖ ^ 2 =
        (M : ℝ) ^ 2 := by
    rw [spectralUpperZetaZeroWindow_criticalShiftedPair_correlation_eq_card
      hq rho M]
    simp
  have hquot := ((hforward.mul hbackward).sub hcorrelation).div
    (hforward.add hbackward) hden
  rw [hcorrelationLimit] at hquot
  rw [finiteReciprocalRadialPhaseCoercivity_eq_criticalShiftedPair
    hq.le rho.1 M]
  unfold pairedEtaGeometricCriticalReflectionPrefixCoercivity
    finiteComplexVectorGramCoercivity finiteComplexVectorNormSq
  apply hquot.congr'
  exact Filter.Eventually.of_forall fun _ ↦ rfl

/-- Every sufficiently late literal reflection-prefix pair obeys one half-limit
coercive lower bound uniformly for all complex coefficient pairs. -/
theorem eventually_pairedEtaGeometricCriticalReflectionPrefixCombination_uniformlyCoercive
    {q : ℕ} (hqOdd : Odd q) (hq : 1 < q) {T : ℝ}
    (rho : ↥(spectralUpperZetaZeroWindow T))
    {M : ℕ} (hM : 1 < M) :
    ∀ᶠ n in atTop, ∀ c d : ℂ,
      finiteReciprocalRadialPhaseCoercivity M
          ‖etaGeometricShiftedMode q (1 / 2) rho.1.val‖
          (etaGeometricNormalizedMode q rho.1.val) / 2 *
          (‖c‖ ^ 2 + ‖d‖ ^ 2) ≤
        finiteComplexVectorNormSq
          (pairedEtaGeometricCriticalReflectionPrefixCombination
            q rho.1 n M c d) := by
  let κ := finiteReciprocalRadialPhaseCoercivity M
    ‖etaGeometricShiftedMode q (1 / 2) rho.1.val‖
    (etaGeometricNormalizedMode q rho.1.val)
  have hκpos : 0 < κ := by
    exact spectralUpperZetaZeroWindow_criticalShiftedReflectionCoercivity_pos
      hq rho hM
  have hκhalf : κ / 2 < κ := by linarith
  have hκEventually : ∀ᶠ n in atTop,
      κ / 2 < pairedEtaGeometricCriticalReflectionPrefixCoercivity
        q rho.1 n M :=
    (tendsto_pairedEtaGeometricCriticalReflectionPrefixCoercivity
      hqOdd hq rho M (by omega)).eventually (Ioi_mem_nhds hκhalf)
  have hforward :=
    tendsto_pairedEtaLowerMomentGeometricPhaseNormalizedPrefixNormSq_shifted
      hqOdd hq (1 / 2) rho.1 M
  have hbackward :=
    tendsto_pairedEtaLowerMomentGeometricPhaseNormalizedPrefixNormSq_shifted
      hqOdd hq (1 / 2)
        (NontrivialZetaZero.conjugatePartner rho.1) M
  have htraceLimit :
      0 < finiteGeometricModeNormSq M
          (etaGeometricShiftedMode q (1 / 2) rho.1.val) +
        finiteGeometricModeNormSq M
          (etaGeometricShiftedMode q (1 / 2)
            (NontrivialZetaZero.conjugatePartner rho.1).val) :=
    add_pos
      (finiteGeometricModeNormSq_pos (by omega) _)
      (finiteGeometricModeNormSq_pos (by omega) _)
  have htraceEventually : ∀ᶠ n in atTop,
      0 <
        pairedEtaLowerMomentGeometricPhaseNormalizedPrefixNormSq
            q (1 / 2) rho.1 n M +
          pairedEtaLowerMomentGeometricPhaseNormalizedPrefixNormSq
            q (1 / 2) (NontrivialZetaZero.conjugatePartner rho.1) n M :=
    (hforward.add hbackward).eventually (Ioi_mem_nhds htraceLimit)
  filter_upwards [hκEventually, htraceEventually] with n hκn htrace
  intro c d
  have hgeneric := finiteComplexVectorCombination_gramCoercive
    (pairedEtaLowerMomentGeometricPhaseNormalizedPrefixVector
      q (1 / 2) rho.1 n M)
    (pairedEtaLowerMomentGeometricPhaseNormalizedPrefixVector
      q (1 / 2) (NontrivialZetaZero.conjugatePartner rho.1) n M)
    (by
      simpa [finiteComplexVectorNormSq,
        pairedEtaLowerMomentGeometricPhaseNormalizedPrefixNormSq] using htrace)
    c d
  have hcoeff : 0 ≤ ‖c‖ ^ 2 + ‖d‖ ^ 2 := by positivity
  have hscaled := mul_le_mul_of_nonneg_right (le_of_lt hκn) hcoeff
  simpa [κ, pairedEtaGeometricCriticalReflectionPrefixCoercivity,
    pairedEtaGeometricCriticalReflectionPrefixCombination] using
    hscaled.trans hgeneric

/-- Substituting the moving completion coefficients gives an eventual explicit
coercive lower bound for the complex channel recovered from the actual upper
reflection-even frame atom. -/
theorem eventually_spectralUpperZetaZeroWindow_geometricCriticalTiltedFrame_coercive
    {q : ℕ} (hqOdd : Odd q) (hq : 1 < q) {T : ℝ}
    (rho : ↥(spectralUpperZetaZeroWindow T))
    {M : ℕ} (hM : 1 < M) :
    ∀ᶠ n in atTop,
      finiteReciprocalRadialPhaseCoercivity M
          ‖etaGeometricShiftedMode q (1 / 2) rho.1.val‖
          (etaGeometricNormalizedMode q rho.1.val) / 2 *
          (‖pairedEtaGeometricCompletedPrefixCoefficient q rho.1 n‖ ^ 2 +
            ‖pairedEtaGeometricCompletedPrefixCoefficient q
              (NontrivialZetaZero.conjugatePartner rho.1) n‖ ^ 2) ≤
        finiteComplexVectorNormSq
          (pairedEtaGeometricCriticalTiltedUpperFrameRecoveredVector
            q T rho n M) := by
  have hprefix :=
    eventually_pairedEtaGeometricCriticalReflectionPrefixCombination_uniformlyCoercive
      hqOdd hq rho hM
  filter_upwards [hprefix, eventually_ge_atTop (1 : ℕ)] with n hcoercive hn
  have hactual := hcoercive
    (pairedEtaGeometricCompletedPrefixCoefficient q rho.1 n)
    (pairedEtaGeometricCompletedPrefixCoefficient q
      (NontrivialZetaZero.conjugatePartner rho.1) n)
  rw [spectralUpperZetaZeroWindow_geometricCriticalTiltedFrame_eq_completedPrefixCombination
    hqOdd hq rho hn M]
  simpa [pairedEtaGeometricCriticalReflectionPrefixCombination, add_comm] using
    hactual

/-- The complex channel recovered from every sufficiently late actual upper
frame atom has strictly positive squared norm. -/
theorem eventually_spectralUpperZetaZeroWindow_geometricCriticalTiltedFrame_normSq_pos
    {q : ℕ} (hqOdd : Odd q) (hq : 1 < q) {T : ℝ}
    (rho : ↥(spectralUpperZetaZeroWindow T))
    {M : ℕ} (hM : 1 < M) :
    ∀ᶠ n in atTop,
      0 < finiteComplexVectorNormSq
        (pairedEtaGeometricCriticalTiltedUpperFrameRecoveredVector
          q T rho n M) := by
  have hbound :=
    eventually_spectralUpperZetaZeroWindow_geometricCriticalTiltedFrame_coercive
      hqOdd hq rho hM
  have hκ : 0 < finiteReciprocalRadialPhaseCoercivity M
      ‖etaGeometricShiftedMode q (1 / 2) rho.1.val‖
      (etaGeometricNormalizedMode q rho.1.val) / 2 := by
    exact half_pos
      (spectralUpperZetaZeroWindow_criticalShiftedReflectionCoercivity_pos
        hq rho hM)
  filter_upwards [hbound] with n hn
  have hcoefficient :
      0 < ‖pairedEtaGeometricCompletedPrefixCoefficient q rho.1 n‖ ^ 2 +
        ‖pairedEtaGeometricCompletedPrefixCoefficient q
          (NontrivialZetaZero.conjugatePartner rho.1) n‖ ^ 2 := by
    apply add_pos_of_pos_of_nonneg
    · exact sq_pos_of_pos (norm_pos_iff.mpr
        (pairedEtaGeometricCompletedPrefixCoefficient_ne_zero
          hq.le rho.1 n))
    · positivity
  exact (mul_pos hκ hcoefficient).trans_le hn

end

end RiemannGaussian
