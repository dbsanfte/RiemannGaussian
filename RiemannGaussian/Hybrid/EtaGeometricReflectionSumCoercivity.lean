import RiemannGaussian.Hybrid.EtaGeometricReflectionSumGram

/-!
# Quantitative coercivity of reciprocal eta reflection pairs

The positive Gram determinant of an off-line reciprocal-radius pair gives
more than noncancellation.  This module proves an explicit lower spectral
bound for its complete signed quadratic form.  If `A` and `B` are the two
mode norm squares and their exact cross-correlation is `M`, then every complex
coefficient pair is bounded below by

`(A * B - M^2) / (A + B) * (|c|^2 + |d|^2)`.

The proof retains the actual complex interference until its final sharp
real-part estimate.  Lean then identifies this abstract constant and linear
combination with the literal critical-shifted eta modes of every upper-window
zero/reflection pair.  This supplies quantitative local coercivity for any
future completion coefficients.  It does not yet control correlations
between different completed reflection sums or improve the certificate.
-/

open Complex Matrix Finset
open scoped BigOperators Classical ComplexConjugate ComplexOrder Matrix Real

namespace RiemannGaussian

noncomputable section

/-- A positive-trace two-by-two Gram form is bounded below by determinant
over trace times the Euclidean coefficient norm. -/
theorem twoByTwoGram_quadratic_lower_bound
    {A B C x y : ℝ} (htrace : 0 < A + B) :
    (A * B - C ^ 2) / (A + B) * (x ^ 2 + y ^ 2) ≤
      A * x ^ 2 + B * y ^ 2 - 2 * C * x * y := by
  rw [div_mul_eq_mul_div]
  apply (div_le_iff₀ htrace).2
  nlinarith [sq_nonneg (A * x - C * y),
    sq_nonneg (B * y - C * x)]

/-- Determinant-over-trace coercivity constant of a finite reciprocal-radius
phase pair. -/
def finiteReciprocalRadialPhaseCoercivity
    (M : ℕ) (r : ℝ) (z : ℂ) : ℝ :=
  finiteReciprocalRadialPhaseReserve M r z /
    (finiteGeometricModeNormSq M ((r : ℂ) * z) +
      finiteGeometricModeNormSq M (((r : ℂ)⁻¹) * z))

/-- The reciprocal-radius coercivity constant is strictly positive beyond
length one when the forward radius is greater than one. -/
theorem finiteReciprocalRadialPhaseCoercivity_pos
    {M : ℕ} (hM : 1 < M) {r : ℝ} (hr : 1 < r)
    (z : ℂ) (hz : ‖z‖ = 1) :
    0 < finiteReciprocalRadialPhaseCoercivity M r z := by
  unfold finiteReciprocalRadialPhaseCoercivity
  apply div_pos (finiteReciprocalRadialPhaseReserve_pos hM hr z hz)
  exact add_pos
    (finiteGeometricModeNormSq_pos (by omega) ((r : ℂ) * z))
    (finiteGeometricModeNormSq_pos (by omega) (((r : ℂ)⁻¹) * z))

/-- Every complex combination of a reciprocal-radius phase pair obeys the
explicit determinant-over-trace norm lower bound. -/
theorem finiteReciprocalRadialPhaseCombination_coercive
    {M : ℕ} (hM : 1 < M) {r : ℝ} (hr : 1 < r)
    (z : ℂ) (hz : ‖z‖ = 1) (c d : ℂ) :
    finiteReciprocalRadialPhaseCoercivity M r z *
        (‖c‖ ^ 2 + ‖d‖ ^ 2) ≤
      finiteComplexVectorNormSq
        (finiteReciprocalRadialPhaseCombination M r z c d) := by
  let A := finiteGeometricModeNormSq M ((r : ℂ) * z)
  let B := finiteGeometricModeNormSq M (((r : ℂ)⁻¹) * z)
  have htrace : 0 < A + B := add_pos
    (finiteGeometricModeNormSq_pos (by omega) ((r : ℂ) * z))
    (finiteGeometricModeNormSq_pos (by omega) (((r : ℂ)⁻¹) * z))
  have hbase := twoByTwoGram_quadratic_lower_bound
    (A := A) (B := B) (C := (M : ℝ))
    (x := ‖c‖) (y := ‖d‖) htrace
  have hinterference :
      -(‖c‖ * ‖d‖) ≤ (star c * d).re := by
    have h := (abs_le.mp (Complex.abs_re_le_norm (star c * d))).1
    simpa [norm_mul] using h
  have hcross :
      A * ‖c‖ ^ 2 + B * ‖d‖ ^ 2 -
          2 * (M : ℝ) * ‖c‖ * ‖d‖ ≤
        A * ‖c‖ ^ 2 + B * ‖d‖ ^ 2 +
          2 * M * (star c * d).re := by
    have hMnonneg : (0 : ℝ) ≤ M := by positivity
    nlinarith
  rw [finiteReciprocalRadialPhaseCombination_normSq_eq
    M (zero_lt_one.trans hr) z hz c d]
  unfold finiteReciprocalRadialPhaseCoercivity
    finiteReciprocalRadialPhaseReserve
  change ((A * B - (M : ℝ) ^ 2) / (A + B)) *
      (‖c‖ ^ 2 + ‖d‖ ^ 2) ≤ _
  simpa [A, B, mul_comm, mul_left_comm, mul_assoc] using
    hbase.trans hcross

/-- A complex linear combination of the literal critical-shifted eta modes at
a zero and its critical-line reflection. -/
def finiteEtaCriticalShiftedReflectionCombination
    (M q : ℕ) (rho : NontrivialZetaZero) (c d : ℂ) : Fin M → ℂ :=
  c • finiteGeometricPhaseVector M
      (etaGeometricShiftedMode q (1 / 2) rho.val) +
    d • finiteGeometricPhaseVector M
      (etaGeometricShiftedMode q (1 / 2)
        (NontrivialZetaZero.conjugatePartner rho).val)

/-- The abstract reciprocal-radius combination is exactly the literal
critical-shifted eta reflection combination. -/
theorem finiteReciprocalRadialPhaseCombination_eq_criticalShiftedReflectionCombination
    {q : ℕ} (hq : 0 < q) (rho : NontrivialZetaZero)
    (M : ℕ) (c d : ℂ) :
    finiteReciprocalRadialPhaseCombination M
        ‖etaGeometricShiftedMode q (1 / 2) rho.val‖
        (etaGeometricNormalizedMode q rho.val) c d =
      finiteEtaCriticalShiftedReflectionCombination M q rho c d := by
  have hpair := finiteReciprocalRadialPhaseModes_eq_criticalShiftedPair
    hq rho M
  have hzero := congrFun hpair (0 : Fin 2)
  have hone := congrFun hpair (1 : Fin 2)
  unfold finiteReciprocalRadialPhaseCombination
    finiteEtaCriticalShiftedReflectionCombination
  rw [hzero, hone]
  rfl

/-- The abstract reciprocal-radius coercivity is exactly determinant over
trace for the two literal critical-shifted eta mode norms. -/
theorem finiteReciprocalRadialPhaseCoercivity_eq_criticalShiftedPair
    {q : ℕ} (hq : 0 < q) (rho : NontrivialZetaZero) (M : ℕ) :
    finiteReciprocalRadialPhaseCoercivity M
        ‖etaGeometricShiftedMode q (1 / 2) rho.val‖
        (etaGeometricNormalizedMode q rho.val) =
      (finiteGeometricModeNormSq M
            (etaGeometricShiftedMode q (1 / 2) rho.val) *
          finiteGeometricModeNormSq M
            (etaGeometricShiftedMode q (1 / 2)
              (NontrivialZetaZero.conjugatePartner rho).val) -
          (M : ℝ) ^ 2) /
        (finiteGeometricModeNormSq M
            (etaGeometricShiftedMode q (1 / 2) rho.val) +
          finiteGeometricModeNormSq M
            (etaGeometricShiftedMode q (1 / 2)
              (NontrivialZetaZero.conjugatePartner rho).val)) := by
  have hpair := finiteReciprocalRadialPhaseModes_eq_criticalShiftedPair
    hq rho M
  have hzero :
      finiteGeometricPhaseVector M
          ((‖etaGeometricShiftedMode q (1 / 2) rho.val‖ : ℂ) *
            etaGeometricNormalizedMode q rho.val) =
        finiteGeometricPhaseVector M
          (etaGeometricShiftedMode q (1 / 2) rho.val) := by
    simpa [finiteReciprocalRadialPhaseModes] using
      congrFun hpair (0 : Fin 2)
  have hone :
      finiteGeometricPhaseVector M
          ((‖etaGeometricShiftedMode q (1 / 2) rho.val‖ : ℂ)⁻¹ *
            etaGeometricNormalizedMode q rho.val) =
        finiteGeometricPhaseVector M
          (etaGeometricShiftedMode q (1 / 2)
            (NontrivialZetaZero.conjugatePartner rho).val) := by
    simpa [finiteReciprocalRadialPhaseModes] using
      congrFun hpair (1 : Fin 2)
  have hnormZero := congrArg finiteComplexVectorNormSq hzero
  have hnormOne := congrArg finiteComplexVectorNormSq hone
  change finiteGeometricModeNormSq M
      ((‖etaGeometricShiftedMode q (1 / 2) rho.val‖ : ℂ) *
        etaGeometricNormalizedMode q rho.val) =
    finiteGeometricModeNormSq M
      (etaGeometricShiftedMode q (1 / 2) rho.val) at hnormZero
  change finiteGeometricModeNormSq M
      ((‖etaGeometricShiftedMode q (1 / 2) rho.val‖ : ℂ)⁻¹ *
        etaGeometricNormalizedMode q rho.val) =
    finiteGeometricModeNormSq M
      (etaGeometricShiftedMode q (1 / 2)
        (NontrivialZetaZero.conjugatePartner rho).val) at hnormOne
  unfold finiteReciprocalRadialPhaseCoercivity
    finiteReciprocalRadialPhaseReserve
  rw [hnormZero, hnormOne]

/-- Every upper-window eta reflection combination inherits the positive
reciprocal-radius coercivity bound. -/
theorem spectralUpperZetaZeroWindow_criticalShiftedReflectionCombination_coercive
    {q : ℕ} (hq : 1 < q) {T : ℝ}
    (rho : ↥(spectralUpperZetaZeroWindow T))
    {M : ℕ} (hM : 1 < M) (c d : ℂ) :
    finiteReciprocalRadialPhaseCoercivity M
        ‖etaGeometricShiftedMode q (1 / 2) rho.1.val‖
        (etaGeometricNormalizedMode q rho.1.val) *
        (‖c‖ ^ 2 + ‖d‖ ^ 2) ≤
      finiteComplexVectorNormSq
        (finiteEtaCriticalShiftedReflectionCombination
          M q rho.1 c d) := by
  rw [← finiteReciprocalRadialPhaseCombination_eq_criticalShiftedReflectionCombination
    hq.le rho.1 M c d]
  exact finiteReciprocalRadialPhaseCombination_coercive hM
    (spectralUpperZetaZeroWindow_criticalShiftedMode_radii hq rho).1
    (etaGeometricNormalizedMode q rho.1.val)
    (norm_etaGeometricNormalizedMode hq.le rho.1.val) c d

/-- Literal determinant-over-trace lower bound for every complex combination
of an upper-window zero and its critical-shifted reflection. -/
theorem spectralUpperZetaZeroWindow_criticalShiftedReflectionCombination_gramLowerBound
    {q : ℕ} (hq : 1 < q) {T : ℝ}
    (rho : ↥(spectralUpperZetaZeroWindow T))
    {M : ℕ} (hM : 1 < M) (c d : ℂ) :
    ((finiteGeometricModeNormSq M
            (etaGeometricShiftedMode q (1 / 2) rho.1.val) *
          finiteGeometricModeNormSq M
            (etaGeometricShiftedMode q (1 / 2)
              (NontrivialZetaZero.conjugatePartner rho.1).val) -
          (M : ℝ) ^ 2) /
        (finiteGeometricModeNormSq M
            (etaGeometricShiftedMode q (1 / 2) rho.1.val) +
          finiteGeometricModeNormSq M
            (etaGeometricShiftedMode q (1 / 2)
              (NontrivialZetaZero.conjugatePartner rho.1).val))) *
        (‖c‖ ^ 2 + ‖d‖ ^ 2) ≤
      finiteComplexVectorNormSq
        (finiteEtaCriticalShiftedReflectionCombination
          M q rho.1 c d) := by
  rw [← finiteReciprocalRadialPhaseCoercivity_eq_criticalShiftedPair
    hq.le rho.1 M]
  exact
    spectralUpperZetaZeroWindow_criticalShiftedReflectionCombination_coercive
      hq rho hM c d

/-- The named reciprocal-radius coercivity constant of every literal
upper-window reflection pair is positive. -/
theorem spectralUpperZetaZeroWindow_criticalShiftedReflectionCoercivity_pos
    {q : ℕ} (hq : 1 < q) {T : ℝ}
    (rho : ↥(spectralUpperZetaZeroWindow T))
    {M : ℕ} (hM : 1 < M) :
    0 < finiteReciprocalRadialPhaseCoercivity M
      ‖etaGeometricShiftedMode q (1 / 2) rho.1.val‖
      (etaGeometricNormalizedMode q rho.1.val) := by
  exact finiteReciprocalRadialPhaseCoercivity_pos hM
    (spectralUpperZetaZeroWindow_criticalShiftedMode_radii hq rho).1
    (etaGeometricNormalizedMode q rho.1.val)
    (norm_etaGeometricNormalizedMode hq.le rho.1.val)

/-- The explicit determinant-over-trace constant of every literal
upper-window reflection pair is strictly positive. -/
theorem spectralUpperZetaZeroWindow_criticalShiftedReflectionGramCoercivity_pos
    {q : ℕ} (hq : 1 < q) {T : ℝ}
    (rho : ↥(spectralUpperZetaZeroWindow T))
    {M : ℕ} (hM : 1 < M) :
    0 <
      (finiteGeometricModeNormSq M
            (etaGeometricShiftedMode q (1 / 2) rho.1.val) *
          finiteGeometricModeNormSq M
            (etaGeometricShiftedMode q (1 / 2)
              (NontrivialZetaZero.conjugatePartner rho.1).val) -
          (M : ℝ) ^ 2) /
        (finiteGeometricModeNormSq M
            (etaGeometricShiftedMode q (1 / 2) rho.1.val) +
          finiteGeometricModeNormSq M
            (etaGeometricShiftedMode q (1 / 2)
              (NontrivialZetaZero.conjugatePartner rho.1).val)) := by
  rw [← finiteReciprocalRadialPhaseCoercivity_eq_criticalShiftedPair
    hq.le rho.1 M]
  exact spectralUpperZetaZeroWindow_criticalShiftedReflectionCoercivity_pos
    hq rho hM

end

end RiemannGaussian
