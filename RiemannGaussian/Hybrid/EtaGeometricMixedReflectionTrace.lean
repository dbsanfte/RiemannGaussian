import RiemannGaussian.Hybrid.EtaGeometricNormalizedReflection
import RiemannGaussian.EtaEnergyFiniteWindowTrace

/-!
# Mixed reflection trace for the geometric eta carrier

Complete whitening of the signed zero-space pullback cancels the eta metric
and leaves only the reflected-zero permutation `P`.  The first scalar that
retains both pieces of information is instead the mixed trace of `P K`, where
`K = Cᴴ C` is the positive zero-index Gram.

This module proves that `P K = Cᵀ C`.  By cyclicity of trace, its real trace is
exactly the already evaluated real trace of the literal complex-symmetric eta
window `C Cᵀ`.  The positive comparison mass `tr(K)` is likewise the real
trace of the Hermitian coordinate Gram `C Cᴴ`.

The checked colour ledger therefore descends without information loss to the
exact scalar identities

`positiveMass - mixedTrace = 2 * offLineImagMass`,

`positiveMass + mixedTrace = 2 * (onLineMass + offLineRealMass)`.

Consequently the mixed trace lies between plus and minus the positive mass.
On every nonempty window with separated features, their quotient is a genuine
number in `[-1, 1]`.  Unlike the fully whitened matrix, this quotient still
depends on multiplicity-weighted eta amplitudes.  No arithmetic bound strong
enough to improve the zero proportion is asserted here.
-/

open Complex Filter
open scoped Classical ComplexConjugate ComplexOrder Matrix

namespace RiemannGaussian

noncomputable section

/-- Positive real trace mass of the multiplicity-weighted zero-index Gram. -/
def pairedEtaGeometricZeroGramTraceMass
    (q : ℕ) (T : ℝ) (n : ℕ) : ℝ :=
  HermitianInertia.rtrace
    (pairedEtaGeometricMultiplicityWeightedZeroGram q
      (spectralZetaZeroWindow T) n)

/-- Real mixed trace coupling critical-line reflection to the positive eta
metric before complete whitening. -/
def pairedEtaGeometricReflectionMixedTrace
    (q : ℕ) (T : ℝ) (hT : 0 ≤ T) (n : ℕ) : ℝ :=
  HermitianInertia.rtrace
    (pairedEtaZeroWindowConjugatePartnerMatrix T hT *
      pairedEtaGeometricMultiplicityWeightedZeroGram q
        (spectralZetaZeroWindow T) n)

/-- Dimensionless signed-to-positive trace balance retaining the coupled
reflection and eta metric. -/
def pairedEtaGeometricReflectionTraceBalance
    (q : ℕ) (T : ℝ) (hT : 0 ≤ T) (n : ℕ) : ℝ :=
  pairedEtaGeometricReflectionMixedTrace q T hT n /
    pairedEtaGeometricZeroGramTraceMass q T n

/-- The mixed zero-space matrix is the ordinary-transpose Gram `Cᵀ C`. -/
theorem pairedEtaZeroWindowConjugatePartnerMatrix_mul_zeroGram_eq_transpose_mul_synthesis
    (q : ℕ) {T : ℝ} (hT : 0 ≤ T) (n : ℕ) :
    pairedEtaZeroWindowConjugatePartnerMatrix T hT *
        pairedEtaGeometricMultiplicityWeightedZeroGram q
          (spectralZetaZeroWindow T) n =
      (pairedEtaGeometricMultiplicityWeightedFeatureSynthesisMatrix q
          (spectralZetaZeroWindow T) n)ᵀ *
        pairedEtaGeometricMultiplicityWeightedFeatureSynthesisMatrix q
          (spectralZetaZeroWindow T) n := by
  rw [pairedEtaGeometricMultiplicityWeightedZeroGram,
    ← Matrix.mul_assoc,
    pairedEtaZeroWindowConjugatePartnerMatrix_mul_synthesis_conjTranspose_eq_transpose
      q hT n]

/-- The mixed reflection trace is exactly the real trace of the literal
signed eta coordinate block. -/
theorem pairedEtaGeometricReflectionMixedTrace_eq_zeroWindowBlock_rtrace
    (q : ℕ) {T : ℝ} (hT : 0 ≤ T) (n : ℕ) :
    pairedEtaGeometricReflectionMixedTrace q T hT n =
      HermitianInertia.rtrace
        (pairedEtaTopPrefixFiniteZeroWindowBlock
          (fun j : Fin (spectralZetaZeroWindow T).card ↦
            pairedEtaGeometricHyperbolicCutoff q n j) T) := by
  unfold pairedEtaGeometricReflectionMixedTrace HermitianInertia.rtrace
  rw [pairedEtaZeroWindowConjugatePartnerMatrix_mul_zeroGram_eq_transpose_mul_synthesis
      q hT n,
    Matrix.trace_mul_comm,
    pairedEtaGeometricMultiplicityWeightedFeatureSynthesisMatrix_mul_transpose_eq_zeroWindowBlock]

/-- The positive zero-Gram trace mass is exactly the real trace of the
Hermitian eta coordinate Gram. -/
theorem pairedEtaGeometricZeroGramTraceMass_eq_zeroWindowHermitianGram_rtrace
    (q : ℕ) (T : ℝ) (n : ℕ) :
    pairedEtaGeometricZeroGramTraceMass q T n =
      HermitianInertia.rtrace
        (pairedEtaTopPrefixFiniteZeroWindowHermitianGram
          (fun j : Fin (spectralZetaZeroWindow T).card ↦
            pairedEtaGeometricHyperbolicCutoff q n j) T) := by
  unfold pairedEtaGeometricZeroGramTraceMass HermitianInertia.rtrace
    pairedEtaGeometricMultiplicityWeightedZeroGram
  rw [Matrix.trace_mul_comm,
    ← pairedEtaGeometricMultiplicityWeightedCoordinateGram]
  exact congrArg Complex.re
    (congrArg Matrix.trace
      (pairedEtaGeometricMultiplicityWeightedCoordinateGram_eq_zeroWindowHermitianGram
        q T n))

/-- Exact scalar colour ledger: the positive mass minus the mixed reflection
trace is twice the imaginary off-line mass. -/
theorem pairedEtaGeometricZeroGramTraceMass_sub_reflectionMixedTrace_eq_two_offLineImag
    (q : ℕ) {T : ℝ} (hT : 0 ≤ T) (n : ℕ) :
    pairedEtaGeometricZeroGramTraceMass q T n -
        pairedEtaGeometricReflectionMixedTrace q T hT n =
      2 * HermitianInertia.rtrace
        (pairedEtaTopPrefixFiniteZeroWindowOffLineImagBlock
          (fun j : Fin (spectralZetaZeroWindow T).card ↦
            pairedEtaGeometricHyperbolicCutoff q n j) T) := by
  rw [pairedEtaGeometricZeroGramTraceMass_eq_zeroWindowHermitianGram_rtrace,
    pairedEtaGeometricReflectionMixedTrace_eq_zeroWindowBlock_rtrace q hT n,
    ← HermitianInertia.rtrace_sub,
    pairedEtaTopPrefixFiniteZeroWindowHermitianGram_sub_signedBlock_eq_two_imag
      _ hT]
  simp [HermitianInertia.rtrace, Matrix.trace_smul]

/-- Exact scalar colour ledger: the positive mass plus the mixed reflection
trace is twice the on-line-plus-real off-line mass. -/
theorem pairedEtaGeometricZeroGramTraceMass_add_reflectionMixedTrace_eq_two_onLine_add_real
    (q : ℕ) {T : ℝ} (hT : 0 ≤ T) (n : ℕ) :
    pairedEtaGeometricZeroGramTraceMass q T n +
        pairedEtaGeometricReflectionMixedTrace q T hT n =
      2 * (HermitianInertia.rtrace
          (pairedEtaTopPrefixFiniteZeroWindowOnLineBlock
            (fun j : Fin (spectralZetaZeroWindow T).card ↦
              pairedEtaGeometricHyperbolicCutoff q n j) T) +
        HermitianInertia.rtrace
          (pairedEtaTopPrefixFiniteZeroWindowOffLineRealBlock
            (fun j : Fin (spectralZetaZeroWindow T).card ↦
              pairedEtaGeometricHyperbolicCutoff q n j) T)) := by
  rw [pairedEtaGeometricZeroGramTraceMass_eq_zeroWindowHermitianGram_rtrace,
    pairedEtaGeometricReflectionMixedTrace_eq_zeroWindowBlock_rtrace q hT n,
    ← HermitianInertia.rtrace_add,
    pairedEtaTopPrefixFiniteZeroWindowHermitianGram_add_signedBlock_eq_two_onLine_add_real
      _ hT]
  simp [HermitianInertia.rtrace, Matrix.trace_smul]
  ring

/-- The mixed reflection trace never exceeds the positive eta trace mass. -/
theorem pairedEtaGeometricReflectionMixedTrace_le_zeroGramTraceMass
    (q : ℕ) {T : ℝ} (hT : 0 ≤ T) (n : ℕ) :
    pairedEtaGeometricReflectionMixedTrace q T hT n ≤
      pairedEtaGeometricZeroGramTraceMass q T n := by
  have himag := pairedEtaTopPrefixFiniteZeroWindowOffLineImagBlock_rtrace_nonneg
    (fun j : Fin (spectralZetaZeroWindow T).card ↦
      pairedEtaGeometricHyperbolicCutoff q n j) T
  have hledger :=
    pairedEtaGeometricZeroGramTraceMass_sub_reflectionMixedTrace_eq_two_offLineImag
      q hT n
  linarith

/-- The negative positive eta trace mass never exceeds the mixed reflection
trace. -/
theorem neg_zeroGramTraceMass_le_pairedEtaGeometricReflectionMixedTrace
    (q : ℕ) {T : ℝ} (hT : 0 ≤ T) (n : ℕ) :
    -pairedEtaGeometricZeroGramTraceMass q T n ≤
      pairedEtaGeometricReflectionMixedTrace q T hT n := by
  have hon := pairedEtaTopPrefixFiniteZeroWindowOnLineBlock_rtrace_nonneg
    (fun j : Fin (spectralZetaZeroWindow T).card ↦
      pairedEtaGeometricHyperbolicCutoff q n j) T
  have hreal := pairedEtaTopPrefixFiniteZeroWindowOffLineRealBlock_rtrace_nonneg
    (fun j : Fin (spectralZetaZeroWindow T).card ↦
      pairedEtaGeometricHyperbolicCutoff q n j) T
  have hledger :=
    pairedEtaGeometricZeroGramTraceMass_add_reflectionMixedTrace_eq_two_onLine_add_real
      q hT n
  linarith

/-- A positive-definite zero Gram on a nonempty window has strictly positive
real trace mass. -/
theorem pairedEtaGeometricZeroGramTraceMass_pos
    (q : ℕ) {T : ℝ} (n : ℕ)
    (hwindow : (spectralZetaZeroWindow T).Nonempty)
    (hK : (pairedEtaGeometricMultiplicityWeightedZeroGram q
      (spectralZetaZeroWindow T) n).PosDef) :
    0 < pairedEtaGeometricZeroGramTraceMass q T n := by
  let _ : Nonempty (Fin (spectralZetaZeroWindow T).card) :=
    Fin.pos_iff_nonempty.mp (Finset.card_pos.mpr hwindow)
  exact (Complex.pos_iff.mp hK.trace_pos).1

/-- On every nonempty separated block, the information-preserving mixed trace
balance lies in the closed interval `[-1, 1]`. -/
theorem pairedEtaGeometricReflectionTraceBalance_mem_Icc
    (q : ℕ) {T : ℝ} (hT : 0 ≤ T) (n : ℕ)
    (hwindow : (spectralZetaZeroWindow T).Nonempty)
    (hK : (pairedEtaGeometricMultiplicityWeightedZeroGram q
      (spectralZetaZeroWindow T) n).PosDef) :
    pairedEtaGeometricReflectionTraceBalance q T hT n ∈ Set.Icc (-1 : ℝ) 1 := by
  have hpos := pairedEtaGeometricZeroGramTraceMass_pos q n hwindow hK
  constructor
  · rw [pairedEtaGeometricReflectionTraceBalance, le_div_iff₀ hpos]
    simpa using
      neg_zeroGramTraceMass_le_pairedEtaGeometricReflectionMixedTrace q hT n
  · rw [pairedEtaGeometricReflectionTraceBalance, div_le_iff₀ hpos]
    simpa using
      pairedEtaGeometricReflectionMixedTrace_le_zeroGramTraceMass q hT n

/-- Every nonempty nonnegative finite spectral window has one odd prime base
for which the coupled reflection trace has positive denominator and normalized
balance in `[-1, 1]` at all sufficiently late geometric blocks. -/
theorem exists_prime_eventually_positive_zeroGramTraceMass_and_reflectionBalance_mem_Icc
    {T : ℝ} (hT : 0 ≤ T)
    (hwindow : (spectralZetaZeroWindow T).Nonempty) :
    ∃ q : ℕ, q.Prime ∧ Odd q ∧ 1 < q ∧
      ∀ᶠ n in atTop,
        0 < pairedEtaGeometricZeroGramTraceMass q T n ∧
          pairedEtaGeometricReflectionTraceBalance q T hT n ∈
            Set.Icc (-1 : ℝ) 1 := by
  obtain ⟨q, hqPrime, hqOdd, hq, hK⟩ :=
    exists_prime_eventually_posDef_pairedEtaGeometricMultiplicityWeightedZeroGram_and_inv
      (spectralZetaZeroWindow T)
  refine ⟨q, hqPrime, hqOdd, hq, ?_⟩
  filter_upwards [hK] with n hn
  exact ⟨pairedEtaGeometricZeroGramTraceMass_pos q n hwindow hn.1,
    pairedEtaGeometricReflectionTraceBalance_mem_Icc q hT n hwindow hn.1⟩

end

end RiemannGaussian
