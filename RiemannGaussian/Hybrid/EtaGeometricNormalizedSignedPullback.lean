import RiemannGaussian.Hybrid.EtaGeometricZeroGram

/-!
# Normalized signed pullback of the geometric eta carrier

The coordinate Hermitian Gram and the signed eta block obey the checked
two-sided order bounds `Gram - Signed >= 0` and `Gram + Signed >= 0`.  This
module transports those inequalities through the actual
multiplicity-weighted eta synthesis matrix `C` without collapsing its zero
labels.

On zero-index space the positive metric is `K = Cᴴ C`, while the signed
pullback is `B = Cᴴ Signed C`.  Direct matrix algebra turns the coordinate
bounds into `K K - B >= 0` and `K K + B >= 0`.  Whenever the packed features
are independent, `K` is positive definite.  Congruence by `K⁻¹` therefore
produces the normalized Hermitian matrix

`A = K⁻¹ B K⁻¹`

with both `1 - A` and `1 + A` positive semidefinite.  Thus `A` is a checked
Hermitian contraction in Loewner order.  For every nonnegative finite
spectral window, one odd prime base makes this conclusion hold at every
sufficiently late geometric block.

This is an information-preserving normalization theorem.  It does not yet
estimate the trace or spectrum of `A`, and hence does not improve the proved
zero proportion.
-/

open Complex Filter
open scoped Classical ComplexConjugate ComplexOrder Matrix

namespace RiemannGaussian

noncomputable section

/-- Pullback of the genuine signed eta block to the represented-zero index
space through the multiplicity-weighted geometric synthesis matrix. -/
def pairedEtaGeometricSignedZeroPullback
    (q : ℕ) (T : ℝ) (n : ℕ) :
    Matrix (Fin (spectralZetaZeroWindow T).card)
      (Fin (spectralZetaZeroWindow T).card) ℂ :=
  let C := pairedEtaGeometricMultiplicityWeightedFeatureSynthesisMatrix
    q (spectralZetaZeroWindow T) n
  Cᴴ *
    pairedEtaTopPrefixFiniteZeroWindowBlock
      (fun j : Fin (spectralZetaZeroWindow T).card ↦
        pairedEtaGeometricHyperbolicCutoff q n j) T *
    C

/-- Metric-normalized signed pullback on represented-zero index space. -/
def pairedEtaGeometricNormalizedSignedZeroPullback
    (q : ℕ) (T : ℝ) (n : ℕ) :
    Matrix (Fin (spectralZetaZeroWindow T).card)
      (Fin (spectralZetaZeroWindow T).card) ℂ :=
  (pairedEtaGeometricMultiplicityWeightedZeroGram q
      (spectralZetaZeroWindow T) n)⁻¹ *
    pairedEtaGeometricSignedZeroPullback q T n *
    (pairedEtaGeometricMultiplicityWeightedZeroGram q
      (spectralZetaZeroWindow T) n)⁻¹

/-- Pulling back the upper signed-coordinate order bound gives
`K K - B >= 0` on represented-zero index space. -/
theorem pairedEtaGeometricZeroGram_mul_self_sub_signedZeroPullback_posSemidef
    (q : ℕ) {T : ℝ} (hT : 0 ≤ T) (n : ℕ) :
    (pairedEtaGeometricMultiplicityWeightedZeroGram q
          (spectralZetaZeroWindow T) n *
        pairedEtaGeometricMultiplicityWeightedZeroGram q
          (spectralZetaZeroWindow T) n -
      pairedEtaGeometricSignedZeroPullback q T n).PosSemidef := by
  let C := pairedEtaGeometricMultiplicityWeightedFeatureSynthesisMatrix
    q (spectralZetaZeroWindow T) n
  have hpull :=
    (pairedEtaTopPrefixFiniteZeroWindowHermitianGram_sub_signedBlock_posSemidef
      (fun j : Fin (spectralZetaZeroWindow T).card ↦
        pairedEtaGeometricHyperbolicCutoff q n j) hT).conjTranspose_mul_mul_same C
  rw [← pairedEtaGeometricMultiplicityWeightedCoordinateGram_eq_zeroWindowHermitianGram]
    at hpull
  convert hpull using 1
  simp only [pairedEtaGeometricMultiplicityWeightedZeroGram,
    pairedEtaGeometricMultiplicityWeightedCoordinateGram,
    pairedEtaGeometricSignedZeroPullback, C, Matrix.mul_sub, Matrix.sub_mul,
    Matrix.mul_assoc]

/-- Pulling back the lower signed-coordinate order bound gives
`K K + B >= 0` on represented-zero index space. -/
theorem pairedEtaGeometricZeroGram_mul_self_add_signedZeroPullback_posSemidef
    (q : ℕ) {T : ℝ} (hT : 0 ≤ T) (n : ℕ) :
    (pairedEtaGeometricMultiplicityWeightedZeroGram q
          (spectralZetaZeroWindow T) n *
        pairedEtaGeometricMultiplicityWeightedZeroGram q
          (spectralZetaZeroWindow T) n +
      pairedEtaGeometricSignedZeroPullback q T n).PosSemidef := by
  let C := pairedEtaGeometricMultiplicityWeightedFeatureSynthesisMatrix
    q (spectralZetaZeroWindow T) n
  have hpull :=
    (pairedEtaTopPrefixFiniteZeroWindowHermitianGram_add_signedBlock_posSemidef
      (fun j : Fin (spectralZetaZeroWindow T).card ↦
        pairedEtaGeometricHyperbolicCutoff q n j) hT).conjTranspose_mul_mul_same C
  rw [← pairedEtaGeometricMultiplicityWeightedCoordinateGram_eq_zeroWindowHermitianGram]
    at hpull
  convert hpull using 1
  simp only [pairedEtaGeometricMultiplicityWeightedZeroGram,
    pairedEtaGeometricMultiplicityWeightedCoordinateGram,
    pairedEtaGeometricSignedZeroPullback, C, Matrix.mul_add, Matrix.add_mul,
    Matrix.mul_assoc]

/-- The normalized signed zero-space pullback is Hermitian on every
nonnegative spectral window. -/
theorem pairedEtaGeometricNormalizedSignedZeroPullback_isHermitian
    (q : ℕ) {T : ℝ} (hT : 0 ≤ T) (n : ℕ) :
    (pairedEtaGeometricNormalizedSignedZeroPullback q T n).IsHermitian := by
  have hB : (pairedEtaGeometricSignedZeroPullback q T n).IsHermitian := by
    exact Matrix.isHermitian_conjTranspose_mul_mul _
      (pairedEtaTopPrefixFiniteZeroWindowBlock_isHermitian _ hT)
  have hKinv :
      ((pairedEtaGeometricMultiplicityWeightedZeroGram q
        (spectralZetaZeroWindow T) n)⁻¹).IsHermitian :=
    (pairedEtaGeometricMultiplicityWeightedZeroGram_posSemidef
      q (spectralZetaZeroWindow T) n).isHermitian.inv
  simpa [pairedEtaGeometricNormalizedSignedZeroPullback, hKinv.eq] using
    Matrix.isHermitian_conjTranspose_mul_mul
      (pairedEtaGeometricMultiplicityWeightedZeroGram q
        (spectralZetaZeroWindow T) n)⁻¹ hB

/-- Positive definiteness of the zero metric normalizes the upper order bound
to `1 - A >= 0`. -/
theorem one_sub_pairedEtaGeometricNormalizedSignedZeroPullback_posSemidef
    (q : ℕ) {T : ℝ} (hT : 0 ≤ T) (n : ℕ)
    (hK : (pairedEtaGeometricMultiplicityWeightedZeroGram q
      (spectralZetaZeroWindow T) n).PosDef) :
    (1 - pairedEtaGeometricNormalizedSignedZeroPullback q T n).PosSemidef := by
  let K := pairedEtaGeometricMultiplicityWeightedZeroGram q
    (spectralZetaZeroWindow T) n
  let B := pairedEtaGeometricSignedZeroPullback q T n
  have hbound : (K * K - B).PosSemidef := by
    simpa [K, B] using
      pairedEtaGeometricZeroGram_mul_self_sub_signedZeroPullback_posSemidef
        q hT n
  have hpull := hbound.conjTranspose_mul_mul_same K⁻¹
  have hK' : K.PosDef := by simpa [K] using hK
  let _ := hK'.isUnit.invertible
  have hKinv : K⁻¹.IsHermitian := hK'.isHermitian.inv
  simpa [pairedEtaGeometricNormalizedSignedZeroPullback, K, B, hKinv.eq,
    mul_sub, sub_mul, mul_assoc, Matrix.inv_mul_of_invertible,
    Matrix.mul_inv_of_invertible] using hpull

/-- Positive definiteness of the zero metric normalizes the lower order bound
to `1 + A >= 0`. -/
theorem one_add_pairedEtaGeometricNormalizedSignedZeroPullback_posSemidef
    (q : ℕ) {T : ℝ} (hT : 0 ≤ T) (n : ℕ)
    (hK : (pairedEtaGeometricMultiplicityWeightedZeroGram q
      (spectralZetaZeroWindow T) n).PosDef) :
    (1 + pairedEtaGeometricNormalizedSignedZeroPullback q T n).PosSemidef := by
  let K := pairedEtaGeometricMultiplicityWeightedZeroGram q
    (spectralZetaZeroWindow T) n
  let B := pairedEtaGeometricSignedZeroPullback q T n
  have hbound : (K * K + B).PosSemidef := by
    simpa [K, B] using
      pairedEtaGeometricZeroGram_mul_self_add_signedZeroPullback_posSemidef
        q hT n
  have hpull := hbound.conjTranspose_mul_mul_same K⁻¹
  have hK' : K.PosDef := by simpa [K] using hK
  let _ := hK'.isUnit.invertible
  have hKinv : K⁻¹.IsHermitian := hK'.isHermitian.inv
  simpa [pairedEtaGeometricNormalizedSignedZeroPullback, K, B, hKinv.eq,
    mul_add, add_mul, mul_assoc, Matrix.inv_mul_of_invertible,
    Matrix.mul_inv_of_invertible] using hpull

/-- At every separated geometric block, the normalized signed pullback is a
Hermitian contraction in the exact two-sided Loewner-order sense. -/
theorem pairedEtaGeometricNormalizedSignedZeroPullback_contraction
    (q : ℕ) {T : ℝ} (hT : 0 ≤ T) (n : ℕ)
    (hK : (pairedEtaGeometricMultiplicityWeightedZeroGram q
      (spectralZetaZeroWindow T) n).PosDef) :
    (pairedEtaGeometricNormalizedSignedZeroPullback q T n).IsHermitian ∧
      (1 - pairedEtaGeometricNormalizedSignedZeroPullback q T n).PosSemidef ∧
      (1 + pairedEtaGeometricNormalizedSignedZeroPullback q T n).PosSemidef :=
  ⟨pairedEtaGeometricNormalizedSignedZeroPullback_isHermitian q hT n,
    one_sub_pairedEtaGeometricNormalizedSignedZeroPullback_posSemidef q hT n hK,
    one_add_pairedEtaGeometricNormalizedSignedZeroPullback_posSemidef q hT n hK⟩

/-- Every nonnegative finite zeta-zero window has one odd prime base for
which every sufficiently late normalized signed zero-space pullback is a
Hermitian contraction. -/
theorem exists_prime_eventually_pairedEtaGeometricNormalizedSignedZeroPullback_contraction
    {T : ℝ} (hT : 0 ≤ T) :
    ∃ q : ℕ, q.Prime ∧ Odd q ∧ 1 < q ∧
      ∀ᶠ n in atTop,
        (pairedEtaGeometricNormalizedSignedZeroPullback q T n).IsHermitian ∧
          (1 - pairedEtaGeometricNormalizedSignedZeroPullback q T n).PosSemidef ∧
          (1 + pairedEtaGeometricNormalizedSignedZeroPullback q T n).PosSemidef := by
  obtain ⟨q, hqPrime, hqOdd, hq, hK⟩ :=
    exists_prime_eventually_posDef_pairedEtaGeometricMultiplicityWeightedZeroGram_and_inv
      (spectralZetaZeroWindow T)
  refine ⟨q, hqPrime, hqOdd, hq, ?_⟩
  filter_upwards [hK] with n hn
  exact pairedEtaGeometricNormalizedSignedZeroPullback_contraction q hT n hn.1

end

end RiemannGaussian
