import RiemannGaussian.Hybrid.EtaGeometricMixedReflectionMoments

/-!
# The positive support behind the mixed eta reflection moments

The ordered zero-index carrier `P K` is generally not Hermitian in the
ordinary Euclidean metric.  It nevertheless has an exact Hermitian
realization on the packed eta coordinate space.  If `C` is the actual
multiplicity-weighted synthesis matrix, `K = Cᴴ C`, and `P` is critical-line
reflection, set

`S = C P Cᴴ` and `Q = C K⁻¹ Cᴴ`.

The existing reflection identity identifies `S` with the literal signed eta
window.  Whenever `K` is positive definite, Lean proves that `Q` is positive
semidefinite and idempotent, that it supports `S` on both sides, and that its
trace is the number of represented distinct zeros.  Thus `Q` removes exactly
the artificial zero eigenspace introduced by the packed coordinate
realization.

For every order, including order zero, the complete supported Hermitian
moment

`Re tr(Q S^r)`

is exactly the ordered mixed reflection moment `Re tr((P K)^r)`.  This is a
finite algebraic identity.  It retains the eta amplitudes in `K`; it does not
assert an arithmetic estimate or an improved zero proportion.
-/

open Complex
open scoped BigOperators Classical ComplexConjugate ComplexOrder Matrix

namespace RiemannGaussian

noncomputable section

namespace HermitianRankTrace

variable {R m n : Type*} [CommSemiring R]
variable [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n]

/-- Rectangular cyclicity for every positive matrix-power trace. -/
theorem trace_pow_succ_mul_comm_rect
    (A : Matrix m n R) (B : Matrix n m R) (r : ℕ) :
    ((A * B) ^ (r + 1)).trace = ((B * A) ^ (r + 1)).trace := by
  have hpower : ∀ k : ℕ,
      (A * B) ^ (k + 1) = A * (B * A) ^ k * B := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
        rw [pow_succ, ih, pow_succ]
        simp only [Matrix.mul_assoc]
  rw [hpower, Matrix.mul_assoc, Matrix.trace_mul_comm,
    Matrix.mul_assoc, ← pow_succ]

end HermitianRankTrace

/-- The literal signed eta window, regarded as the Hermitian coordinate-space
realization of the mixed reflection carrier. -/
def pairedEtaGeometricReflectionHermitianCarrier
    (q : ℕ) (T : ℝ) (n : ℕ) :
    Matrix
      (Fin (spectralZetaZeroWindow T).card × Fin 2)
      (Fin (spectralZetaZeroWindow T).card × Fin 2) ℂ :=
  pairedEtaTopPrefixFiniteZeroWindowBlock
    (fun j : Fin (spectralZetaZeroWindow T).card ↦
      pairedEtaGeometricHyperbolicCutoff q n j) T

/-- The coordinate-space support projection induced by the positive
zero-index Gram. -/
def pairedEtaGeometricReflectionSupportProjection
    (q : ℕ) (T : ℝ) (n : ℕ) :
    Matrix
      (Fin (spectralZetaZeroWindow T).card × Fin 2)
      (Fin (spectralZetaZeroWindow T).card × Fin 2) ℂ :=
  let C := pairedEtaGeometricMultiplicityWeightedFeatureSynthesisMatrix q
    (spectralZetaZeroWindow T) n
  let K := pairedEtaGeometricMultiplicityWeightedZeroGram q
    (spectralZetaZeroWindow T) n
  C * K⁻¹ * Cᴴ

/-- The literal signed coordinate carrier factors as `C P Cᴴ`. -/
theorem pairedEtaGeometricReflectionHermitianCarrier_eq_synthesis_mul_partner_mul_conjTranspose
    (q : ℕ) {T : ℝ} (hT : 0 ≤ T) (n : ℕ) :
    pairedEtaGeometricReflectionHermitianCarrier q T n =
      pairedEtaGeometricMultiplicityWeightedFeatureSynthesisMatrix q
          (spectralZetaZeroWindow T) n *
        pairedEtaZeroWindowConjugatePartnerMatrix T hT *
        (pairedEtaGeometricMultiplicityWeightedFeatureSynthesisMatrix q
          (spectralZetaZeroWindow T) n)ᴴ := by
  rw [pairedEtaGeometricReflectionHermitianCarrier,
    ← pairedEtaGeometricMultiplicityWeightedFeatureSynthesisMatrix_mul_transpose_eq_zeroWindowBlock]
  rw [← pairedEtaZeroWindowConjugatePartnerMatrix_mul_synthesis_conjTranspose_eq_transpose
    q hT n]
  simp only [Matrix.mul_assoc]

/-- The coordinate carrier is Hermitian on every nonnegative symmetric
spectral window. -/
theorem pairedEtaGeometricReflectionHermitianCarrier_isHermitian
    (q : ℕ) {T : ℝ} (hT : 0 ≤ T) (n : ℕ) :
    (pairedEtaGeometricReflectionHermitianCarrier q T n).IsHermitian := by
  exact pairedEtaTopPrefixFiniteZeroWindowBlock_isHermitian
    (fun j : Fin (spectralZetaZeroWindow T).card ↦
      pairedEtaGeometricHyperbolicCutoff q n j) hT

/-- Positive definiteness of `K` makes the induced coordinate support
positive semidefinite. -/
theorem pairedEtaGeometricReflectionSupportProjection_posSemidef
    (q : ℕ) (T : ℝ) (n : ℕ)
    (hK : (pairedEtaGeometricMultiplicityWeightedZeroGram q
      (spectralZetaZeroWindow T) n).PosDef) :
    (pairedEtaGeometricReflectionSupportProjection q T n).PosSemidef := by
  let C := pairedEtaGeometricMultiplicityWeightedFeatureSynthesisMatrix q
    (spectralZetaZeroWindow T) n
  let K := pairedEtaGeometricMultiplicityWeightedZeroGram q
    (spectralZetaZeroWindow T) n
  change (C * K⁻¹ * Cᴴ).PosSemidef
  have hK' : K.PosDef := by simpa [K] using hK
  exact hK'.inv.posSemidef.mul_mul_conjTranspose_same C

/-- The support projection is Hermitian. -/
theorem pairedEtaGeometricReflectionSupportProjection_isHermitian
    (q : ℕ) (T : ℝ) (n : ℕ)
    (hK : (pairedEtaGeometricMultiplicityWeightedZeroGram q
      (spectralZetaZeroWindow T) n).PosDef) :
    (pairedEtaGeometricReflectionSupportProjection q T n).IsHermitian :=
  (pairedEtaGeometricReflectionSupportProjection_posSemidef q T n hK).isHermitian

/-- The induced coordinate support is an idempotent. -/
theorem pairedEtaGeometricReflectionSupportProjection_mul_self
    (q : ℕ) (T : ℝ) (n : ℕ)
    (hK : (pairedEtaGeometricMultiplicityWeightedZeroGram q
      (spectralZetaZeroWindow T) n).PosDef) :
    pairedEtaGeometricReflectionSupportProjection q T n *
        pairedEtaGeometricReflectionSupportProjection q T n =
      pairedEtaGeometricReflectionSupportProjection q T n := by
  let C := pairedEtaGeometricMultiplicityWeightedFeatureSynthesisMatrix q
    (spectralZetaZeroWindow T) n
  let K := pairedEtaGeometricMultiplicityWeightedZeroGram q
    (spectralZetaZeroWindow T) n
  have hK' : K.PosDef := by simpa [K] using hK
  let _ := hK'.isUnit.invertible
  have hCK : Cᴴ * C = K := by rfl
  change (C * K⁻¹ * Cᴴ) * (C * K⁻¹ * Cᴴ) = C * K⁻¹ * Cᴴ
  calc
    (C * K⁻¹ * Cᴴ) * (C * K⁻¹ * Cᴴ) =
        C * K⁻¹ * (Cᴴ * C) * K⁻¹ * Cᴴ := by
      simp only [Matrix.mul_assoc]
    _ = C * K⁻¹ * K * K⁻¹ * Cᴴ := by rw [hCK]
    _ = C * K⁻¹ * Cᴴ := by
      rw [Matrix.mul_assoc C K⁻¹ K, Matrix.inv_mul_of_invertible]
      simp

/-- The support projection has trace equal to the number of represented
distinct zeros. -/
theorem pairedEtaGeometricReflectionSupportProjection_trace
    (q : ℕ) (T : ℝ) (n : ℕ)
    (hK : (pairedEtaGeometricMultiplicityWeightedZeroGram q
      (spectralZetaZeroWindow T) n).PosDef) :
    (pairedEtaGeometricReflectionSupportProjection q T n).trace =
      ((spectralZetaZeroWindow T).card : ℂ) := by
  let C := pairedEtaGeometricMultiplicityWeightedFeatureSynthesisMatrix q
    (spectralZetaZeroWindow T) n
  let K := pairedEtaGeometricMultiplicityWeightedZeroGram q
    (spectralZetaZeroWindow T) n
  have hK' : K.PosDef := by simpa [K] using hK
  let _ := hK'.isUnit.invertible
  have hCK : Cᴴ * C = K := by rfl
  change (C * K⁻¹ * Cᴴ).trace = _
  calc
    (C * K⁻¹ * Cᴴ).trace = (Cᴴ * (C * K⁻¹)).trace := by
      rw [Matrix.trace_mul_comm]
    _ = ((Cᴴ * C) * K⁻¹).trace := by
      simp only [Matrix.mul_assoc]
    _ = (K * K⁻¹).trace := by rw [hCK]
    _ = (1 : Matrix (Fin (spectralZetaZeroWindow T).card)
        (Fin (spectralZetaZeroWindow T).card) ℂ).trace := by
      rw [Matrix.mul_inv_of_invertible]
    _ = ((spectralZetaZeroWindow T).card : ℂ) := by
      simp [Matrix.trace_one]

/-- The support projection acts as the identity on the carrier from the
left. -/
theorem pairedEtaGeometricReflectionSupportProjection_mul_carrier
    (q : ℕ) {T : ℝ} (hT : 0 ≤ T) (n : ℕ)
    (hK : (pairedEtaGeometricMultiplicityWeightedZeroGram q
      (spectralZetaZeroWindow T) n).PosDef) :
    pairedEtaGeometricReflectionSupportProjection q T n *
        pairedEtaGeometricReflectionHermitianCarrier q T n =
      pairedEtaGeometricReflectionHermitianCarrier q T n := by
  rw [pairedEtaGeometricReflectionHermitianCarrier_eq_synthesis_mul_partner_mul_conjTranspose
    q hT n]
  let C := pairedEtaGeometricMultiplicityWeightedFeatureSynthesisMatrix q
    (spectralZetaZeroWindow T) n
  let K := pairedEtaGeometricMultiplicityWeightedZeroGram q
    (spectralZetaZeroWindow T) n
  let P := pairedEtaZeroWindowConjugatePartnerMatrix T hT
  have hK' : K.PosDef := by simpa [K] using hK
  let _ := hK'.isUnit.invertible
  have hCK : Cᴴ * C = K := by rfl
  change (C * K⁻¹ * Cᴴ) * (C * P * Cᴴ) = C * P * Cᴴ
  calc
    (C * K⁻¹ * Cᴴ) * (C * P * Cᴴ) =
        C * K⁻¹ * (Cᴴ * C) * P * Cᴴ := by
      simp only [Matrix.mul_assoc]
    _ = C * K⁻¹ * K * P * Cᴴ := by rw [hCK]
    _ = C * P * Cᴴ := by
      rw [Matrix.mul_assoc C K⁻¹ K, Matrix.inv_mul_of_invertible]
      simp

/-- The support projection acts as the identity on the carrier from the
right. -/
theorem pairedEtaGeometricReflectionHermitianCarrier_mul_supportProjection
    (q : ℕ) {T : ℝ} (hT : 0 ≤ T) (n : ℕ)
    (hK : (pairedEtaGeometricMultiplicityWeightedZeroGram q
      (spectralZetaZeroWindow T) n).PosDef) :
    pairedEtaGeometricReflectionHermitianCarrier q T n *
        pairedEtaGeometricReflectionSupportProjection q T n =
      pairedEtaGeometricReflectionHermitianCarrier q T n := by
  rw [pairedEtaGeometricReflectionHermitianCarrier_eq_synthesis_mul_partner_mul_conjTranspose
    q hT n]
  let C := pairedEtaGeometricMultiplicityWeightedFeatureSynthesisMatrix q
    (spectralZetaZeroWindow T) n
  let K := pairedEtaGeometricMultiplicityWeightedZeroGram q
    (spectralZetaZeroWindow T) n
  let P := pairedEtaZeroWindowConjugatePartnerMatrix T hT
  have hK' : K.PosDef := by simpa [K] using hK
  let _ := hK'.isUnit.invertible
  have hCK : Cᴴ * C = K := by rfl
  change (C * P * Cᴴ) * (C * K⁻¹ * Cᴴ) = C * P * Cᴴ
  calc
    (C * P * Cᴴ) * (C * K⁻¹ * Cᴴ) =
        C * P * (Cᴴ * C) * K⁻¹ * Cᴴ := by
      simp only [Matrix.mul_assoc]
    _ = C * P * K * K⁻¹ * Cᴴ := by rw [hCK]
    _ = C * P * Cᴴ := by
      rw [Matrix.mul_assoc (C * P) K K⁻¹,
        Matrix.mul_inv_of_invertible]
      simp

/-- The support projection and Hermitian carrier commute. -/
theorem pairedEtaGeometricReflectionSupportProjection_commute_carrier
    (q : ℕ) {T : ℝ} (hT : 0 ≤ T) (n : ℕ)
    (hK : (pairedEtaGeometricMultiplicityWeightedZeroGram q
      (spectralZetaZeroWindow T) n).PosDef) :
    Commute
      (pairedEtaGeometricReflectionSupportProjection q T n)
      (pairedEtaGeometricReflectionHermitianCarrier q T n) := by
  rw [commute_iff_eq]
  rw [pairedEtaGeometricReflectionSupportProjection_mul_carrier q hT n hK,
    pairedEtaGeometricReflectionHermitianCarrier_mul_supportProjection q hT n hK]

/-- Every positive carrier power is supported on the left by `Q`. -/
theorem pairedEtaGeometricReflectionSupportProjection_mul_carrier_pow_succ
    (q : ℕ) {T : ℝ} (hT : 0 ≤ T) (n r : ℕ)
    (hK : (pairedEtaGeometricMultiplicityWeightedZeroGram q
      (spectralZetaZeroWindow T) n).PosDef) :
    pairedEtaGeometricReflectionSupportProjection q T n *
        pairedEtaGeometricReflectionHermitianCarrier q T n ^ (r + 1) =
      pairedEtaGeometricReflectionHermitianCarrier q T n ^ (r + 1) := by
  rw [pow_succ']
  simp only [← Matrix.mul_assoc,
    pairedEtaGeometricReflectionSupportProjection_mul_carrier q hT n hK]

/-- The supported coordinate-space moment sequence. -/
def pairedEtaGeometricReflectionSupportedMoment
    (q : ℕ) (T : ℝ) (n r : ℕ) : ℝ :=
  (pairedEtaGeometricReflectionSupportProjection q T n *
    pairedEtaGeometricReflectionHermitianCarrier q T n ^ r).trace.re

/-- Every positive-order mixed zero-index moment is the corresponding trace
of the literal Hermitian coordinate carrier. -/
theorem pairedEtaGeometricReflectionMixedMoment_succ_eq_carrier_rtrace
    (q : ℕ) {T : ℝ} (hT : 0 ≤ T) (n r : ℕ) :
    pairedEtaGeometricReflectionMixedMoment q T hT n (r + 1) =
      (pairedEtaGeometricReflectionHermitianCarrier q T n ^ (r + 1)).trace.re := by
  let C := pairedEtaGeometricMultiplicityWeightedFeatureSynthesisMatrix q
    (spectralZetaZeroWindow T) n
  unfold pairedEtaGeometricReflectionMixedMoment
  rw [pairedEtaGeometricReflectionCrossScaleMatrix_eq_transpose_mul_synthesis
    q hT n n]
  rw [pairedEtaGeometricReflectionHermitianCarrier,
    ← pairedEtaGeometricMultiplicityWeightedFeatureSynthesisMatrix_mul_transpose_eq_zeroWindowBlock]
  exact congrArg Complex.re
    (HermitianRankTrace.trace_pow_succ_mul_comm_rect C Cᵀ r).symm

/-- The support trace supplies the correct zeroth moment, and all positive
orders agree by rectangular trace cyclicity. -/
theorem pairedEtaGeometricReflectionSupportedMoment_eq_mixedMoment
    (q : ℕ) {T : ℝ} (hT : 0 ≤ T) (n r : ℕ)
    (hK : (pairedEtaGeometricMultiplicityWeightedZeroGram q
      (spectralZetaZeroWindow T) n).PosDef) :
    pairedEtaGeometricReflectionSupportedMoment q T n r =
      pairedEtaGeometricReflectionMixedMoment q T hT n r := by
  cases r with
  | zero =>
      rw [pairedEtaGeometricReflectionMixedMoment_zero q hT n]
      unfold pairedEtaGeometricReflectionSupportedMoment
      simp only [pow_zero, Matrix.mul_one]
      rw [pairedEtaGeometricReflectionSupportProjection_trace q T n hK]
      simp
  | succ r =>
      unfold pairedEtaGeometricReflectionSupportedMoment
      rw [pairedEtaGeometricReflectionSupportProjection_mul_carrier_pow_succ
        q hT n r hK]
      exact (pairedEtaGeometricReflectionMixedMoment_succ_eq_carrier_rtrace
        q hT n r).symm

end

end RiemannGaussian
