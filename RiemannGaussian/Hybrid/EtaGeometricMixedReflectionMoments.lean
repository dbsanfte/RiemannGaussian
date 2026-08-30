import RiemannGaussian.Hybrid.EtaGeometricMixedReflectionTrace
import RiemannGaussian.Hybrid.EtaSpectralHeatClosedPaths

/-!
# Ordered mixed reflection moments for geometric eta features

The scalar `Re tr(P K)` retains the first coupling between critical-line
reflection `P` and the positive eta metric `K`.  This module keeps the entire
ordered word before any spectral or norm collapse.

For geometric blocks `n` and `m`, the cross-scale carrier is

`P (C_nᴴ C_m) = C_nᵀ C_m`.

Each entry is therefore an explicit complex-symmetric correlation of two
actual multiplicity-weighted packed eta features, at their respective scales.
At equal scales this is `P K`.  Lean defines every real moment
`Re tr((P K)^r)` and expands it into the complete ordered closed path sum on
zero-index space.  The edge expansion retains zero labels, analytic
multiplicity, phase, cutoff scale, and path order.

The module also retains the two-step cross-scale word and proves its symmetry
under exchanging the two scales.  These are exact finite identities, not an
arithmetic estimate or a stronger zero proportion.
-/

open Complex
open scoped BigOperators Classical ComplexConjugate ComplexOrder Matrix

namespace RiemannGaussian

noncomputable section

/-- Reflection-coupled cross-scale zero-index matrix. -/
def pairedEtaGeometricReflectionCrossScaleMatrix
    (q : ℕ) (T : ℝ) (hT : 0 ≤ T) (n m : ℕ) :
    Matrix (Fin (spectralZetaZeroWindow T).card)
      (Fin (spectralZetaZeroWindow T).card) ℂ :=
  pairedEtaZeroWindowConjugatePartnerMatrix T hT *
    ((pairedEtaGeometricMultiplicityWeightedFeatureSynthesisMatrix q
        (spectralZetaZeroWindow T) n)ᴴ *
      pairedEtaGeometricMultiplicityWeightedFeatureSynthesisMatrix q
        (spectralZetaZeroWindow T) m)

/-- Moving reflection through the left synthesis factor converts the
cross-scale carrier to the ordinary-transpose product `C_nᵀ C_m`. -/
theorem pairedEtaGeometricReflectionCrossScaleMatrix_eq_transpose_mul_synthesis
    (q : ℕ) {T : ℝ} (hT : 0 ≤ T) (n m : ℕ) :
    pairedEtaGeometricReflectionCrossScaleMatrix q T hT n m =
      (pairedEtaGeometricMultiplicityWeightedFeatureSynthesisMatrix q
          (spectralZetaZeroWindow T) n)ᵀ *
        pairedEtaGeometricMultiplicityWeightedFeatureSynthesisMatrix q
          (spectralZetaZeroWindow T) m := by
  rw [pairedEtaGeometricReflectionCrossScaleMatrix, ← Matrix.mul_assoc,
    pairedEtaZeroWindowConjugatePartnerMatrix_mul_synthesis_conjTranspose_eq_transpose
      q hT n]

/-- One ordered, phase-preserving cross-scale edge between two enumerated
zeros. -/
def pairedEtaGeometricReflectionCrossScaleEdge
    (q : ℕ) (T : ℝ) (n m : ℕ)
    (i j : Fin (spectralZetaZeroWindow T).card) : ℂ :=
  ∑ a : Fin (spectralZetaZeroWindow T).card × Fin 2,
    pairedEtaGeometricMultiplicityWeightedFeatureSynthesisMatrix q
        (spectralZetaZeroWindow T) n a i *
      pairedEtaGeometricMultiplicityWeightedFeatureSynthesisMatrix q
        (spectralZetaZeroWindow T) m a j

/-- Every cross-scale matrix entry is its literal ordered eta edge. -/
theorem pairedEtaGeometricReflectionCrossScaleMatrix_apply_eq_edge
    (q : ℕ) {T : ℝ} (hT : 0 ≤ T) (n m : ℕ)
    (i j : Fin (spectralZetaZeroWindow T).card) :
    pairedEtaGeometricReflectionCrossScaleMatrix q T hT n m i j =
      pairedEtaGeometricReflectionCrossScaleEdge q T n m i j := by
  rw [pairedEtaGeometricReflectionCrossScaleMatrix_eq_transpose_mul_synthesis
    q hT n m]
  rfl

/-- The edge exposes both square-root multiplicity weights and the complete
same-coordinate correlation of the actual packed eta features. -/
theorem pairedEtaGeometricReflectionCrossScaleEdge_eq_weight_mul_weight_mul_sum
    (q : ℕ) (T : ℝ) (n m : ℕ)
    (i j : Fin (spectralZetaZeroWindow T).card) :
    pairedEtaGeometricReflectionCrossScaleEdge q T n m i j =
      pairedEtaGeometricMultiplicitySqrtWeight
          ((etaZeroWindowEquivFin (spectralZetaZeroWindow T)).symm i) *
        pairedEtaGeometricMultiplicitySqrtWeight
          ((etaZeroWindowEquivFin (spectralZetaZeroWindow T)).symm j) *
        ∑ a : Fin (spectralZetaZeroWindow T).card × Fin 2,
          pairedEtaGeometricPackedHyperbolicFeature q
              (spectralZetaZeroWindow T) n i a *
            pairedEtaGeometricPackedHyperbolicFeature q
              (spectralZetaZeroWindow T) m j a := by
  change
    (∑ a,
      (pairedEtaGeometricMultiplicitySqrtWeight
          ((etaZeroWindowEquivFin (spectralZetaZeroWindow T)).symm i) *
        pairedEtaGeometricPackedHyperbolicFeature q
          (spectralZetaZeroWindow T) n i a) *
      (pairedEtaGeometricMultiplicitySqrtWeight
          ((etaZeroWindowEquivFin (spectralZetaZeroWindow T)).symm j) *
        pairedEtaGeometricPackedHyperbolicFeature q
          (spectralZetaZeroWindow T) m j a)) = _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a _ha
  ring

/-- Reversing both scale order and zero-edge orientation preserves the
complex-symmetric cross-scale edge. -/
theorem pairedEtaGeometricReflectionCrossScaleEdge_swap
    (q : ℕ) (T : ℝ) (n m : ℕ)
    (i j : Fin (spectralZetaZeroWindow T).card) :
    pairedEtaGeometricReflectionCrossScaleEdge q T n m i j =
      pairedEtaGeometricReflectionCrossScaleEdge q T m n j i := by
  unfold pairedEtaGeometricReflectionCrossScaleEdge
  apply Finset.sum_congr rfl
  intro a _ha
  ring

/-- The transpose of an ordered cross-scale carrier reverses its scales. -/
theorem pairedEtaGeometricReflectionCrossScaleMatrix_transpose
    (q : ℕ) {T : ℝ} (hT : 0 ≤ T) (n m : ℕ) :
    (pairedEtaGeometricReflectionCrossScaleMatrix q T hT n m)ᵀ =
      pairedEtaGeometricReflectionCrossScaleMatrix q T hT m n := by
  ext i j
  rw [Matrix.transpose_apply,
    pairedEtaGeometricReflectionCrossScaleMatrix_apply_eq_edge,
    pairedEtaGeometricReflectionCrossScaleMatrix_apply_eq_edge,
    pairedEtaGeometricReflectionCrossScaleEdge_swap]

/-- At equal scales the cross-scale carrier is exactly the mixed matrix
`P K`. -/
theorem pairedEtaGeometricReflectionCrossScaleMatrix_self
    (q : ℕ) {T : ℝ} (hT : 0 ≤ T) (n : ℕ) :
    pairedEtaGeometricReflectionCrossScaleMatrix q T hT n n =
      pairedEtaZeroWindowConjugatePartnerMatrix T hT *
        pairedEtaGeometricMultiplicityWeightedZeroGram q
          (spectralZetaZeroWindow T) n := by
  rfl

/-- The order-`r` mixed reflection moment at one geometric scale. -/
def pairedEtaGeometricReflectionMixedMoment
    (q : ℕ) (T : ℝ) (hT : 0 ≤ T) (n r : ℕ) : ℝ :=
  ((pairedEtaGeometricReflectionCrossScaleMatrix q T hT n n) ^ r).trace.re

/-- The complete complex sum of ordered length-`r` closed paths through the
zero-index mixed eta carrier. -/
def pairedEtaGeometricReflectionMixedClosedPathSum
    (q : ℕ) (T : ℝ) (n r : ℕ) : ℂ :=
  HermitianRankTrace.matrixClosedPathSum
    (fun i j ↦ pairedEtaGeometricReflectionCrossScaleEdge q T n n i j) r

/-- Every mixed moment is exactly the real part of its complete ordered
closed eta path sum. -/
theorem pairedEtaGeometricReflectionMixedMoment_eq_re_closedPathSum
    (q : ℕ) {T : ℝ} (hT : 0 ≤ T) (n r : ℕ) :
    pairedEtaGeometricReflectionMixedMoment q T hT n r =
      (pairedEtaGeometricReflectionMixedClosedPathSum q T n r).re := by
  have hmatrix :
      (fun i j ↦ pairedEtaGeometricReflectionCrossScaleEdge q T n n i j) =
        pairedEtaGeometricReflectionCrossScaleMatrix q T hT n n := by
    ext i j
    exact (pairedEtaGeometricReflectionCrossScaleMatrix_apply_eq_edge
      q hT n n i j).symm
  unfold pairedEtaGeometricReflectionMixedMoment
    pairedEtaGeometricReflectionMixedClosedPathSum
  rw [hmatrix, HermitianRankTrace.matrixClosedPathSum_eq_trace_pow]

/-- The zeroth mixed moment is the number of represented distinct zeros. -/
theorem pairedEtaGeometricReflectionMixedMoment_zero
    (q : ℕ) {T : ℝ} (hT : 0 ≤ T) (n : ℕ) :
    pairedEtaGeometricReflectionMixedMoment q T hT n 0 =
      (spectralZetaZeroWindow T).card := by
  simp [pairedEtaGeometricReflectionMixedMoment, Matrix.trace_one]

/-- The first mixed moment recovers the checked amplitude-sensitive mixed
trace. -/
theorem pairedEtaGeometricReflectionMixedMoment_one
    (q : ℕ) {T : ℝ} (hT : 0 ≤ T) (n : ℕ) :
    pairedEtaGeometricReflectionMixedMoment q T hT n 1 =
      pairedEtaGeometricReflectionMixedTrace q T hT n := by
  simp [pairedEtaGeometricReflectionMixedMoment,
    pairedEtaGeometricReflectionMixedTrace,
    HermitianInertia.rtrace,
    pairedEtaGeometricReflectionCrossScaleMatrix_self]

/-- A successor mixed closed-path sum exposes its base and penultimate zero
indices before either sum is collapsed. -/
theorem pairedEtaGeometricReflectionMixedClosedPathSum_succ
    (q : ℕ) (T : ℝ) (n r : ℕ) :
    pairedEtaGeometricReflectionMixedClosedPathSum q T n (r + 1) =
      ∑ i, ∑ j,
        HermitianRankTrace.matrixPowerPathSum
            (fun a b ↦ pairedEtaGeometricReflectionCrossScaleEdge q T n n a b)
            r i j *
          pairedEtaGeometricReflectionCrossScaleEdge q T n n j i := by
  exact HermitianRankTrace.matrixClosedPathSum_succ _ r

/-- Real trace of the ordered two-step cross-scale word. -/
def pairedEtaGeometricReflectionCrossScaleTwoStepMoment
    (q : ℕ) (T : ℝ) (hT : 0 ≤ T) (n m : ℕ) : ℝ :=
  (pairedEtaGeometricReflectionCrossScaleMatrix q T hT n m *
    pairedEtaGeometricReflectionCrossScaleMatrix q T hT m n).trace.re

/-- The two-step cross-scale moment is symmetric under exchanging its two
scales. -/
theorem pairedEtaGeometricReflectionCrossScaleTwoStepMoment_comm
    (q : ℕ) {T : ℝ} (hT : 0 ≤ T) (n m : ℕ) :
    pairedEtaGeometricReflectionCrossScaleTwoStepMoment q T hT n m =
      pairedEtaGeometricReflectionCrossScaleTwoStepMoment q T hT m n := by
  unfold pairedEtaGeometricReflectionCrossScaleTwoStepMoment
  rw [Matrix.trace_mul_comm]

/-- At equal scales the cross-scale two-step word is the second mixed
reflection moment. -/
theorem pairedEtaGeometricReflectionCrossScaleTwoStepMoment_self
    (q : ℕ) {T : ℝ} (hT : 0 ≤ T) (n : ℕ) :
    pairedEtaGeometricReflectionCrossScaleTwoStepMoment q T hT n n =
      pairedEtaGeometricReflectionMixedMoment q T hT n 2 := by
  simp only [pairedEtaGeometricReflectionCrossScaleTwoStepMoment,
    pairedEtaGeometricReflectionMixedMoment, pow_two]

/-- The two-step cross-scale moment is the real part of the literal ordered
double-edge sum, with both scales and both zero indices retained. -/
theorem pairedEtaGeometricReflectionCrossScaleTwoStepMoment_eq_re_sum_edges
    (q : ℕ) {T : ℝ} (hT : 0 ≤ T) (n m : ℕ) :
    pairedEtaGeometricReflectionCrossScaleTwoStepMoment q T hT n m =
      (∑ i, ∑ j,
        pairedEtaGeometricReflectionCrossScaleEdge q T n m i j *
          pairedEtaGeometricReflectionCrossScaleEdge q T m n j i).re := by
  unfold pairedEtaGeometricReflectionCrossScaleTwoStepMoment Matrix.trace
  simp only [Matrix.diag_apply, Matrix.mul_apply,
    pairedEtaGeometricReflectionCrossScaleMatrix_apply_eq_edge]

end

end RiemannGaussian
