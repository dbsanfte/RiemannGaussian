import RiemannGaussian.Hybrid.EtaGeometricReflectionAtomModel

/-!
# Coordinate heat for the reflection-even eta atom model

The normalized atom model is defined on the zero-index compression
`A₊ = E₊ K E₊`.  This module transports its complete nonzero spectrum back to
the actual packed eta coordinate space without losing the parity or colour
information that created it.

Writing `C` for the multiplicity-weighted eta synthesis matrix, set
`W = C E₊`.  Then Lean proves

`WᴴW = A₊`,

while the coordinate carrier `WWᴴ = C E₊ Cᴴ` is exactly the already checked
positive sum of the on-line and off-line-real eta blocks.  All positive-order
moments transfer exactly between the two Grams.  Ordinary heat transfers with
one explicit zero-padding correction because the coordinate space has twice
the ambient dimension.

The two coordinate colours remain separate on every edge of a new ordered
coloured-path expansion.  Consequently the heat observable whose crossing
would beat `13/18` is now an exact convergent series of literal even-length
eta paths, retaining intermediate coordinates and the on-line/off-line-real
choice at every step.  No heat crossing or improved zero proportion is proved
here.
-/

open Matrix Finset
open scoped BigOperators Classical ComplexConjugate ComplexOrder Matrix Real

namespace RiemannGaussian.HermitianRankTrace

noncomputable section

/-! ## Colour-resolved matrix paths -/

variable {R : Type*} [Semiring R]
variable {ι c : Type*} [Fintype ι] [DecidableEq ι] [Fintype c]

/-- The sum of ordered length-`k` paths through a finite family of coloured
matrix edges. Every successor step retains both its intermediate vertex and
its edge colour. -/
def matrixColouredPowerPathSum (A : c → Matrix ι ι R) :
    ℕ → ι → ι → R
  | 0, i, j => if i = j then 1 else 0
  | k + 1, i, j =>
      ∑ a, ∑ colour, matrixColouredPowerPathSum A k i a * A colour a j

/-- The colour-resolved path sum equals the corresponding power of the sum
of all colour matrices. -/
theorem matrixColouredPowerPathSum_eq_pow_sum
    (A : c → Matrix ι ι R) (k : ℕ) (i j : ι) :
    matrixColouredPowerPathSum A k i j =
      ((∑ colour, A colour) ^ k) i j := by
  induction k generalizing i j with
  | zero =>
      simp [matrixColouredPowerPathSum, Matrix.one_apply]
  | succ k ih =>
      simp only [matrixColouredPowerPathSum, pow_succ, Matrix.mul_apply, ih]
      apply Finset.sum_congr rfl
      intro a _ha
      rw [Matrix.sum_apply, Finset.mul_sum]

/-- The sum of all colour-resolved closed paths. -/
def matrixColouredClosedPathSum (A : c → Matrix ι ι R) (k : ℕ) : R :=
  ∑ i, matrixColouredPowerPathSum A k i i

/-- The colour-resolved closed-path sum is the trace of the corresponding
power of the summed carrier. -/
theorem matrixColouredClosedPathSum_eq_trace_pow_sum
    (A : c → Matrix ι ι R) (k : ℕ) :
    matrixColouredClosedPathSum A k =
      Matrix.trace ((∑ colour, A colour) ^ k) := by
  simp only [matrixColouredClosedPathSum, Matrix.trace, Matrix.diag,
    matrixColouredPowerPathSum_eq_pow_sum]

/-! ## Rectangular heat transfer -/

variable {K : Type*} [RCLike K]
variable {d e : Type*} [Fintype d] [DecidableEq d]
  [Fintype e] [DecidableEq e]

/-- Ordinary heat transfers across a rectangular matrix Gram after exactly
accounting for the different numbers of padded zero eigenvalues. -/
theorem hermitianHeatMomentTrace_zero_conjTranspose_mul_self
    (W : Matrix d e K) (u : ℝ) :
    hermitianHeatMomentTrace
        (Matrix.posSemidef_conjTranspose_mul_self W).isHermitian 0 u =
      hermitianHeatMomentTrace
          (Matrix.posSemidef_self_mul_conjTranspose W).isHermitian 0 u -
        Fintype.card d + Fintype.card e := by
  have htransfer := Multiplicity.sum_eigenvalues_comm W
    (fun x : ℝ ↦ Real.exp (-u * x ^ 2) - 1) (by simp)
  rw [hermitianHeatMomentTrace_eq_sum_eigenvalues,
    hermitianHeatMomentTrace_eq_sum_eigenvalues]
  simp only [pow_zero, one_mul]
  simp only [Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul,
    mul_one, Finset.card_univ] at htransfer
  linarith

/-- Hermitian heat-moment traces respect equality of their carrier matrices;
the Hermitian proof arguments are propositionally irrelevant. -/
theorem hermitianHeatMomentTrace_eq_of_eq
    {A B : Matrix d d K} (hA : A.IsHermitian) (hB : B.IsHermitian)
    (hAB : A = B) (order : ℕ) (u : ℝ) :
    hermitianHeatMomentTrace hA order u =
      hermitianHeatMomentTrace hB order u := by
  subst B
  rfl

end

end RiemannGaussian.HermitianRankTrace

namespace RiemannGaussian

noncomputable section

open HermitianRankTrace

/-- The eta synthesis matrix restricted to reflection-even zero-index
coefficients. -/
def pairedEtaGeometricReflectionEvenFeatureSynthesisMatrix
    (q : ℕ) (T : ℝ) (hT : 0 ≤ T) (n : ℕ) :
    Matrix
      (Fin (spectralZetaZeroWindow T).card × Fin 2)
      (Fin (spectralZetaZeroWindow T).card) ℂ :=
  pairedEtaGeometricMultiplicityWeightedFeatureSynthesisMatrix q
      (spectralZetaZeroWindow T) n *
    pairedEtaZeroWindowReflectionEvenProjection T hT

/-- The coordinate-space carrier of the reflection-even eta synthesis. -/
def pairedEtaGeometricReflectionEvenCoordinateCarrier
    (q : ℕ) (T : ℝ) (hT : 0 ≤ T) (n : ℕ) :
    Matrix
      (Fin (spectralZetaZeroWindow T).card × Fin 2)
      (Fin (spectralZetaZeroWindow T).card × Fin 2) ℂ :=
  pairedEtaGeometricReflectionEvenFeatureSynthesisMatrix q T hT n *
    (pairedEtaGeometricReflectionEvenFeatureSynthesisMatrix q T hT n)ᴴ

/-- The two information channels retained by the reflection-even coordinate
carrier: critical-line mass and off-line real mass. -/
def pairedEtaGeometricReflectionEvenCoordinateColourCarrier
    (q : ℕ) (T : ℝ) (n : ℕ) :
    Fin 2 → Matrix
      (Fin (spectralZetaZeroWindow T).card × Fin 2)
      (Fin (spectralZetaZeroWindow T).card × Fin 2) ℂ :=
  ![pairedEtaTopPrefixFiniteZeroWindowOnLineBlock
      (fun j : Fin (spectralZetaZeroWindow T).card ↦
        pairedEtaGeometricHyperbolicCutoff q n j) T,
    pairedEtaTopPrefixFiniteZeroWindowOffLineRealBlock
      (fun j : Fin (spectralZetaZeroWindow T).card ↦
        pairedEtaGeometricHyperbolicCutoff q n j) T]

/-- The zero-index Gram of the even synthesis is exactly `A₊ = E₊ K E₊`. -/
theorem pairedEtaGeometricReflectionEvenFeatureSynthesisMatrix_conjTranspose_mul_self
    (q : ℕ) (T : ℝ) (hT : 0 ≤ T) (n : ℕ) :
    (pairedEtaGeometricReflectionEvenFeatureSynthesisMatrix q T hT n)ᴴ *
        pairedEtaGeometricReflectionEvenFeatureSynthesisMatrix q T hT n =
      pairedEtaGeometricReflectionEvenCompressedZeroGram q T hT n := by
  unfold pairedEtaGeometricReflectionEvenFeatureSynthesisMatrix
    pairedEtaGeometricReflectionEvenCompressedZeroGram
    pairedEtaGeometricMultiplicityWeightedZeroGram
  rw [Matrix.conjTranspose_mul,
    (pairedEtaZeroWindowReflectionEvenProjection_isHermitian T hT).eq]
  simp only [Matrix.mul_assoc]

/-- The coordinate carrier is the direct compression `C E₊ Cᴴ`. -/
theorem pairedEtaGeometricReflectionEvenCoordinateCarrier_eq_synthesis_mul_projection_mul_conjTranspose
    (q : ℕ) (T : ℝ) (hT : 0 ≤ T) (n : ℕ) :
    pairedEtaGeometricReflectionEvenCoordinateCarrier q T hT n =
      pairedEtaGeometricMultiplicityWeightedFeatureSynthesisMatrix q
          (spectralZetaZeroWindow T) n *
        pairedEtaZeroWindowReflectionEvenProjection T hT *
        (pairedEtaGeometricMultiplicityWeightedFeatureSynthesisMatrix q
          (spectralZetaZeroWindow T) n)ᴴ := by
  let C := pairedEtaGeometricMultiplicityWeightedFeatureSynthesisMatrix q
    (spectralZetaZeroWindow T) n
  let E := pairedEtaZeroWindowReflectionEvenProjection T hT
  have hE := pairedEtaZeroWindowReflectionEvenProjection_isHermitian T hT
  have hE2 := pairedEtaZeroWindowReflectionEvenProjection_mul_self T hT
  unfold pairedEtaGeometricReflectionEvenCoordinateCarrier
    pairedEtaGeometricReflectionEvenFeatureSynthesisMatrix
  change (C * E) * (C * E)ᴴ = C * E * Cᴴ
  rw [Matrix.conjTranspose_mul, hE.eq]
  rw [Matrix.mul_assoc C E, ← Matrix.mul_assoc E E, hE2]
  exact (Matrix.mul_assoc C E Cᴴ).symm

/-- The reflection-even coordinate carrier is exactly the existing positive
on-line-plus-real eta colour block. -/
theorem pairedEtaGeometricReflectionEvenCoordinateCarrier_eq_onLine_add_offLineReal
    (q : ℕ) {T : ℝ} (hT : 0 ≤ T) (n : ℕ) :
    pairedEtaGeometricReflectionEvenCoordinateCarrier q T hT n =
      pairedEtaTopPrefixFiniteZeroWindowOnLineBlock
          (fun j : Fin (spectralZetaZeroWindow T).card ↦
            pairedEtaGeometricHyperbolicCutoff q n j) T +
        pairedEtaTopPrefixFiniteZeroWindowOffLineRealBlock
          (fun j : Fin (spectralZetaZeroWindow T).card ↦
            pairedEtaGeometricHyperbolicCutoff q n j) T := by
  let C := pairedEtaGeometricMultiplicityWeightedFeatureSynthesisMatrix q
    (spectralZetaZeroWindow T) n
  let P := pairedEtaZeroWindowConjugatePartnerMatrix T hT
  let H := pairedEtaTopPrefixFiniteZeroWindowHermitianGram
    (fun j : Fin (spectralZetaZeroWindow T).card ↦
      pairedEtaGeometricHyperbolicCutoff q n j) T
  let S := pairedEtaTopPrefixFiniteZeroWindowBlock
    (fun j : Fin (spectralZetaZeroWindow T).card ↦
      pairedEtaGeometricHyperbolicCutoff q n j) T
  have hCP : C * P * Cᴴ = S := by
    rw [Matrix.mul_assoc,
      pairedEtaZeroWindowConjugatePartnerMatrix_mul_synthesis_conjTranspose_eq_transpose
        q hT n]
    exact pairedEtaGeometricMultiplicityWeightedFeatureSynthesisMatrix_mul_transpose_eq_zeroWindowBlock
      q T n
  have hCC : C * Cᴴ = H := by
    exact pairedEtaGeometricMultiplicityWeightedCoordinateGram_eq_zeroWindowHermitianGram
      q T n
  rw [pairedEtaGeometricReflectionEvenCoordinateCarrier_eq_synthesis_mul_projection_mul_conjTranspose]
  change C * ((1 / 2 : ℂ) • (1 + P)) * Cᴴ = _
  calc
    C * ((1 / 2 : ℂ) • (1 + P)) * Cᴴ =
        (1 / 2 : ℂ) • (C * Cᴴ + C * P * Cᴴ) := by
      rw [Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_add,
        Matrix.mul_one, Matrix.add_mul]
    _ = (1 / 2 : ℂ) • (H + S) := by rw [hCC, hCP]
    _ = _ := by
      rw [pairedEtaTopPrefixFiniteZeroWindowHermitianGram_add_signedBlock_eq_two_onLine_add_real
        (fun j : Fin (spectralZetaZeroWindow T).card ↦
          pairedEtaGeometricHyperbolicCutoff q n j) hT]
      module

/-- Summing the two retained colour matrices recovers the reflection-even
coordinate carrier. -/
theorem sum_pairedEtaGeometricReflectionEvenCoordinateColourCarrier_eq
    (q : ℕ) {T : ℝ} (hT : 0 ≤ T) (n : ℕ) :
    (∑ colour, pairedEtaGeometricReflectionEvenCoordinateColourCarrier
      q T n colour) =
        pairedEtaGeometricReflectionEvenCoordinateCarrier q T hT n := by
  rw [Fin.sum_univ_two]
  exact
    (pairedEtaGeometricReflectionEvenCoordinateCarrier_eq_onLine_add_offLineReal
      q hT n).symm

/-- The reflection-even coordinate carrier is positive semidefinite. -/
theorem pairedEtaGeometricReflectionEvenCoordinateCarrier_posSemidef
    (q : ℕ) (T : ℝ) (hT : 0 ≤ T) (n : ℕ) :
    (pairedEtaGeometricReflectionEvenCoordinateCarrier q T hT n).PosSemidef :=
  Matrix.posSemidef_self_mul_conjTranspose _

/-- Complete ordered, colour-resolved closed paths through the literal
reflection-even eta coordinate carrier. -/
def pairedEtaGeometricReflectionEvenCoordinateColouredClosedPathSum
    (q : ℕ) (T : ℝ) (n order : ℕ) : ℂ :=
  matrixColouredClosedPathSum
    (pairedEtaGeometricReflectionEvenCoordinateColourCarrier q T n) order

/-- Every coordinate-carrier power trace is exactly the real part of its
ordered colour-resolved eta path sum. -/
theorem pairedEtaGeometricReflectionEvenCoordinateCarrier_rtrace_pow_eq_re_colouredClosedPathSum
    (q : ℕ) {T : ℝ} (hT : 0 ≤ T) (n order : ℕ) :
    rtrace ((pairedEtaGeometricReflectionEvenCoordinateCarrier
        q T hT n) ^ order) =
      (pairedEtaGeometricReflectionEvenCoordinateColouredClosedPathSum
        q T n order).re := by
  unfold pairedEtaGeometricReflectionEvenCoordinateColouredClosedPathSum
    rtrace
  rw [matrixColouredClosedPathSum_eq_trace_pow_sum,
    sum_pairedEtaGeometricReflectionEvenCoordinateColourCarrier_eq q hT n]
  rfl

/-- Ordinary heat on the reflection-even coordinate carrier is a convergent
series of all even-length ordered paths with on-line/off-line-real colour
retained on every edge. -/
theorem hasSum_pairedEtaGeometricReflectionEvenCoordinateCarrier_heatTrace_colouredClosedPaths
    (q : ℕ) {T : ℝ} (hT : 0 ≤ T) (n : ℕ) (u : ℝ) :
    HasSum
      (fun m : ℕ ↦ ((-u) ^ m / (m.factorial : ℝ)) *
        (pairedEtaGeometricReflectionEvenCoordinateColouredClosedPathSum
          q T n (2 * m)).re)
      (hermitianHeatMomentTrace
        (pairedEtaGeometricReflectionEvenCoordinateCarrier_posSemidef
          q T hT n).isHermitian 0 u) := by
  simpa only [zero_add,
    pairedEtaGeometricReflectionEvenCoordinateCarrier_rtrace_pow_eq_re_colouredClosedPathSum]
    using hasSum_hermitianHeatMomentTrace_rtrace_powers
      (pairedEtaGeometricReflectionEvenCoordinateCarrier_posSemidef
        q T hT n).isHermitian 0 u

/-- Every positive-order atom moment transfers exactly from the zero-index
compression to the literal on-line-plus-real coordinate carrier. -/
theorem pairedEtaGeometricReflectionEvenAtomModel_moment_succ_eq_coordinate_rtrace_pow
    (q : ℕ) {T : ℝ} (hT : 0 ≤ T) (n order : ℕ)
    (hwindow : (spectralZetaZeroWindow T).Nonempty)
    (hK : (pairedEtaGeometricMultiplicityWeightedZeroGram q
      (spectralZetaZeroWindow T) n).PosDef) :
    (pairedEtaGeometricReflectionEvenAtomModel
        q hT n hwindow hK).moment (order + 1) =
      (1 / ((spectralZetaZeroWindow T).card : ℝ)) *
        (((spectralZetaZeroWindow T).card : ℝ) /
          rtrace (pairedEtaGeometricReflectionEvenCompressedZeroGram
            q T hT n)) ^ (order + 1) *
        rtrace ((pairedEtaGeometricReflectionEvenCoordinateCarrier
          q T hT n) ^ (order + 1)) := by
  rw [pairedEtaGeometricReflectionEvenAtomModel_moment_eq_rtrace_pow]
  congr 1
  let W := pairedEtaGeometricReflectionEvenFeatureSynthesisMatrix q T hT n
  have hgram : Wᴴ * W =
      pairedEtaGeometricReflectionEvenCompressedZeroGram q T hT n :=
    pairedEtaGeometricReflectionEvenFeatureSynthesisMatrix_conjTranspose_mul_self
      q T hT n
  have hcoord : W * Wᴴ =
      pairedEtaGeometricReflectionEvenCoordinateCarrier q T hT n := rfl
  have htrace := Multiplicity.trace_pow_succ_comm W order
  unfold rtrace
  rw [← hgram, ← hcoord]
  exact congrArg RCLike.re htrace.symm

/-- Ordinary heat on `A₊` is ordinary heat on the literal coordinate carrier
minus exactly one ambient zero-padding copy of the zero-window cardinality. -/
theorem pairedEtaGeometricReflectionEvenCompressedZeroGram_heatTrace_eq_coordinateCarrier_sub_card
    (q : ℕ) {T : ℝ} (hT : 0 ≤ T) (n : ℕ) (u : ℝ) :
    hermitianHeatMomentTrace
        (pairedEtaGeometricReflectionEvenCompressedZeroGram_posSemidef
          q T hT n).isHermitian 0 u =
      hermitianHeatMomentTrace
          (pairedEtaGeometricReflectionEvenCoordinateCarrier_posSemidef
            q T hT n).isHermitian 0 u -
        (spectralZetaZeroWindow T).card := by
  let W := pairedEtaGeometricReflectionEvenFeatureSynthesisMatrix q T hT n
  let A := pairedEtaGeometricReflectionEvenCompressedZeroGram q T hT n
  let B := pairedEtaGeometricReflectionEvenCoordinateCarrier q T hT n
  have hgram : Wᴴ * W = A :=
    pairedEtaGeometricReflectionEvenFeatureSynthesisMatrix_conjTranspose_mul_self
      q T hT n
  have hcoord : W * Wᴴ = B := rfl
  let hA := pairedEtaGeometricReflectionEvenCompressedZeroGram_posSemidef
    q T hT n
  let hB := pairedEtaGeometricReflectionEvenCoordinateCarrier_posSemidef
    q T hT n
  calc
    hermitianHeatMomentTrace hA.isHermitian 0 u =
        hermitianHeatMomentTrace
          (Matrix.posSemidef_conjTranspose_mul_self W).isHermitian 0 u :=
      hermitianHeatMomentTrace_eq_of_eq hA.isHermitian
        (Matrix.posSemidef_conjTranspose_mul_self W).isHermitian hgram.symm 0 u
    _ = hermitianHeatMomentTrace
          (Matrix.posSemidef_self_mul_conjTranspose W).isHermitian 0 u -
        Fintype.card (Fin (spectralZetaZeroWindow T).card × Fin 2) +
        Fintype.card (Fin (spectralZetaZeroWindow T).card) :=
      hermitianHeatMomentTrace_zero_conjTranspose_mul_self W u
    _ = hermitianHeatMomentTrace hB.isHermitian 0 u -
        (spectralZetaZeroWindow T).card := by
      rw [hermitianHeatMomentTrace_eq_of_eq
        (Matrix.posSemidef_self_mul_conjTranspose W).isHermitian
        hB.isHermitian hcoord 0 u]
      simp only [Fintype.card_prod, Fintype.card_fin]
      push_cast
      ring

/-- The literal critical fraction beats `13/18` exactly when the
on-line-plus-real coordinate heat, after its exact padding correction,
crosses the normalized `5/36` threshold. -/
theorem pairedEtaGeometricReflectionEvenAtomModel_thirteen_eighteen_lt_criticalFraction_iff_exists_coordinateHeat
    (q : ℕ) {T : ℝ} (hT : 0 ≤ T) (n : ℕ)
    (hwindow : (spectralZetaZeroWindow T).Nonempty)
    (hK : (pairedEtaGeometricMultiplicityWeightedZeroGram q
      (spectralZetaZeroWindow T) n).PosDef) :
    (13 : ℝ) / 18 <
        (spectralCriticalZetaZeroWindow T).card /
          (spectralZetaZeroWindow T).card ↔
      ∃ u : ℝ, 0 ≤ u ∧
        (1 / ((spectralZetaZeroWindow T).card : ℝ)) *
          (hermitianHeatMomentTrace
              (pairedEtaGeometricReflectionEvenCoordinateCarrier_posSemidef
                q T hT n).isHermitian 0
              (u * (((spectralZetaZeroWindow T).card : ℝ) /
                rtrace (pairedEtaGeometricReflectionEvenCompressedZeroGram
                  q T hT n)) ^ 2) -
            (spectralZetaZeroWindow T).card) < (5 : ℝ) / 36 := by
  rw [pairedEtaGeometricReflectionEvenAtomModel_thirteen_eighteen_lt_criticalFraction_iff_exists_rtrace_heat
    q hT n hwindow hK]
  apply exists_congr
  intro u
  apply and_congr_right
  intro _hu
  rw [pairedEtaGeometricReflectionEvenCompressedZeroGram_heatTrace_eq_coordinateCarrier_sub_card]

/-- Terminal colour-resolved coordinate-heat interface. The complete even
path series and the exact `13/18` crossing criterion are simultaneously
available on the same literal eta carrier. -/
theorem pairedEtaGeometricReflectionEvenCoordinateHeatCertificateInterface
    (q : ℕ) {T : ℝ} (hT : 0 ≤ T) (n : ℕ)
    (hwindow : (spectralZetaZeroWindow T).Nonempty)
    (hK : (pairedEtaGeometricMultiplicityWeightedZeroGram q
      (spectralZetaZeroWindow T) n).PosDef) :
    (∀ v : ℝ,
      HasSum
        (fun m : ℕ ↦ ((-v) ^ m / (m.factorial : ℝ)) *
          (pairedEtaGeometricReflectionEvenCoordinateColouredClosedPathSum
            q T n (2 * m)).re)
        (hermitianHeatMomentTrace
          (pairedEtaGeometricReflectionEvenCoordinateCarrier_posSemidef
            q T hT n).isHermitian 0 v)) ∧
      ((13 : ℝ) / 18 <
          (spectralCriticalZetaZeroWindow T).card /
            (spectralZetaZeroWindow T).card ↔
        ∃ u : ℝ, 0 ≤ u ∧
          (1 / ((spectralZetaZeroWindow T).card : ℝ)) *
            (hermitianHeatMomentTrace
                (pairedEtaGeometricReflectionEvenCoordinateCarrier_posSemidef
                  q T hT n).isHermitian 0
                (u * (((spectralZetaZeroWindow T).card : ℝ) /
                  rtrace (pairedEtaGeometricReflectionEvenCompressedZeroGram
                    q T hT n)) ^ 2) -
              (spectralZetaZeroWindow T).card) < (5 : ℝ) / 36) := by
  exact
    ⟨fun v ↦
      hasSum_pairedEtaGeometricReflectionEvenCoordinateCarrier_heatTrace_colouredClosedPaths
        q hT n v,
      pairedEtaGeometricReflectionEvenAtomModel_thirteen_eighteen_lt_criticalFraction_iff_exists_coordinateHeat
        q hT n hwindow hK⟩

end

end RiemannGaussian
