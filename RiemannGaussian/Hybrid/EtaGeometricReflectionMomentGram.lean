import RiemannGaussian.Hybrid.EtaGeometricReflectionSupport

/-!
# Positive Hankel Grams for the supported mixed eta moments

The support construction gives a Hermitian carrier `S` and a positive
projection `Q` with `QS = SQ = S`.  This module turns the complete supported
moment sequence into an actual Gram matrix.

For a chosen finite family of orders `k_i`, flatten the supported powers
`Q S^(k_i)` into columns.  Their ordinary Hermitian column Gram is positive
semidefinite, and its `(i,j)` entry is exactly

`Re tr(Q S^(k_i+k_j)) = Re tr((P K)^(k_i+k_j))`.

Consequently every finite Hankel matrix drawn from the mixed reflection
moments is positive semidefinite.  A second congruence gives the canonical
dimensionless normalization: total mass is divided by the represented-zero
count and the spectral coordinate is scaled by the mean positive eta mass.
This supplies the positive normalized moment interface required by the
certificate program.  It does not supply the still-open eta-arithmetic bounds
on those moments.
-/

open Complex
open scoped BigOperators Classical ComplexConjugate ComplexOrder Matrix

namespace RiemannGaussian

noncomputable section

namespace HermitianRankTrace

variable {d r : Type*} [Fintype d] [DecidableEq d]
variable [Fintype r] [DecidableEq r]

/-- Flatten a finite family of square complex matrices into the columns of
one synthesis matrix. -/
def matrixFamilyFlatten (F : r → Matrix d d ℂ) : Matrix (d × d) r ℂ :=
  fun ab i ↦ F i ab.1 ab.2

omit [DecidableEq d] [Fintype r] [DecidableEq r] in
/-- The column Gram of flattened matrices is their Frobenius trace Gram. -/
theorem matrixFamilyFlatten_conjTranspose_mul_apply
    (F : r → Matrix d d ℂ) (i j : r) :
    ((matrixFamilyFlatten F)ᴴ * matrixFamilyFlatten F) i j =
      ((F i)ᴴ * F j).trace := by
  simp only [matrixFamilyFlatten, Matrix.mul_apply,
    Matrix.conjTranspose_apply, Matrix.trace, Matrix.diag_apply,
    Fintype.sum_prod_type]
  rw [Finset.sum_comm]

end HermitianRankTrace

/-- The flattened supported matrix power of one selected order. -/
def pairedEtaGeometricReflectionSupportedPowerFeature
    (q : ℕ) (T : ℝ) (n r : ℕ) :
    Matrix
      (Fin (spectralZetaZeroWindow T).card × Fin 2)
      (Fin (spectralZetaZeroWindow T).card × Fin 2) ℂ :=
  pairedEtaGeometricReflectionSupportProjection q T n *
    pairedEtaGeometricReflectionHermitianCarrier q T n ^ r

/-- Every two supported power features have Frobenius product equal to the
supported power at the sum of their orders. -/
theorem pairedEtaGeometricReflectionSupportedPowerFeature_conjTranspose_mul
    (q : ℕ) {T : ℝ} (hT : 0 ≤ T) (n r s : ℕ)
    (hK : (pairedEtaGeometricMultiplicityWeightedZeroGram q
      (spectralZetaZeroWindow T) n).PosDef) :
    (pairedEtaGeometricReflectionSupportedPowerFeature q T n r)ᴴ *
        pairedEtaGeometricReflectionSupportedPowerFeature q T n s =
      pairedEtaGeometricReflectionSupportProjection q T n *
        pairedEtaGeometricReflectionHermitianCarrier q T n ^ (r + s) := by
  let Q := pairedEtaGeometricReflectionSupportProjection q T n
  let S := pairedEtaGeometricReflectionHermitianCarrier q T n
  have hQ : Q.IsHermitian := by
    simpa [Q] using
      pairedEtaGeometricReflectionSupportProjection_isHermitian q T n hK
  have hS : S.IsHermitian := by
    simpa [S] using
      pairedEtaGeometricReflectionHermitianCarrier_isHermitian q hT n
  have hQ2 : Q * Q = Q := by
    simpa [Q] using
      pairedEtaGeometricReflectionSupportProjection_mul_self q T n hK
  have hcomm : Commute Q S := by
    simpa [Q, S] using
      pairedEtaGeometricReflectionSupportProjection_commute_carrier q hT n hK
  change (Q * S ^ r)ᴴ * (Q * S ^ s) = Q * S ^ (r + s)
  simp only [Matrix.conjTranspose_mul, hQ.eq, (hS.pow r).eq]
  calc
    (S ^ r * Q) * (Q * S ^ s) = S ^ r * (Q * Q) * S ^ s := by
      noncomm_ring
    _ = S ^ r * Q * S ^ s := by rw [hQ2]
    _ = Q * S ^ r * S ^ s := by
      rw [← (hcomm.pow_right r).eq]
    _ = Q * S ^ (r + s) := by
      simp only [pow_add, Matrix.mul_assoc]

/-- Flattened supported powers at arbitrary selected orders. -/
def pairedEtaGeometricReflectionSupportedPowerSynthesis
    {r : Type*}
    (q : ℕ) (T : ℝ) (n : ℕ) (order : r → ℕ) :
    Matrix
      ((Fin (spectralZetaZeroWindow T).card × Fin 2) ×
        (Fin (spectralZetaZeroWindow T).card × Fin 2)) r ℂ :=
  HermitianRankTrace.matrixFamilyFlatten fun i ↦
    pairedEtaGeometricReflectionSupportedPowerFeature q T n (order i)

/-- The complete supported mixed-moment Hankel Gram. -/
def pairedEtaGeometricReflectionSupportedMomentGram
    {r : Type*}
    (q : ℕ) (T : ℝ) (n : ℕ) (order : r → ℕ) : Matrix r r ℂ :=
  (pairedEtaGeometricReflectionSupportedPowerSynthesis q T n order)ᴴ *
    pairedEtaGeometricReflectionSupportedPowerSynthesis q T n order

/-- Every finite supported mixed-moment Hankel Gram is positive
semidefinite. -/
theorem pairedEtaGeometricReflectionSupportedMomentGram_posSemidef
    {r : Type*} [Fintype r]
    (q : ℕ) (T : ℝ) (n : ℕ) (order : r → ℕ) :
    (pairedEtaGeometricReflectionSupportedMomentGram q T n order).PosSemidef :=
  Matrix.posSemidef_conjTranspose_mul_self _

/-- A supported moment is a genuinely real trace of the commuting Hermitian
support and carrier. -/
theorem ofReal_pairedEtaGeometricReflectionSupportedMoment_eq_trace
    (q : ℕ) {T : ℝ} (hT : 0 ≤ T) (n r : ℕ)
    (hK : (pairedEtaGeometricMultiplicityWeightedZeroGram q
      (spectralZetaZeroWindow T) n).PosDef) :
    (pairedEtaGeometricReflectionSupportedMoment q T n r : ℂ) =
      (pairedEtaGeometricReflectionSupportProjection q T n *
        pairedEtaGeometricReflectionHermitianCarrier q T n ^ r).trace := by
  let Q := pairedEtaGeometricReflectionSupportProjection q T n
  let S := pairedEtaGeometricReflectionHermitianCarrier q T n
  have hQ : Q.IsHermitian := by
    simpa [Q] using
      pairedEtaGeometricReflectionSupportProjection_isHermitian q T n hK
  have hS : S.IsHermitian := by
    simpa [S] using
      pairedEtaGeometricReflectionHermitianCarrier_isHermitian q hT n
  have hcomm : Commute Q S := by
    simpa [Q, S] using
      pairedEtaGeometricReflectionSupportProjection_commute_carrier q hT n hK
  have hQS : (Q * S ^ r).IsHermitian :=
    (hQ.commute_iff (hS.pow r)).mp (hcomm.pow_right r)
  unfold pairedEtaGeometricReflectionSupportedMoment
  change (((Q * S ^ r).trace.re : ℝ) : ℂ) = (Q * S ^ r).trace
  rw [hQS.trace_eq_sum_eigenvalues]
  simp

/-- Every Hankel-Gram entry is exactly the corresponding mixed reflection
moment, not merely an abstract matrix coefficient. -/
theorem pairedEtaGeometricReflectionSupportedMomentGram_apply
    {r : Type*}
    (q : ℕ) {T : ℝ} (hT : 0 ≤ T) (n : ℕ) (order : r → ℕ)
    (i j : r)
    (hK : (pairedEtaGeometricMultiplicityWeightedZeroGram q
      (spectralZetaZeroWindow T) n).PosDef) :
    pairedEtaGeometricReflectionSupportedMomentGram q T n order i j =
      (pairedEtaGeometricReflectionMixedMoment q T hT n
        (order i + order j) : ℂ) := by
  unfold pairedEtaGeometricReflectionSupportedMomentGram
    pairedEtaGeometricReflectionSupportedPowerSynthesis
  rw [HermitianRankTrace.matrixFamilyFlatten_conjTranspose_mul_apply]
  rw [pairedEtaGeometricReflectionSupportedPowerFeature_conjTranspose_mul
    q hT n (order i) (order j) hK]
  rw [← ofReal_pairedEtaGeometricReflectionSupportedMoment_eq_trace
    q hT n (order i + order j) hK]
  rw [pairedEtaGeometricReflectionSupportedMoment_eq_mixedMoment
    q hT n (order i + order j) hK]

/-! ## Canonical dimensionless normalization -/

/-- Normalize the supported moment mass to one and scale its spectral
coordinate by the reciprocal mean positive eta trace mass. -/
def pairedEtaGeometricReflectionNormalizedMixedMoment
    (q : ℕ) (T : ℝ) (hT : 0 ≤ T) (n r : ℕ) : ℝ :=
  ((spectralZetaZeroWindow T).card : ℝ)⁻¹ *
    (((spectralZetaZeroWindow T).card : ℝ) /
      pairedEtaGeometricZeroGramTraceMass q T n) ^ r *
    pairedEtaGeometricReflectionMixedMoment q T hT n r

/-- Diagonal order scaling used to normalize the complete Hankel Gram. -/
def pairedEtaGeometricReflectionMomentScaleDiagonal
    {r : Type*} [DecidableEq r]
    (q : ℕ) (T : ℝ) (n : ℕ) (order : r → ℕ) : Matrix r r ℂ :=
  Matrix.diagonal fun i ↦
    ((((spectralZetaZeroWindow T).card : ℝ) /
      pairedEtaGeometricZeroGramTraceMass q T n) ^ order i : ℂ)

/-- The real diagonal order scaling is Hermitian. -/
theorem pairedEtaGeometricReflectionMomentScaleDiagonal_isHermitian
    {r : Type*} [DecidableEq r]
    (q : ℕ) (T : ℝ) (n : ℕ) (order : r → ℕ) :
    (pairedEtaGeometricReflectionMomentScaleDiagonal q T n order).IsHermitian := by
  rw [Matrix.IsHermitian]
  ext i j
  by_cases hij : i = j
  · subst j
    simp [pairedEtaGeometricReflectionMomentScaleDiagonal]
  · have hji : j ≠ i := Ne.symm hij
    simp [pairedEtaGeometricReflectionMomentScaleDiagonal, hij, hji]

/-- The normalized supported Hankel Gram. -/
def pairedEtaGeometricReflectionNormalizedMomentGram
    {r : Type*} [Fintype r] [DecidableEq r]
    (q : ℕ) (T : ℝ) (n : ℕ) (order : r → ℕ) : Matrix r r ℂ :=
  ((spectralZetaZeroWindow T).card : ℝ)⁻¹ •
    ((pairedEtaGeometricReflectionMomentScaleDiagonal q T n order)ᴴ *
      pairedEtaGeometricReflectionSupportedMomentGram q T n order *
      pairedEtaGeometricReflectionMomentScaleDiagonal q T n order)

/-- Every finite normalized mixed-moment Hankel Gram remains positive
semidefinite. -/
theorem pairedEtaGeometricReflectionNormalizedMomentGram_posSemidef
    {r : Type*} [Fintype r] [DecidableEq r]
    (q : ℕ) (T : ℝ) (n : ℕ) (order : r → ℕ) :
    (pairedEtaGeometricReflectionNormalizedMomentGram q T n order).PosSemidef := by
  unfold pairedEtaGeometricReflectionNormalizedMomentGram
  apply
    ((pairedEtaGeometricReflectionSupportedMomentGram_posSemidef
        q T n order).conjTranspose_mul_mul_same
      (pairedEtaGeometricReflectionMomentScaleDiagonal q T n order)).smul
  exact inv_nonneg.mpr (Nat.cast_nonneg _)

/-- Every normalized Hankel-Gram entry is the normalized mixed moment at the
sum of its selected orders. -/
theorem pairedEtaGeometricReflectionNormalizedMomentGram_apply
    {r : Type*} [Fintype r] [DecidableEq r]
    (q : ℕ) {T : ℝ} (hT : 0 ≤ T) (n : ℕ) (order : r → ℕ)
    (i j : r)
    (hK : (pairedEtaGeometricMultiplicityWeightedZeroGram q
      (spectralZetaZeroWindow T) n).PosDef) :
    pairedEtaGeometricReflectionNormalizedMomentGram q T n order i j =
      (pairedEtaGeometricReflectionNormalizedMixedMoment q T hT n
        (order i + order j) : ℂ) := by
  unfold pairedEtaGeometricReflectionNormalizedMomentGram
  rw [(pairedEtaGeometricReflectionMomentScaleDiagonal_isHermitian
    q T n order).eq]
  unfold pairedEtaGeometricReflectionMomentScaleDiagonal
  simp only [Matrix.smul_apply, Matrix.mul_diagonal, Matrix.diagonal_mul,
    Complex.real_smul]
  rw [pairedEtaGeometricReflectionSupportedMomentGram_apply
    q hT n order i j hK]
  unfold pairedEtaGeometricReflectionNormalizedMixedMoment
  push_cast
  rw [pow_add]
  ring

/-- The normalized Gram is simultaneously positive semidefinite and
entrywise identical to the complete normalized mixed-moment Hankel matrix. -/
theorem pairedEtaGeometricReflectionNormalizedMomentGram_posSemidef_and_apply
    {r : Type*} [Fintype r] [DecidableEq r]
    (q : ℕ) {T : ℝ} (hT : 0 ≤ T) (n : ℕ) (order : r → ℕ)
    (hK : (pairedEtaGeometricMultiplicityWeightedZeroGram q
      (spectralZetaZeroWindow T) n).PosDef) :
    (pairedEtaGeometricReflectionNormalizedMomentGram q T n order).PosSemidef ∧
      ∀ i j,
        pairedEtaGeometricReflectionNormalizedMomentGram q T n order i j =
          (pairedEtaGeometricReflectionNormalizedMixedMoment q T hT n
            (order i + order j) : ℂ) := by
  exact
    ⟨pairedEtaGeometricReflectionNormalizedMomentGram_posSemidef q T n order,
      fun i j ↦ pairedEtaGeometricReflectionNormalizedMomentGram_apply
        q hT n order i j hK⟩

/-- On a nonempty window the normalized zeroth moment is one. -/
@[simp]
theorem pairedEtaGeometricReflectionNormalizedMixedMoment_zero
    (q : ℕ) {T : ℝ} (hT : 0 ≤ T) (n : ℕ)
    (hwindow : (spectralZetaZeroWindow T).Nonempty) :
    pairedEtaGeometricReflectionNormalizedMixedMoment q T hT n 0 = 1 := by
  have hcard : ((spectralZetaZeroWindow T).card : ℝ) ≠ 0 := by
    exact_mod_cast Finset.card_ne_zero.mpr hwindow
  rw [pairedEtaGeometricReflectionNormalizedMixedMoment,
    pairedEtaGeometricReflectionMixedMoment_zero q hT n]
  field_simp

/-- On a nonempty separated window the normalized first moment is exactly the
previous information-preserving signed-to-positive trace balance. -/
theorem pairedEtaGeometricReflectionNormalizedMixedMoment_one
    (q : ℕ) {T : ℝ} (hT : 0 ≤ T) (n : ℕ)
    (hwindow : (spectralZetaZeroWindow T).Nonempty)
    (hK : (pairedEtaGeometricMultiplicityWeightedZeroGram q
      (spectralZetaZeroWindow T) n).PosDef) :
    pairedEtaGeometricReflectionNormalizedMixedMoment q T hT n 1 =
      pairedEtaGeometricReflectionTraceBalance q T hT n := by
  have hcard : ((spectralZetaZeroWindow T).card : ℝ) ≠ 0 := by
    exact_mod_cast Finset.card_ne_zero.mpr hwindow
  have hmass : pairedEtaGeometricZeroGramTraceMass q T n ≠ 0 :=
    (pairedEtaGeometricZeroGramTraceMass_pos q n hwindow hK).ne'
  rw [pairedEtaGeometricReflectionNormalizedMixedMoment,
    pairedEtaGeometricReflectionMixedMoment_one q hT n]
  unfold pairedEtaGeometricReflectionTraceBalance
  field_simp

/-- Every two selected orders obey the normalized Hankel Cauchy--Schwarz
inequality.  This is the first certificate-facing consequence of the complete
positive moment Gram. -/
theorem pairedEtaGeometricReflectionNormalizedMixedMoment_sq_le_even_mul_even
    (q : ℕ) {T : ℝ} (hT : 0 ≤ T) (n a b : ℕ)
    (hK : (pairedEtaGeometricMultiplicityWeightedZeroGram q
      (spectralZetaZeroWindow T) n).PosDef) :
    pairedEtaGeometricReflectionNormalizedMixedMoment q T hT n (a + b) ^ 2 ≤
      pairedEtaGeometricReflectionNormalizedMixedMoment q T hT n (2 * a) *
        pairedEtaGeometricReflectionNormalizedMixedMoment q T hT n (2 * b) := by
  let order : Fin 2 → ℕ := ![a, b]
  let G := pairedEtaGeometricReflectionNormalizedMomentGram q T n order
  have hdet : (0 : ℂ) ≤ G.det :=
    (pairedEtaGeometricReflectionNormalizedMomentGram_posSemidef
      q T n order).det_nonneg
  have h00 := pairedEtaGeometricReflectionNormalizedMomentGram_apply
    q hT n order (0 : Fin 2) (0 : Fin 2) hK
  have h01 := pairedEtaGeometricReflectionNormalizedMomentGram_apply
    q hT n order (0 : Fin 2) (1 : Fin 2) hK
  have h10 := pairedEtaGeometricReflectionNormalizedMomentGram_apply
    q hT n order (1 : Fin 2) (0 : Fin 2) hK
  have h11 := pairedEtaGeometricReflectionNormalizedMomentGram_apply
    q hT n order (1 : Fin 2) (1 : Fin 2) hK
  dsimp only [G] at hdet
  rw [Matrix.det_fin_two, h00, h01, h10, h11] at hdet
  have hdet' : (0 : ℂ) ≤
      ((pairedEtaGeometricReflectionNormalizedMixedMoment q T hT n (2 * a) *
          pairedEtaGeometricReflectionNormalizedMixedMoment q T hT n (2 * b) -
        pairedEtaGeometricReflectionNormalizedMixedMoment q T hT n (a + b) ^ 2 :
        ℝ) : ℂ) := by
    simpa [order, pow_two, two_mul, add_comm] using hdet
  exact sub_nonneg.mp (Complex.zero_le_real.mp hdet')

end

end RiemannGaussian
