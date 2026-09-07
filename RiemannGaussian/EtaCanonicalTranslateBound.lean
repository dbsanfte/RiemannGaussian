import RiemannGaussian.EtaCanonicalTranslateMatrix
import RiemannGaussian.EtaCurrentTranslatedProjectionPower

/-!
# Complete residual bounds for an exact eta coefficient law

The regularized Gram inverse supplies an exact coefficient vector for
every finite family of nonnegative translates. Its diagonal cost bounds
the original full coefficient norm tail. The complete continuous residual
is therefore at most the explicit resolvent deficit `1-b dot A^{-1}b`.
This is a proved all-family estimate, not a proof that the deficits vanish.
-/

open Complex Matrix MeasureTheory Set
open scoped Matrix

namespace RiemannGaussian

noncomputable section

/-- The exact quadratic objective including a proved majorant for the entire omitted tail. -/
def pairedEtaTranslateRidgeObjective {d : ℕ} (N : ℕ) (a : Fin d → ℝ) (c : Fin d → ℝ) : ℝ :=
  1 + dotProduct c (pairedEtaRegularizedTranslateGram N a *ᵥ c) -
    2 * dotProduct (pairedEtaTranslateTargetVector a) c

/-- The exact resolvent deficit for the mathematically defined coefficient vector. -/
def pairedEtaCanonicalTranslateBudget {d : ℕ} (N : ℕ) (a : Fin d → ℝ) : ℝ :=
  1 - dotProduct (pairedEtaTranslateTargetVector a) (pairedEtaCanonicalTranslateCoefficient N a)

/-- Finite Cauchy--Schwarz retains the complete original coefficient norm tail with an explicit dimension cost. -/
theorem pairedEtaTranslate_tail_le_regularization {d : ℕ} (N : ℕ) (c : Fin d → ℝ) :
    (∑ j, |c j|) ^ 2 / (2 * N + 1 : ℝ) ≤
      pairedEtaTranslateRegularization d N * ∑ j, c j ^ 2 := by
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ : Finset (Fin d)) (fun j ↦ |c j|) (fun _ ↦ (1 : ℝ))
  simp only [mul_one, one_pow, sq_abs, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul, mul_one] at hcs
  have hs : 0 ≤ ∑ j, c j ^ 2 := Finset.sum_nonneg (fun _ _ ↦ sq_nonneg _)
  have h : (∑ j, |c j|) ^ 2 ≤ (d + 1 : ℝ) * ∑ j, c j ^ 2 := by nlinarith
  calc
    _ ≤ ((d + 1 : ℝ) * ∑ j, c j ^ 2) / (2 * N + 1 : ℝ) :=
      div_le_div_of_nonneg_right h (by positivity)
    _ = _ := by unfold pairedEtaTranslateRegularization; ring

/-- The literal finite budget is its unchanged matrix energy, signed target pairing, and full coefficient norm tail. -/
theorem pairedEtaTranslatedFiniteResidualBudget_eq_realMatrix {d : ℕ} (N : ℕ)
    (a : Fin d → ℝ) (c : Fin d → ℝ) :
    pairedEtaTranslatedFiniteResidualBudget N a (fun j ↦ (c j : ℂ)) =
      1 + dotProduct c (pairedEtaTranslateGramMatrix N a *ᵥ c) -
        2 * dotProduct (pairedEtaTranslateTargetVector a) c +
        (∑ j, |c j|) ^ 2 / (2 * N + 1 : ℝ) := by
  unfold pairedEtaTranslatedFiniteResidualBudget pairedEtaTranslatedFiniteResidualForm
  simp only [Complex.conj_ofReal, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    mul_zero, sub_zero, Complex.norm_real, Real.norm_eq_abs]
  have hquad : (∑ j, ∑ k, c j * c k * pairedEtaTranslatedFiniteGram N
      (Real.log (2 * N + 1 : ℝ)) (a j) (a k)) =
      dotProduct c (pairedEtaTranslateGramMatrix N a *ᵥ c) := by
    simp only [dotProduct, Matrix.mulVec, pairedEtaTranslateGramMatrix, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    apply Finset.sum_congr rfl
    intro k _
    ring
  rw [hquad]
  congr 2
  simp only [dotProduct, pairedEtaTranslateTargetVector, mul_comm]

/-- The regularized actual Gram adds exactly its diagonal coefficient-square allowance. -/
theorem pairedEtaRegularizedTranslateGram_energy {d : ℕ} (N : ℕ)
    (a : Fin d → ℝ) (c : Fin d → ℝ) :
    dotProduct c (pairedEtaRegularizedTranslateGram N a *ᵥ c) =
      dotProduct c (pairedEtaTranslateGramMatrix N a *ᵥ c) +
        pairedEtaTranslateRegularization d N * ∑ j, c j ^ 2 := by
  simp only [pairedEtaRegularizedTranslateGram, Matrix.add_mulVec, Matrix.smul_mulVec,
    Matrix.one_mulVec, dotProduct_add, dotProduct_smul, smul_eq_mul]
  congr 1
  simp only [dotProduct, pow_two]

/-- The exact ridge objective controls the full original finite budget for every real coefficient vector. -/
theorem pairedEtaTranslatedFiniteResidualBudget_le_ridgeObjective {d : ℕ} (N : ℕ)
    (a : Fin d → ℝ) (c : Fin d → ℝ) :
    pairedEtaTranslatedFiniteResidualBudget N a (fun j ↦ (c j : ℂ)) ≤
      pairedEtaTranslateRidgeObjective N a c := by
  rw [pairedEtaTranslatedFiniteResidualBudget_eq_realMatrix, pairedEtaTranslateRidgeObjective,
    pairedEtaRegularizedTranslateGram_energy]
  linarith [pairedEtaTranslate_tail_le_regularization N c]

/-- The exact normal equations evaluate the objective at the canonical coefficient vector. -/
theorem pairedEtaTranslateRidgeObjective_canonical {d : ℕ} (N : ℕ) {a : Fin d → ℝ}
    (ha : ∀ j, 0 ≤ a j) :
    pairedEtaTranslateRidgeObjective N a (pairedEtaCanonicalTranslateCoefficient N a) =
      pairedEtaCanonicalTranslateBudget N a := by
  rw [pairedEtaTranslateRidgeObjective, pairedEtaCanonicalTranslateCoefficient_normal N ha,
    dotProduct_comm (pairedEtaCanonicalTranslateCoefficient N a), pairedEtaCanonicalTranslateBudget]
  ring

/-- Every trial coefficient vector retains an exact nonnegative quadratic remainder above the canonical resolvent deficit. -/
theorem pairedEtaTranslateRidgeObjective_eq_canonical_add_square {d : ℕ} (N : ℕ) {a : Fin d → ℝ}
    (ha : ∀ j, 0 ≤ a j) (c : Fin d → ℝ) :
    pairedEtaTranslateRidgeObjective N a c = pairedEtaCanonicalTranslateBudget N a +
      dotProduct (c - pairedEtaCanonicalTranslateCoefficient N a)
        (pairedEtaRegularizedTranslateGram N a *ᵥ (c - pairedEtaCanonicalTranslateCoefficient N a)) := by
  let A := pairedEtaRegularizedTranslateGram N a
  let u := pairedEtaCanonicalTranslateCoefficient N a
  let b := pairedEtaTranslateTargetVector a
  have hn : A *ᵥ u = b := pairedEtaCanonicalTranslateCoefficient_normal N ha
  have hsym : Aᵀ = A := by
    ext j k
    have h := congrArg (fun M : Matrix (Fin d) (Fin d) ℝ ↦ M j k)
      (pairedEtaRegularizedTranslateGram_posDef N ha).isHermitian
    simpa only [Matrix.conjTranspose_apply, star_trivial, Matrix.transpose_apply] using h
  have hcross : dotProduct u (A *ᵥ c) = dotProduct b c := by
    have h := Matrix.dotProduct_transpose_mulVec A u c
    rw [hsym, hn, dotProduct_comm c b] at h
    exact h
  change 1 + dotProduct c (A *ᵥ c) - 2 * dotProduct b c =
    (1 - dotProduct b u) + dotProduct (c - u) (A *ᵥ (c - u))
  rw [Matrix.mulVec_sub, dotProduct_sub, sub_dotProduct, sub_dotProduct, hn, hcross,
    dotProduct_comm c b, dotProduct_comm u b]
  ring

/-- The exact canonical rule minimizes the full regularized objective, so structured trial coefficients can bound its deficit. -/
theorem pairedEtaCanonicalTranslateBudget_le_trial {d : ℕ} (N : ℕ) {a : Fin d → ℝ}
    (ha : ∀ j, 0 ≤ a j) (c : Fin d → ℝ) :
    pairedEtaCanonicalTranslateBudget N a ≤ pairedEtaTranslateRidgeObjective N a c := by
  rw [pairedEtaTranslateRidgeObjective_eq_canonical_add_square N ha c]
  have h := (pairedEtaRegularizedTranslateGram_posDef N ha).posSemidef.dotProduct_mulVec_nonneg
    (c - pairedEtaCanonicalTranslateCoefficient N a)
  rw [star_trivial] at h
  linarith

/-- The defined coefficient family has a complete finite budget controlled by its exact resolvent deficit. -/
theorem pairedEtaCanonicalTranslate_finiteBudget_le {d : ℕ} (N : ℕ) {a : Fin d → ℝ}
    (ha : ∀ j, 0 ≤ a j) :
    pairedEtaTranslatedFiniteResidualBudget N a (fun j ↦ (pairedEtaCanonicalTranslateCoefficient N a j : ℂ)) ≤
      pairedEtaCanonicalTranslateBudget N a :=
  (pairedEtaTranslatedFiniteResidualBudget_le_ridgeObjective N a
    (pairedEtaCanonicalTranslateCoefficient N a)).trans_eq (pairedEtaTranslateRidgeObjective_canonical N ha)

/-- The entire continuous eta residual for the exact coefficient law is controlled, including its full infinite tail. -/
theorem pairedEtaCanonicalTranslate_residualEnergy_le {d N : ℕ} (hN : 1 ≤ N) {a : Fin d → ℝ}
    (ha : ∀ j, 0 ≤ a j) :
    pairedEtaTranslatedResidualEnergy a (fun j ↦ (pairedEtaCanonicalTranslateCoefficient N a j : ℂ)) ≤
      pairedEtaCanonicalTranslateBudget N a :=
  (pairedEtaTranslatedResidualEnergy_le_finiteBudget hN ha _).trans (pairedEtaCanonicalTranslate_finiteBudget_le N ha)

/-- Every valid canonical resolvent deficit is a proved nonnegative full error allowance. -/
theorem pairedEtaCanonicalTranslateBudget_nonneg {d N : ℕ} (hN : 1 ≤ N) {a : Fin d → ℝ}
    (ha : ∀ j, 0 ≤ a j) : 0 ≤ pairedEtaCanonicalTranslateBudget N a :=
  (pairedEtaTranslatedResidualEnergy_nonneg a _).trans (pairedEtaCanonicalTranslate_residualEnergy_le hN ha)

/-- Positive definiteness and the normal equations keep the exact canonical budget at most the original unit target mass. -/
theorem pairedEtaCanonicalTranslateBudget_le_one {d : ℕ} (N : ℕ) {a : Fin d → ℝ}
    (ha : ∀ j, 0 ≤ a j) : pairedEtaCanonicalTranslateBudget N a ≤ 1 := by
  have h := (pairedEtaRegularizedTranslateGram_posDef N ha).posSemidef.dotProduct_mulVec_nonneg
    (pairedEtaCanonicalTranslateCoefficient N a)
  rw [star_trivial, pairedEtaCanonicalTranslateCoefficient_normal N ha,
    dotProduct_comm (pairedEtaCanonicalTranslateCoefficient N a)] at h
  unfold pairedEtaCanonicalTranslateBudget
  linarith

/-- The exact coefficient law bounds the absolute displacement of every actual zero using both reflected target weights. -/
theorem pairedEtaCurrentHorizontalDisplacement_mul_headWeight_le_canonicalBudget {d N : ℕ}
    (rho : NontrivialZetaZero) (hN : 1 ≤ N) {a : Fin d → ℝ} (ha : ∀ j, 0 ≤ a j) :
    pairedEtaCurrentHorizontalDisplacement rho * pairedEtaProjectionHeadZeroWeight rho ≤
      pairedEtaCanonicalTranslateBudget N a :=
  (pairedEtaCurrentHorizontalDisplacement_mul_headWeight_le_finiteBudget rho hN ha _).trans
    (pairedEtaCanonicalTranslate_finiteBudget_le N ha)

end

end RiemannGaussian
