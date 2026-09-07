import RiemannGaussian.EtaTranslatedFiniteResidual
import Mathlib.LinearAlgebra.Matrix.PosDef

/-!
# Exact regularized Gram coefficients on the actual eta translates

The literal finite translate Gram is symmetric and positive semidefinite
by its existing integral-of-squares identity. An explicit positive diagonal
regularization makes it invertible. Multiplication of that inverse by the
exact compact-target pairing defines coefficients without numerical
optimization or an assumed inverse. No asymptotic error estimate is assumed.
-/

open Complex Matrix MeasureTheory Set
open scoped Matrix

namespace RiemannGaussian

noncomputable section

/-- The literal finite eta overlap Gram as a real matrix. -/
def pairedEtaTranslateGramMatrix {d : ℕ} (N : ℕ) (a : Fin d → ℝ) : Matrix (Fin d) (Fin d) ℝ :=
  fun j k ↦ pairedEtaTranslatedFiniteGram N (Real.log (2 * N + 1 : ℝ)) (a j) (a k)

/-- The exact target pairing vector for the same original translates. -/
def pairedEtaTranslateTargetVector {d : ℕ} (a : Fin d → ℝ) : Fin d → ℝ :=
  fun j ↦ pairedEtaTranslatedHeadPairing (a j)

/-- The exact overlap entry retains its symmetry before any matrix estimate. -/
theorem pairedEtaTranslatedFiniteGram_symm (N : ℕ) (T a b : ℝ) :
    pairedEtaTranslatedFiniteGram N T a b = pairedEtaTranslatedFiniteGram N T b a := by
  unfold pairedEtaTranslatedFiniteGram
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro n _
  apply Finset.sum_congr rfl
  intro m _
  simp only [pairedEtaTranslatedOverlapMass, max_comm, min_comm]

/-- The actual real translate matrix is Hermitian, including repeated translates. -/
theorem pairedEtaTranslateGramMatrix_isHermitian {d : ℕ} (N : ℕ) (a : Fin d → ℝ) :
    (pairedEtaTranslateGramMatrix N a).IsHermitian := by
  ext j k
  simp only [Matrix.conjTranspose_apply, star_trivial, pairedEtaTranslateGramMatrix]
  exact pairedEtaTranslatedFiniteGram_symm N _ _ _

/-- The matrix quadratic form is exactly the weighted square integral of the full finite translate combination. -/
theorem pairedEtaTranslateGramMatrix_energy_eq_integral {d N : ℕ} {a : Fin d → ℝ}
    (ha : ∀ j, 0 ≤ a j) (c : Fin d → ℝ) :
    dotProduct c ((pairedEtaTranslateGramMatrix N a) *ᵥ c) =
      ∫ t : ℝ in Ioc 0 (Real.log (2 * N + 1 : ℝ)), Real.exp (-t) *
        ‖pairedEtaTranslatedCombination a (fun j ↦ (c j : ℂ)) t‖ ^ 2 := by
  rw [integral_pairedEtaTranslatedCombination_sq_eq_finiteGram ha (fun j ↦ (c j : ℂ)) le_rfl]
  simp only [dotProduct, Matrix.mulVec, pairedEtaTranslateGramMatrix, Finset.mul_sum,
    Complex.conj_ofReal, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro k _
  ring

/-- Positive semidefiniteness follows from the unchanged full complex combination's actual square integral. -/
theorem pairedEtaTranslateGramMatrix_posSemidef {d : ℕ} (N : ℕ) {a : Fin d → ℝ}
    (ha : ∀ j, 0 ≤ a j) : (pairedEtaTranslateGramMatrix N a).PosSemidef := by
  apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg (pairedEtaTranslateGramMatrix_isHermitian N a)
  intro c
  rw [star_trivial, pairedEtaTranslateGramMatrix_energy_eq_integral ha c]
  exact integral_nonneg (fun _ ↦ by positivity)

/-- An explicit diagonal cost dominating the full coefficient norm tail, with positivity even for an empty family. -/
def pairedEtaTranslateRegularization (d N : ℕ) : ℝ := (d + 1 : ℝ) / (2 * N + 1 : ℝ)

/-- The regularization is strictly positive at every arithmetic cutoff and dimension. -/
theorem pairedEtaTranslateRegularization_pos (d N : ℕ) : 0 < pairedEtaTranslateRegularization d N := by
  unfold pairedEtaTranslateRegularization
  positivity

/-- The actual Gram with its explicit positive diagonal regularization. -/
def pairedEtaRegularizedTranslateGram {d : ℕ} (N : ℕ) (a : Fin d → ℝ) : Matrix (Fin d) (Fin d) ℝ :=
  pairedEtaTranslateGramMatrix N a + pairedEtaTranslateRegularization d N • 1

/-- The regularized actual Gram is positive definite without any spacing or rank assumption on the translates. -/
theorem pairedEtaRegularizedTranslateGram_posDef {d : ℕ} (N : ℕ) {a : Fin d → ℝ}
    (ha : ∀ j, 0 ≤ a j) : (pairedEtaRegularizedTranslateGram N a).PosDef :=
  Matrix.PosDef.posSemidef_add (pairedEtaTranslateGramMatrix_posSemidef N ha)
    (Matrix.PosDef.one.smul (pairedEtaTranslateRegularization_pos d N))

/-- An exact coefficient law from the regularized actual Gram and the unchanged compact target. -/
def pairedEtaCanonicalTranslateCoefficient {d : ℕ} (N : ℕ) (a : Fin d → ℝ) : Fin d → ℝ :=
  (pairedEtaRegularizedTranslateGram N a)⁻¹ *ᵥ pairedEtaTranslateTargetVector a

/-- The defined inverse solves the exact regularized normal equations; invertibility is proved for the actual matrix. -/
theorem pairedEtaCanonicalTranslateCoefficient_normal {d : ℕ} (N : ℕ) {a : Fin d → ℝ}
    (ha : ∀ j, 0 ≤ a j) :
    pairedEtaRegularizedTranslateGram N a *ᵥ pairedEtaCanonicalTranslateCoefficient N a =
      pairedEtaTranslateTargetVector a := by
  have hu := (pairedEtaRegularizedTranslateGram_posDef N ha).isUnit
  rw [pairedEtaCanonicalTranslateCoefficient, Matrix.mulVec_mulVec,
    Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).mp hu), Matrix.one_mulVec]

end

end RiemannGaussian
