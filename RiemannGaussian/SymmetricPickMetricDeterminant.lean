import RiemannGaussian.SymmetricQuartetPickDefect

/-!
# Two-node weighted-Gram determinant bridge

This file proves the finite `2 × 2` determinant algebra underlying the
claimed metric-pencil product formula.  If the squared metric modes are the
two generalized roots of the weighted Gram pencil formalized below, their
nonnegative magnitudes multiply to `‖s₀ * s₁‖`.

Identifying an analytic Hardy cross-angle complement with this weighted Gram
pencil is a separate theorem and is not assumed here.
-/

namespace RiemannGaussian

noncomputable section

open scoped ComplexConjugate Matrix

def twoHermitianMatrix (A D : ℝ) (C : ℂ) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![(A : ℂ), C;
     starRingEnd ℂ C, (D : ℂ)]

/-- Congruence of the base Gram matrix by `diag(s₀,s₁)`. -/
def twoValueWeightedHermitianMatrix
    (A D : ℝ) (C s₀ s₁ : ℂ) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![((Complex.normSq s₀ * A : ℝ) : ℂ),
      s₀ * C * starRingEnd ℂ s₁;
     starRingEnd ℂ s₀ * starRingEnd ℂ C * s₁,
      ((Complex.normSq s₁ * D : ℝ) : ℂ)]

theorem twoHermitianMatrix_det (A D : ℝ) (C : ℂ) :
    Matrix.det (twoHermitianMatrix A D C) =
      (twoHermitianDet A D C : ℂ) := by
  simp [Matrix.det_fin_two, twoHermitianMatrix, twoHermitianDet,
    Complex.normSq_eq_conj_mul_self]
  ring

theorem twoValueWeightedHermitianMatrix_det
    (A D : ℝ) (C s₀ s₁ : ℂ) :
    Matrix.det (twoValueWeightedHermitianMatrix A D C s₀ s₁) =
      (Complex.normSq (s₀ * s₁) : ℂ) *
        (twoHermitianDet A D C : ℂ) := by
  simp only [Matrix.det_fin_two]
  simp [twoValueWeightedHermitianMatrix]
  unfold twoHermitianDet
  push_cast
  simp only [Complex.normSq_eq_conj_mul_self]
  ring

/-- Generalized squared-mode pencil `W - μ G`, where `G` is the base Gram
matrix and `W = diag(s) G diag(s)†`. -/
def twoValueWeightedGramPencil
    (A D : ℝ) (C s₀ s₁ μ : ℂ) : Matrix (Fin 2) (Fin 2) ℂ :=
  twoValueWeightedHermitianMatrix A D C s₀ s₁ -
    μ • twoHermitianMatrix A D C

def twoValueWeightedGramPencilMiddle
    (A D : ℝ) (C s₀ s₁ : ℂ) : ℂ :=
  -(A * D : ℂ) *
      ((Complex.normSq s₀ : ℂ) + (Complex.normSq s₁ : ℂ)) +
    (Complex.normSq C : ℂ) *
      (s₀ * starRingEnd ℂ s₁ + starRingEnd ℂ s₀ * s₁)

theorem twoValueWeightedGramPencil_det
    (A D : ℝ) (C s₀ s₁ μ : ℂ) :
    Matrix.det (twoValueWeightedGramPencil A D C s₀ s₁ μ) =
      (twoHermitianDet A D C : ℂ) * μ ^ 2 +
        twoValueWeightedGramPencilMiddle A D C s₀ s₁ * μ +
        (twoHermitianDet A D C : ℂ) *
          (Complex.normSq (s₀ * s₁) : ℂ) := by
  rw [Matrix.det_fin_two]
  simp [twoValueWeightedGramPencil,
    twoValueWeightedHermitianMatrix, twoHermitianMatrix,
    Matrix.sub_apply, smul_eq_mul]
  unfold twoValueWeightedGramPencilMiddle twoHermitianDet
  push_cast
  simp only [Complex.normSq_eq_conj_mul_self]
  ring

theorem product_of_two_distinct_quadratic_roots
    {d e n μ₀ μ₁ : ℂ} (hd : d ≠ 0) (hne : μ₀ ≠ μ₁)
    (h₀ : d * μ₀ ^ 2 + e * μ₀ + d * n = 0)
    (h₁ : d * μ₁ ^ 2 + e * μ₁ + d * n = 0) :
    μ₀ * μ₁ = n := by
  have hfactor :
      (μ₀ - μ₁) * (d * (μ₀ + μ₁) + e) = 0 := by
    calc
      (μ₀ - μ₁) * (d * (μ₀ + μ₁) + e) =
          (d * μ₀ ^ 2 + e * μ₀ + d * n) -
            (d * μ₁ ^ 2 + e * μ₁ + d * n) := by ring
      _ = 0 := by rw [h₀, h₁]; ring
  have hsum : d * (μ₀ + μ₁) + e = 0 :=
    (mul_eq_zero.mp hfactor).resolve_left (sub_ne_zero.mpr hne)
  have hproduct : d * (n - μ₀ * μ₁) = 0 := by
    calc
      d * (n - μ₀ * μ₁) =
          (d * μ₀ ^ 2 + e * μ₀ + d * n) -
            μ₀ * (d * (μ₀ + μ₁) + e) := by ring
      _ = 0 := by rw [h₀, hsum]; ring
  have := (mul_eq_zero.mp hproduct).resolve_left hd
  exact (sub_eq_zero.mp this).symm

/-- Vieta product for the two distinct generalized squared modes of the
weighted two-node Gram pencil. -/
theorem twoValueWeightedGramPencil_root_product
    {A D : ℝ} {C s₀ s₁ μ₀ μ₁ : ℂ}
    (hdet : twoHermitianDet A D C ≠ 0) (hne : μ₀ ≠ μ₁)
    (hroot₀ : Matrix.det
      (twoValueWeightedGramPencil A D C s₀ s₁ μ₀) = 0)
    (hroot₁ : Matrix.det
      (twoValueWeightedGramPencil A D C s₀ s₁ μ₁) = 0) :
    μ₀ * μ₁ = (Complex.normSq (s₀ * s₁) : ℂ) := by
  apply product_of_two_distinct_quadratic_roots
      (d := (twoHermitianDet A D C : ℂ))
      (e := twoValueWeightedGramPencilMiddle A D C s₀ s₁)
  · exact_mod_cast hdet
  · exact hne
  · simpa [twoValueWeightedGramPencil_det] using hroot₀
  · simpa [twoValueWeightedGramPencil_det] using hroot₁

/-- If the two supplied metric magnitudes are nonnegative and their squares
are the distinct generalized roots, their product is the residual two-value
modulus. -/
theorem twoValueWeightedGramPencil_magnitude_product
    {A D σ₀ σ₁ : ℝ} {C s₀ s₁ : ℂ}
    (hdet : twoHermitianDet A D C ≠ 0)
    (hσ₀ : 0 ≤ σ₀) (hσ₁ : 0 ≤ σ₁) (hne : σ₀ ^ 2 ≠ σ₁ ^ 2)
    (hroot₀ : Matrix.det
      (twoValueWeightedGramPencil A D C s₀ s₁ (σ₀ ^ 2 : ℂ)) = 0)
    (hroot₁ : Matrix.det
      (twoValueWeightedGramPencil A D C s₀ s₁ (σ₁ ^ 2 : ℂ)) = 0) :
    σ₀ * σ₁ = ‖s₀ * s₁‖ := by
  have hneC : (σ₀ ^ 2 : ℂ) ≠ (σ₁ ^ 2 : ℂ) := by
    exact_mod_cast hne
  have hproductC := twoValueWeightedGramPencil_root_product
    hdet hneC hroot₀ hroot₁
  have hproduct : σ₀ ^ 2 * σ₁ ^ 2 =
      Complex.normSq (s₀ * s₁) := by
    exact_mod_cast hproductC
  have hnormSq : ‖s₀ * s₁‖ ^ 2 =
      Complex.normSq (s₀ * s₁) := Complex.sq_norm _
  have hnonneg : 0 ≤ σ₀ * σ₁ := mul_nonneg hσ₀ hσ₁
  have hnormNonneg : 0 ≤ ‖s₀ * s₁‖ := norm_nonneg _
  nlinarith

end

end RiemannGaussian
