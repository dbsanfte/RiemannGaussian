import RiemannGaussian.SymmetricPickSchur

/-!
# Exact Schur complement for a general two-node Pick block

This file removes the normalization assumption from the preceding Pick-disk
algebra.  Everything is written in terms of the two real diagonal entries and
one complex off-diagonal entry of the base `2 x 2` Hermitian block.
-/

namespace RiemannGaussian

noncomputable section

open scoped ComplexConjugate ComplexOrder

def twoHermitianDet (A D : ℝ) (C : ℂ) : ℝ :=
  A * D - Complex.normSq C

def twoHermitianAdjugateNorm
    (A D : ℝ) (C x₀ x₁ : ℂ) : ℝ :=
  D * Complex.normSq x₀ + A * Complex.normSq x₁ -
    2 * (starRingEnd ℂ x₀ * C * x₁).re

def twoHermitianInvNorm
    (A D : ℝ) (C x₀ x₁ : ℂ) : ℝ :=
  twoHermitianAdjugateNorm A D C x₀ x₁ / twoHermitianDet A D C

def twoHermitianInvForm
    (A D : ℝ) (C x₀ x₁ y₀ y₁ : ℂ) : ℂ :=
  ((D : ℂ) * starRingEnd ℂ x₀ * y₀ -
      C * starRingEnd ℂ x₀ * y₁ -
      starRingEnd ℂ C * starRingEnd ℂ x₁ * y₀ +
      (A : ℂ) * starRingEnd ℂ x₁ * y₁) /
    (twoHermitianDet A D C : ℂ)

def generalTwoNodePickMatrix
    (A D : ℝ) (C : ℂ) (h : ℝ)
    (u₀ u₁ v₀ v₁ s : ℂ) : Matrix (Fin 3) (Fin 3) ℂ :=
  let c₀ := normalizedPickCross u₀ v₀ s
  let c₁ := normalizedPickCross u₁ v₁ s
  !![(A : ℂ), C, c₀;
     starRingEnd ℂ C, (D : ℂ), c₁;
     starRingEnd ℂ c₀, starRingEnd ℂ c₁,
       (h * (1 - Complex.normSq s) : ℝ)]

theorem generalTwoNodePickMatrix_det
    (A D : ℝ) (C : ℂ) (h : ℝ)
    (u₀ u₁ v₀ v₁ s : ℂ) :
    Matrix.det (generalTwoNodePickMatrix A D C h u₀ u₁ v₀ v₁ s) =
      ((twoHermitianDet A D C * (h * (1 - Complex.normSq s)) -
        twoHermitianAdjugateNorm A D C
          (normalizedPickCross u₀ v₀ s)
          (normalizedPickCross u₁ v₁ s) : ℝ) : ℂ) := by
  rw [Matrix.det_fin_three]
  simp only [generalTwoNodePickMatrix]
  unfold twoHermitianDet twoHermitianAdjugateNorm
  apply Complex.ext <;>
    simp [Complex.normSq_apply, Complex.mul_re, Complex.mul_im]
  <;> ring

/-- Positive semidefiniteness of the full block gives the exact unnormalized
Schur-complement inequality. -/
theorem generalTwoNodePickMatrix_schur_inequality
    {A D h : ℝ} {C u₀ u₁ v₀ v₁ s : ℂ}
    (hdet : 0 < twoHermitianDet A D C)
    (hpsd : (generalTwoNodePickMatrix A D C h u₀ u₁ v₀ v₁ s).PosSemidef) :
    twoHermitianInvNorm A D C
        (normalizedPickCross u₀ v₀ s)
        (normalizedPickCross u₁ v₁ s) ≤
      h * (1 - Complex.normSq s) := by
  have hnonneg := hpsd.det_nonneg
  rw [generalTwoNodePickMatrix_det, Complex.zero_le_real] at hnonneg
  unfold twoHermitianInvNorm
  exact (div_le_iff₀ hdet).2 (by
    rw [mul_comm]
    linarith)

theorem twoHermitianInvNorm_cross_expansion
    {A D : ℝ} {C : ℂ}
    (u₀ u₁ v₀ v₁ s : ℂ)
    (hdet : twoHermitianDet A D C ≠ 0) :
    twoHermitianInvNorm A D C
        (normalizedPickCross u₀ v₀ s)
        (normalizedPickCross u₁ v₁ s) =
      twoHermitianInvNorm A D C u₀ u₁ +
        Complex.normSq s * twoHermitianInvNorm A D C v₀ v₁ +
        2 * (s * twoHermitianInvForm A D C v₀ v₁ u₀ u₁).re := by
  unfold twoHermitianInvNorm twoHermitianAdjugateNorm
    twoHermitianInvForm normalizedPickCross
  simp [Complex.normSq_apply, Complex.mul_re, Complex.mul_im]
  field_simp [hdet]
  ring

/-- Determinant identity for the inverse Hermitian form. -/
theorem twoHermitianInvForm_lagrange
    {A D : ℝ} {C : ℂ}
    (u₀ u₁ v₀ v₁ : ℂ)
    (hdet : twoHermitianDet A D C ≠ 0) :
    twoHermitianInvNorm A D C v₀ v₁ *
        twoHermitianInvNorm A D C u₀ u₁ -
      Complex.normSq (twoHermitianInvForm A D C v₀ v₁ u₀ u₁) =
      Complex.normSq (v₀ * u₁ - v₁ * u₀) /
        twoHermitianDet A D C := by
  unfold twoHermitianInvNorm twoHermitianAdjugateNorm
    twoHermitianInvForm
  simp [Complex.normSq_apply, Complex.mul_re, Complex.mul_im]
  field_simp [hdet]
  unfold twoHermitianDet
  rw [Complex.normSq_apply]
  ring

theorem twoHermitianInvForm_cauchy_schwarz
    {A D : ℝ} {C : ℂ}
    (u₀ u₁ v₀ v₁ : ℂ)
    (hdet : 0 < twoHermitianDet A D C) :
    Complex.normSq (twoHermitianInvForm A D C v₀ v₁ u₀ u₁) ≤
      twoHermitianInvNorm A D C v₀ v₁ *
        twoHermitianInvNorm A D C u₀ u₁ := by
  have hid := twoHermitianInvForm_lagrange u₀ u₁ v₀ v₁ hdet.ne'
  have hright : 0 ≤
      Complex.normSq (v₀ * u₁ - v₁ * u₀) /
        twoHermitianDet A D C :=
    div_nonneg (Complex.normSq_nonneg _) hdet.le
  linarith

theorem generalTwoNodePickMatrix_valueDiskQuadratic
    {A D h : ℝ} {C u₀ u₁ v₀ v₁ s : ℂ}
    (hdet : 0 < twoHermitianDet A D C)
    (hbase : twoHermitianInvNorm A D C u₀ u₁ = h)
    (hpsd : (generalTwoNodePickMatrix A D C h u₀ u₁ v₀ v₁ s).PosSemidef) :
    (h + twoHermitianInvNorm A D C v₀ v₁) * ‖s‖ ^ 2 ≤
      -2 * (s * twoHermitianInvForm A D C v₀ v₁ u₀ u₁).re := by
  have hschur := generalTwoNodePickMatrix_schur_inequality hdet hpsd
  rw [twoHermitianInvNorm_cross_expansion u₀ u₁ v₀ v₁ s hdet.ne'] at hschur
  rw [hbase] at hschur
  simp only [Complex.normSq_eq_norm_sq] at hschur ⊢
  linarith

/-- Complete unnormalized two-node Pick-disk theorem. -/
theorem norm_le_two_mul_div_one_add_sq_of_generalTwoNodePickMatrix
    {A D h b : ℝ} {C u₀ u₁ v₀ v₁ s : ℂ}
    (hh : 0 < h) (hb : 0 ≤ b)
    (hdet : 0 < twoHermitianDet A D C)
    (hbase : twoHermitianInvNorm A D C u₀ u₁ = h)
    (hlinear :
      ‖twoHermitianInvForm A D C v₀ v₁ u₀ u₁‖ = h * b)
    (hpsd : (generalTwoNodePickMatrix A D C h u₀ u₁ v₀ v₁ s).PosSemidef) :
    ‖s‖ ≤ 2 * b / (1 + b ^ 2) := by
  let M := twoHermitianInvNorm A D C v₀ v₁
  let d := twoHermitianInvForm A D C v₀ v₁ u₀ u₁
  have hcs := twoHermitianInvForm_cauchy_schwarz
    u₀ u₁ v₀ v₁ hdet
  have hdSq : Complex.normSq d = h ^ 2 * b ^ 2 := by
    rw [Complex.normSq_eq_norm_sq, hlinear]
    ring
  have hM : h * b ^ 2 ≤ M := by
    rw [hbase] at hcs
    change Complex.normSq d ≤ M * h at hcs
    rw [hdSq] at hcs
    nlinarith
  apply norm_le_two_mul_div_one_add_sq_of_pickDiskQuadratic hh hb hM
    hlinear
  exact generalTwoNodePickMatrix_valueDiskQuadratic hdet hbase hpsd

end

end RiemannGaussian
