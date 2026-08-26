import RiemannGaussian.FiniteBlaschkePick
import Mathlib.LinearAlgebra.Matrix.Notation

/-!
# A checked two-dimensional Pick Schur complement

This file derives the scalar value-disk quadratic from a normalized `3 x 3`
positive-semidefinite Pick block.  The normalization records the two base
kernel vectors as an orthonormal coordinate pair.  Cauchy--Schwarz is proved
here by an exact two-coordinate Lagrange identity.
-/

namespace RiemannGaussian

noncomputable section

open scoped ComplexConjugate ComplexOrder

/-- Cross column in a normalized two-base-node Pick block. -/
def normalizedPickCross (u v s : ℂ) : ℂ :=
  u + starRingEnd ℂ s * v

/-- Normalized `3 x 3` Pick block with identity base block. -/
def normalizedThreePointPickMatrix
    (h : ℝ) (u₀ u₁ v₀ v₁ s : ℂ) : Matrix (Fin 3) (Fin 3) ℂ :=
  !![(1 : ℂ), 0, normalizedPickCross u₀ v₀ s;
     0, 1, normalizedPickCross u₁ v₁ s;
     starRingEnd ℂ (normalizedPickCross u₀ v₀ s),
       starRingEnd ℂ (normalizedPickCross u₁ v₁ s),
       (h * (1 - Complex.normSq s) : ℝ)]

/-- Testing the normalized positive block against the vector
`(-cross₀,-cross₁,1)` gives its scalar Schur-complement inequality. -/
theorem normalizedThreePointPickMatrix_schur_inequality
    {h : ℝ} {u₀ u₁ v₀ v₁ s : ℂ}
    (hpsd : (normalizedThreePointPickMatrix h u₀ u₁ v₀ v₁ s).PosSemidef) :
    Complex.normSq (normalizedPickCross u₀ v₀ s) +
        Complex.normSq (normalizedPickCross u₁ v₁ s) ≤
      h * (1 - Complex.normSq s) := by
  let c₀ := normalizedPickCross u₀ v₀ s
  let c₁ := normalizedPickCross u₁ v₁ s
  let test : Fin 3 → ℂ := ![-c₀, -c₁, (1 : ℂ)]
  have hq := hpsd.dotProduct_mulVec_nonneg test
  have heval :
      star test ⬝ᵥ
          Matrix.mulVec
            (normalizedThreePointPickMatrix h u₀ u₁ v₀ v₁ s) test =
        ((h * (1 - Complex.normSq s) - Complex.normSq c₀ -
          Complex.normSq c₁ : ℝ) : ℂ) := by
    dsimp only [test, c₀, c₁, normalizedThreePointPickMatrix]
    simp only [Matrix.mulVec, Matrix.vec3_dotProduct]
    simp [← Complex.normSq_eq_conj_mul_self]
    ring
  rw [heval, Complex.zero_le_real] at hq
  dsimp only [c₀, c₁] at hq
  linarith

/-- Coefficient multiplying the linear term in the normalized value disk. -/
def normalizedPickLinearCoefficient
    (u₀ u₁ v₀ v₁ : ℂ) : ℂ :=
  starRingEnd ℂ v₀ * u₀ + starRingEnd ℂ v₁ * u₁

/-- Coefficient multiplying `|s|²` beyond the diagonal contribution. -/
def normalizedPickQuadraticCoefficient (v₀ v₁ : ℂ) : ℝ :=
  Complex.normSq v₀ + Complex.normSq v₁

theorem normalizedPickCross_normSq_sum
    (u₀ u₁ v₀ v₁ s : ℂ) :
    Complex.normSq (normalizedPickCross u₀ v₀ s) +
        Complex.normSq (normalizedPickCross u₁ v₁ s) =
      Complex.normSq u₀ + Complex.normSq u₁ +
        Complex.normSq s * normalizedPickQuadraticCoefficient v₀ v₁ +
        2 * (s * normalizedPickLinearCoefficient u₀ u₁ v₀ v₁).re := by
  unfold normalizedPickCross normalizedPickQuadraticCoefficient
    normalizedPickLinearCoefficient Complex.normSq
  simp
  ring

/-- The normalized PSD block and the boundary identity at `s = 0` imply the
exact real value-disk quadratic used by the terminal scalar theorem. -/
theorem normalizedThreePointPickMatrix_valueDiskQuadratic
    {h : ℝ} {u₀ u₁ v₀ v₁ s : ℂ}
    (hbase : Complex.normSq u₀ + Complex.normSq u₁ = h)
    (hpsd : (normalizedThreePointPickMatrix h u₀ u₁ v₀ v₁ s).PosSemidef) :
    (h + normalizedPickQuadraticCoefficient v₀ v₁) * ‖s‖ ^ 2 ≤
      -2 * (s * normalizedPickLinearCoefficient u₀ u₁ v₀ v₁).re := by
  have hschur := normalizedThreePointPickMatrix_schur_inequality hpsd
  rw [normalizedPickCross_normSq_sum] at hschur
  simp only [Complex.normSq_eq_norm_sq] at hschur hbase ⊢
  linarith

/-- Exact two-coordinate Lagrange identity underlying Cauchy--Schwarz. -/
theorem normalizedPick_lagrange_identity
    (u₀ u₁ v₀ v₁ : ℂ) :
    normalizedPickQuadraticCoefficient v₀ v₁ *
        (Complex.normSq u₀ + Complex.normSq u₁) -
      Complex.normSq
        (normalizedPickLinearCoefficient u₀ u₁ v₀ v₁) =
      Complex.normSq (v₀ * u₁ - v₁ * u₀) := by
  unfold normalizedPickQuadraticCoefficient normalizedPickLinearCoefficient
    Complex.normSq
  simp
  ring

theorem normalizedPick_cauchy_schwarz
    (u₀ u₁ v₀ v₁ : ℂ) :
    Complex.normSq
        (normalizedPickLinearCoefficient u₀ u₁ v₀ v₁) ≤
      normalizedPickQuadraticCoefficient v₀ v₁ *
        (Complex.normSq u₀ + Complex.normSq u₁) := by
  have hid := normalizedPick_lagrange_identity u₀ u₁ v₀ v₁
  have hnonneg : 0 ≤ Complex.normSq (v₀ * u₁ - v₁ * u₀) :=
    Complex.normSq_nonneg _
  linarith

/-- Complete normalized algebraic Pick-disk bound.  The only geometry-specific
input is the displayed norm identity for the linear coefficient. -/
theorem norm_le_two_mul_div_one_add_sq_of_normalizedPickMatrix
    {h b : ℝ} {u₀ u₁ v₀ v₁ s : ℂ}
    (hh : 0 < h) (hb : 0 ≤ b)
    (hbase : Complex.normSq u₀ + Complex.normSq u₁ = h)
    (hlinear :
      ‖normalizedPickLinearCoefficient u₀ u₁ v₀ v₁‖ = h * b)
    (hpsd : (normalizedThreePointPickMatrix h u₀ u₁ v₀ v₁ s).PosSemidef) :
    ‖s‖ ≤ 2 * b / (1 + b ^ 2) := by
  let M := normalizedPickQuadraticCoefficient v₀ v₁
  let d := normalizedPickLinearCoefficient u₀ u₁ v₀ v₁
  have hcs := normalizedPick_cauchy_schwarz u₀ u₁ v₀ v₁
  have hdSq : Complex.normSq d = h ^ 2 * b ^ 2 := by
    rw [Complex.normSq_eq_norm_sq, hlinear]
    ring
  have hM : h * b ^ 2 ≤ M := by
    rw [hbase] at hcs
    dsimp only [d, M] at hdSq ⊢
    rw [hdSq] at hcs
    nlinarith
  apply norm_le_two_mul_div_one_add_sq_of_pickDiskQuadratic hh hb hM
    hlinear
  exact normalizedThreePointPickMatrix_valueDiskQuadratic hbase hpsd

end

end RiemannGaussian
