/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.CertifiedQuadraticForm
import Mathlib.Tactic

/-!
# Integer certificates for complete quadratic forms

Approximate Gram factors are checked using only integer products, sums,
absolute values and comparisons. The soundness theorem then transports the
checked matrix into real positive semidefiniteness. No eigenvalue estimate
from the certificate generator is trusted.
-/

namespace RiemannGaussian.CertifiedIntegerQuadraticForm
open Matrix
open scoped BigOperators

/-- The exact integer residual of a proposed Gram factor. -/
def residual {ι κ : Type*} [Fintype κ]
    (H : Matrix ι ι ℤ) (L : Matrix ι κ ℤ) : Matrix ι ι ℤ :=
  H - L * L.transpose

/-- Entrywise interpretation of an integer matrix over the reals. -/
noncomputable def realMatrix {ι κ : Type*} (M : Matrix ι κ ℤ) : Matrix ι κ ℝ :=
  fun i j => (M i j : ℝ)

/-- Executable symmetry and residual diagonal-dominance checks. -/
def check {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ]
    (H : Matrix ι ι ℤ) (L : Matrix ι κ ℤ) : Bool :=
  letI : ∀ i j : ι, Decidable (H i j = H j i) := fun i j => Int.instDecidableEq (H i j) (H j i)
  decide (∀ i j : ι, H i j = H j i) &&
    decide (∀ i : ι, (∑ j ∈ Finset.univ.erase i, |residual H L i j|) ≤ residual H L i i)

/-- Integer residuals cast exactly to real Gram residuals. -/
theorem residual_cast {ι κ : Type*} [Fintype κ]
    (H : Matrix ι ι ℤ) (L : Matrix ι κ ℤ) (i j : ι) :
    (residual H L i j : ℝ) =
      (realMatrix H - realMatrix L * (realMatrix L)ᴴ) i j := by
  simp only [residual, Matrix.sub_apply, Matrix.mul_apply, Matrix.transpose_apply,
    Matrix.conjTranspose_apply, realMatrix, star_trivial, Int.cast_sub, Int.cast_sum, Int.cast_mul]

/-- A checked integer certificate proves the real matrix positive
semidefinite using only the ordinary logical axioms of Lean. -/
theorem check_sound {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ]
    (H : Matrix ι ι ℤ) (L : Matrix ι κ ℤ) (h : check H L = true) :
    (realMatrix H).PosSemidef := by
  simp only [check, Bool.and_eq_true, decide_eq_true_eq] at h
  have hsym : (realMatrix H).IsHermitian := by
    ext i j
    simp only [Matrix.conjTranspose_apply, realMatrix, star_trivial]
    rw [h.1 j i]
  apply CertifiedQuadraticForm.posSemidef_of_gram_residual hsym (realMatrix L)
  intro i
  simp_rw [← residual_cast]
  exact_mod_cast h.2 i

end RiemannGaussian.CertifiedIntegerQuadraticForm
