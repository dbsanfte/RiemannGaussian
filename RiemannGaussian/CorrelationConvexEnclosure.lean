/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.CertifiedQuadraticForm
import RiemannGaussian.CorrelationQuadraticEnclosure

/-!
# A tangent bound from the complete correlation curvature

Individual correlations may have negative curvature. The combined matrix
retains their shared coordinate directions, and a certificate for that
matrix suffices to support the whole weighted sum at any anchor in the box.
-/

namespace RiemannGaussian.CorrelationConvexEnclosure
noncomputable section
open Matrix Set
open scoped BigOperators

/-- The complete matrix of a sum of signed squares of linear forms. -/
def curvatureMatrix {ι κ : Type*} [Fintype ι]
    (d : ι → ℝ) (a : ι → κ → ℝ) : Matrix κ κ ℝ :=
  fun i j => ∑ t, d t * a t i * a t j

/-- Expanding the matrix keeps all mixed coordinate products exactly. -/
theorem curvatureMatrix_energy {ι κ : Type*} [Fintype ι] [Fintype κ]
    (d : ι → ℝ) (a : ι → κ → ℝ) (u : κ → ℝ) :
    u ⬝ᵥ (curvatureMatrix d a *ᵥ u) =
      ∑ t, d t * (∑ j, a t j * u j) ^ 2 := by
  simp only [dotProduct, mulVec, curvatureMatrix, Finset.mul_sum, Finset.sum_mul]
  calc
    (∑ i, ∑ j, ∑ t, u i * (d t * a t i * a t j * u j)) =
        ∑ i, ∑ t, ∑ j, u i * (d t * a t i * a t j * u j) :=
      Finset.sum_congr rfl fun _ _ => Finset.sum_comm
    _ = ∑ t, ∑ i, ∑ j, u i * (d t * a t i * a t j * u j) := Finset.sum_comm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro t _
      simp only [pow_two, Finset.mul_sum, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      ring

/-- A matrix certificate pays the complete signed square sum. -/
theorem square_sum_nonneg {ι κ : Type*} [Fintype ι] [Fintype κ]
    (d : ι → ℝ) (a : ι → κ → ℝ)
    (h : (curvatureMatrix d a).PosSemidef) (u : κ → ℝ) :
    0 ≤ ∑ t, d t * (∑ j, a t j * u j) ^ 2 := by
  rw [← curvatureMatrix_energy]
  simpa only [star_trivial] using h.dotProduct_mulVec_nonneg u

/-- Summing the scalar Taylor remainders and retaining their full matrix
proves a tangent bound for the complete weighted correlation sum. -/
theorem coupled_tangent_lower {ι κ : Type*} [Fintype ι] [Fintype κ]
    {f f' f'' : ℝ → ℝ} (c l lo hi m x : ι → ℝ)
    (a : ι → κ → ℝ) (u : κ → ℝ)
    (hc : ∀ t, 0 ≤ c t)
    (hf : ∀ t z, z ∈ Icc (lo t) (hi t) → HasDerivAt f (f' z) z)
    (hf' : ∀ t z, z ∈ Icc (lo t) (hi t) → HasDerivAt f' (f'' z) z)
    (hl : ∀ t z, z ∈ Icc (lo t) (hi t) → l t ≤ f'' z)
    (hm : ∀ t, m t ∈ Icc (lo t) (hi t))
    (hx : ∀ t, x t ∈ Icc (lo t) (hi t))
    (hdelta : ∀ t, x t - m t = ∑ j, a t j * u j)
    (hmat : (curvatureMatrix (fun t => c t * l t) a).PosSemidef) :
    (∑ t, c t * (f (m t) + f' (m t) * (x t - m t))) ≤ ∑ t, c t * f (x t) := by
  have hq : 0 ≤ ∑ t, (c t * l t) * (x t - m t) ^ 2 := by
    simp_rw [hdelta]
    exact square_sum_nonneg _ _ hmat u
  calc
    _ ≤ (∑ t, c t * (f (m t) + f' (m t) * (x t - m t))) +
        (1 / 2 : ℝ) * (∑ t, (c t * l t) * (x t - m t) ^ 2) := by linarith
    _ = ∑ t, c t * (f (m t) + f' (m t) * (x t - m t) +
        l t / 2 * (x t - m t) ^ 2) := by
      rw [Finset.mul_sum, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun _ _ => by ring
    _ ≤ _ := Finset.sum_le_sum fun t _ =>
      mul_le_mul_of_nonneg_left
        (CorrelationQuadraticEnclosure.lower_from_second_derivative
          (hf t) (hf' t) (hl t) (hm t) (hx t)) (hc t)

end
end RiemannGaussian.CorrelationConvexEnclosure
