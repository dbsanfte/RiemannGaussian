/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.LinearAlgebra.Matrix.Gershgorin
import Mathlib.LinearAlgebra.Eigenspace.Matrix
import Mathlib.Algebra.Order.Star.Real

/-!
# Rational witnesses for a nonnegative coupled quadratic form

A proposed Gram factor need not equal the matrix exactly. It suffices to
check that the symmetric residual is diagonally dominant with nonnegative
diagonal. All numerical obligations are rational polynomial inequalities;
computing the proposed factor requires no trust.
-/

namespace RiemannGaussian.CertifiedQuadraticForm
noncomputable section
open Matrix
open scoped BigOperators

/-- Symmetric diagonal dominance with a nonnegative diagonal implies
nonnegative quadratic energy. -/
theorem posSemidef_of_diagonal_dominance {ι : Type*} [Fintype ι] [DecidableEq ι]
    {H : Matrix ι ι ℝ} (hH : H.IsHermitian)
    (hd : ∀ i, (∑ j ∈ Finset.univ.erase i, |H i j|) ≤ H i i) : H.PosSemidef := by
  apply hH.posSemidef_iff_eigenvalues_nonneg.mpr
  intro i
  change (0 : ℝ) ≤ hH.eigenvalues i
  have hμ : Module.End.HasEigenvalue H.toLin' (hH.eigenvalues i) :=
    Module.End.HasEigenvalue.of_mem_spectrum
      (by simpa only [Matrix.spectrum_toLin'] using hH.eigenvalues_mem_spectrum_real i)
  obtain ⟨k, hk⟩ := eigenvalue_mem_ball hμ
  simp only [mem_closedBall_iff_norm', Real.norm_eq_abs] at hk
  linarith [(abs_le.mp hk).2, hd k]

/-- An approximate Gram factor is a certificate when its residual passes
diagonal dominance. No division or numerical eigenvalue is needed to
check this witness. -/
theorem posSemidef_of_gram_residual {ι κ : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype κ] {H : Matrix ι ι ℝ} (hH : H.IsHermitian) (L : Matrix ι κ ℝ)
    (hd : ∀ i,
      (∑ j ∈ Finset.univ.erase i, |(H - L * Lᴴ) i j|) ≤ (H - L * Lᴴ) i i) :
    H.PosSemidef := by
  have hg := Matrix.posSemidef_self_mul_conjTranspose L
  have hr := posSemidef_of_diagonal_dominance (hH.sub hg.isHermitian) hd
  simpa only [sub_add_cancel] using hr.add hg

end
end RiemannGaussian.CertifiedQuadraticForm
