/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaPhaseContactFactorization

/-!
# Removing the exact phase contacts without losing the kernel

Eight successive monic linear divisions remove the four double contacts.
For the exact phase polynomial this is an exact factorization, so no
remainder is discarded. Linearity shows that only the three frequencies
above degree eight contribute to the quotient; the lower coefficients
still enforce the vanishing remainder in the original kernel.
-/

open scoped Classical Polynomial
open Polynomial

namespace RiemannGaussian

noncomputable section

private def phaseLinearDivision (q : ℝ) : ℝ[X] →ₗ[ℝ] ℝ[X] where
  toFun p := p /ₘ (X - C q)
  map_add' p r := by
    apply (div_modByMonic_unique (p /ₘ (X - C q) + r /ₘ (X - C q))
      (p %ₘ (X - C q) + r %ₘ (X - C q)) (monic_X_sub_C q) ?_).1
    constructor
    · linear_combination p.modByMonic_add_div (X - C q) + r.modByMonic_add_div (X - C q)
    · exact (degree_add_le _ _).trans_lt
        (max_lt (degree_modByMonic_lt p (monic_X_sub_C q))
          (degree_modByMonic_lt r (monic_X_sub_C q)))
  map_smul' c p := by
    apply (div_modByMonic_unique (c • (p /ₘ (X - C q)))
      (c • (p %ₘ (X - C q))) (monic_X_sub_C q) ?_).1
    constructor
    · rw [mul_smul_comm, ← smul_add, modByMonic_add_div]
    · exact (degree_smul_le _ _).trans_lt (degree_modByMonic_lt p (monic_X_sub_C q))

/-- The product of the four squared contact factors. -/
def phaseContactFactor (q : Fin 4 → ℝ) : ℝ[X] := ∏ j : Fin 4, (X - C (q j)) ^ 2

/-- Successive exact monic divisions, retaining a linear map on the
entire original polynomial. -/
def phaseContactDeflate (q : Fin 4 → ℝ) : ℝ[X] →ₗ[ℝ] ℝ[X] :=
  (phaseLinearDivision (q 3)).comp ((phaseLinearDivision (q 3)).comp
  ((phaseLinearDivision (q 2)).comp ((phaseLinearDivision (q 2)).comp
  ((phaseLinearDivision (q 1)).comp ((phaseLinearDivision (q 1)).comp
  ((phaseLinearDivision (q 0)).comp (phaseLinearDivision (q 0))))))))

/-- The division map is explicitly the eight synthetic divisions. -/
theorem phaseContactDeflate_apply (q : Fin 4 → ℝ) (p : ℝ[X]) :
    phaseContactDeflate q p =
      (((((((p /ₘ (X - C (q 0))) /ₘ (X - C (q 0))) /ₘ (X - C (q 1))) /ₘ
        (X - C (q 1))) /ₘ (X - C (q 2))) /ₘ (X - C (q 2))) /ₘ (X - C (q 3))) /ₘ
          (X - C (q 3)) := rfl

/-- The degree-eight factor is cancelled exactly, with every double
contact present. -/
theorem phaseContactDeflate_factor_mul (q : Fin 4 → ℝ) (r : ℝ[X]) :
    phaseContactDeflate q (phaseContactFactor q * r) = r := by
  simp [phaseContactDeflate_apply, phaseContactFactor, Fin.prod_univ_succ, pow_two, mul_assoc,
    mul_divByMonic_cancel_left _ (monic_X_sub_C _)]

/-- The eight divisions remove every polynomial of degree below eight. -/
theorem phaseContactDeflate_eq_zero_of_natDegree_le {p : ℝ[X]} (hp : p.natDegree ≤ 7)
    (q : Fin 4 → ℝ) : phaseContactDeflate q p = 0 := by
  rw [phaseContactDeflate_apply]
  apply (divByMonic_eq_zero_iff (monic_X_sub_C (q 3))).mpr
  apply degree_lt_degree
  simp only [natDegree_divByMonic _ (monic_X_sub_C _), natDegree_X_sub_C]
  omega

/-- The canonical quotient of the exact phase kernel, defined by its
contact geometry rather than by a numerical coefficient list. -/
def phaseContactExactQuotient : ℝ[X] :=
  phaseContactDeflate (fun j ↦ phaseContactExactRoot (phaseContactCosineCoordinate j))
    phaseContactExactPolynomial

/-- The constructed polynomial equals the squared contact factor times
the canonical quotient. In particular its remainder is exactly zero. -/
theorem phaseContactExactPolynomial_eq_factor_mul_quotient :
    phaseContactExactPolynomial =
      phaseContactFactor (fun j ↦ phaseContactExactRoot (phaseContactCosineCoordinate j)) *
        phaseContactExactQuotient := by
  obtain ⟨r, _, hr⟩ := exists_phaseContactExactPolynomial_quotient
  have hr' : phaseContactExactPolynomial =
      phaseContactFactor (fun j ↦ phaseContactExactRoot (phaseContactCosineCoordinate j)) * r := hr
  have hq : phaseContactExactQuotient = r := by
    unfold phaseContactExactQuotient
    rw [hr', phaseContactDeflate_factor_mul]
  rw [hq]
  exact hr'

/-- The canonical quotient has degree at most sixteen. -/
theorem phaseContactExactQuotient_natDegree_le : phaseContactExactQuotient.natDegree ≤ 16 := by
  obtain ⟨r, hd, hr⟩ := exists_phaseContactExactPolynomial_quotient
  have hr' : phaseContactExactPolynomial =
      phaseContactFactor (fun j ↦ phaseContactExactRoot (phaseContactCosineCoordinate j)) * r := hr
  unfold phaseContactExactQuotient
  rw [hr', phaseContactDeflate_factor_mul]
  exact hd

/-- Only frequencies 10, 13 and 24 contribute to the quotient. The six
lower coefficients remain in the original polynomial and its exact
contact factorization; they have zero quotient because their degrees are
below the contact factor's degree. -/
theorem phaseContactExactQuotient_eq_three_frequencies :
    phaseContactExactQuotient =
      ∑ i : Fin 3, phaseContactExactCoefficients ⟨i.val + 6, by omega⟩ •
        phaseContactDeflate (fun j ↦ phaseContactExactRoot (phaseContactCosineCoordinate j))
          (Chebyshev.T ℝ (phaseContactFrequency ⟨i.val + 6, by omega⟩ : ℤ)) := by
  let q : Fin 4 → ℝ := fun j ↦ phaseContactExactRoot (phaseContactCosineCoordinate j)
  have hlow (i : Fin 6) : phaseContactDeflate q
      (Chebyshev.T ℝ (phaseContactFrequency ⟨i.val, by omega⟩ : ℤ)) = 0 := by
    apply phaseContactDeflate_eq_zero_of_natDegree_le
    simp only [Chebyshev.natDegree_T, Int.natAbs_natCast]
    fin_cases i <;> norm_num [phaseContactFrequency]
  unfold phaseContactExactQuotient phaseContactExactPolynomial
  simp only [← smul_eq_C_mul, map_sum, map_smul]
  change (∑ i : Fin 9, phaseContactExactCoefficients i •
    phaseContactDeflate q (Chebyshev.T ℝ (phaseContactFrequency i : ℤ))) = _
  have h0 : phaseContactDeflate q (Chebyshev.T ℝ 0) = 0 := hlow 0
  have h1 : phaseContactDeflate q (Chebyshev.T ℝ 1) = 0 := hlow 1
  have h2 : phaseContactDeflate q (Chebyshev.T ℝ 2) = 0 := hlow 2
  have h3 : phaseContactDeflate q (Chebyshev.T ℝ 3) = 0 := hlow 3
  have h4 : phaseContactDeflate q (Chebyshev.T ℝ 4) = 0 := hlow 4
  have h5 : phaseContactDeflate q (Chebyshev.T ℝ 7) = 0 := hlow 5
  simp only [Chebyshev.T_zero] at h0
  simp only [Chebyshev.T_one] at h1
  simp [Fin.sum_univ_succ, phaseContactFrequency, h0, h1, h2, h3, h4, h5]
  rfl

/-- Positivity of the quotient gives nonnegativity of the exact kernel
while keeping all four contact zeros. -/
theorem phaseContactExactKernel_nonneg_of_quotient {x : ℝ}
    (hx : 0 ≤ phaseContactExactQuotient.eval x) : 0 ≤ phaseContactExactKernel x := by
  rw [← phaseContactExactPolynomial_eval, phaseContactExactPolynomial_eq_factor_mul_quotient, eval_mul]
  apply mul_nonneg _ hx
  simp only [phaseContactFactor, eval_prod, eval_pow, eval_sub, eval_X, eval_C]
  exact Finset.prod_nonneg (fun _ _ ↦ sq_nonneg _)

end

end RiemannGaussian
