/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaPhaseContactPrimal
import Mathlib.Algebra.Polynomial.FieldDivision
import Mathlib.RingTheory.Coprime.Lemmas

/-!
# Exact double-contact factorization of the phase candidate

The four contact cosines are distinct. The exact kernel has zero value and
zero derivative at each, so it contains all four squared linear factors.
The remaining factor has degree at most sixteen. This removes the flat
contact zeros from the subsequent global positivity problem without
asserting that the remaining factor is already positive.
-/

open scoped Classical Polynomial
open Polynomial

namespace RiemannGaussian

noncomputable section

private theorem phase_square_factor_dvd {p : ℝ[X]} {q : ℝ}
    (hp : p.eval q = 0) (hd : p.derivative.eval q = 0) : (X - C q) ^ 2 ∣ p := by
  obtain ⟨a, ha⟩ := (Polynomial.dvd_iff_isRoot).mpr hp
  have ha0 : a.eval q = 0 := by
    rw [ha] at hd
    simpa using hd
  obtain ⟨b, hb⟩ := (Polynomial.dvd_iff_isRoot).mpr ha0
  refine ⟨b, ?_⟩
  rw [ha, hb, pow_two, mul_assoc]

private theorem phase_four_factor_dvd {p : ℝ[X]} {q : Fin 4 → ℝ}
    (hq : Function.Injective q) (hp : ∀ j, p.eval (q j) = 0)
    (hd : ∀ j, p.derivative.eval (q j) = 0) :
    (∏ j : Fin 4, (X - C (q j)) ^ 2) ∣ p := by
  apply Fintype.prod_dvd_of_coprime
  · intro i j hij
    exact (Polynomial.pairwise_coprime_X_sub_C hq hij).pow
  · intro j
    exact phase_square_factor_dvd (hp j) (hd j)

private theorem phase_four_factor_natDegree (q : Fin 4 → ℝ) :
    (∏ j : Fin 4, (X - C (q j)) ^ 2).natDegree = 8 := by
  rw [Polynomial.natDegree_prod]
  · norm_num
  · intro i _
    exact pow_ne_zero 2 (X_sub_C_ne_zero (q i))

private theorem phase_four_factor_quotient {p : ℝ[X]} (hp0 : p ≠ 0) (hpdegree : p.natDegree ≤ 24)
    {q : Fin 4 → ℝ} (hq : Function.Injective q) (hp : ∀ j, p.eval (q j) = 0)
    (hd : ∀ j, p.derivative.eval (q j) = 0) :
    ∃ r : ℝ[X], r.natDegree ≤ 16 ∧ p = (∏ j : Fin 4, (X - C (q j)) ^ 2) * r := by
  obtain ⟨r, hr⟩ := phase_four_factor_dvd hq hp hd
  have hprod0 : (∏ j : Fin 4, (X - C (q j)) ^ 2) ≠ 0 := by
    apply Finset.prod_ne_zero_iff.mpr
    intro i _
    exact pow_ne_zero 2 (X_sub_C_ne_zero (q i))
  have hr0 : r ≠ 0 := by intro h; rw [hr, h, mul_zero] at hp0; exact hp0 rfl
  have hdegree := Polynomial.natDegree_mul hprod0 hr0
  rw [← hr, phase_four_factor_natDegree] at hdegree
  exact ⟨r, by omega, hr⟩
/-- The exact kernel as a polynomial, keeping its original Chebyshev expansion. -/
def phaseContactExactPolynomial : ℝ[X] :=
  ∑ i : Fin 9, C (phaseContactExactCoefficients i) * Chebyshev.T ℝ (phaseContactFrequency i : ℤ)

/-- Polynomial evaluation recovers the exact phase kernel. -/
theorem phaseContactExactPolynomial_eval (x : ℝ) :
    phaseContactExactPolynomial.eval x = phaseContactExactKernel x := by
  simp [phaseContactExactPolynomial, phaseContactExactKernel, phaseChebyshevValue, Polynomial.eval_finsetSum]

/-- The proved contact cosines are strictly ordered, hence all four contacts
remain distinct after replacing the numerical candidate by the exact root. -/
theorem phaseContactExactRoot_cosine_strictAnti :
    StrictAnti (fun j : Fin 4 ↦ phaseContactExactRoot (phaseContactCosineCoordinate j)) := by
  intro i j hij
  have hc : (1 / 25 : ℝ) ≤ phaseContactRootCenter (phaseContactCosineCoordinate i) -
      phaseContactRootCenter (phaseContactCosineCoordinate j) := by
    have hNat : i.val < j.val := hij
    fin_cases i <;> fin_cases j <;> norm_num at hNat <;>
      norm_num [phaseContactRootCenter, phaseContactRootCenterQ, phaseContactCosineCoordinate]
  have hdi : |phaseContactExactRoot (phaseContactCosineCoordinate i) -
      phaseContactRootCenter (phaseContactCosineCoordinate i)| ≤ (1 / 10 ^ 30 : ℝ) :=
    (norm_le_pi_norm (phaseContactExactRoot - phaseContactRootCenter) (phaseContactCosineCoordinate i)).trans
      phaseContactExactRoot_dist_le
  have hdj : |phaseContactExactRoot (phaseContactCosineCoordinate j) -
      phaseContactRootCenter (phaseContactCosineCoordinate j)| ≤ (1 / 10 ^ 30 : ℝ) :=
    (norm_le_pi_norm (phaseContactExactRoot - phaseContactRootCenter) (phaseContactCosineCoordinate j)).trans
      phaseContactExactRoot_dist_le
  have hi := (abs_le.mp hdi).1
  have hj := (abs_le.mp hdj).2
  linarith

/-- The exact polynomial is nonzero, as its positive coefficients sum to
a strictly positive value at cosine coordinate one. -/
theorem phaseContactExactPolynomial_ne_zero : phaseContactExactPolynomial ≠ 0 := by
  have ht (n : ℕ) : phaseChebyshevValue n 1 = 1 := by
    simpa using phaseChebyshevValue_cos n 0
  have hp : 0 < phaseContactExactPolynomial.eval 1 := by
    rw [phaseContactExactPolynomial_eval]
    simp only [phaseContactExactKernel, ht, mul_one]
    exact Finset.sum_pos (fun i _ ↦ phaseContactExactCoefficients_pos i) Finset.univ_nonempty
  intro he
  rw [he, eval_zero] at hp
  exact (lt_irrefl 0) hp

/-- No frequency beyond 24 enters the constructed polynomial. -/
theorem phaseContactExactPolynomial_natDegree_le : phaseContactExactPolynomial.natDegree ≤ 24 := by
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro i _
  calc
    _ ≤ (Chebyshev.T ℝ (phaseContactFrequency i : ℤ)).natDegree := Polynomial.natDegree_C_mul_le _ _
    _ = phaseContactFrequency i := by simp [Chebyshev.natDegree_T]
    _ ≤ 24 := by fin_cases i <;> norm_num [phaseContactFrequency]

/-- The exact phase kernel factors into its four squared contact factors
and a polynomial of degree at most sixteen. The quotient is not assumed positive. -/
theorem exists_phaseContactExactPolynomial_quotient :
    ∃ r : ℝ[X], r.natDegree ≤ 16 ∧ phaseContactExactPolynomial =
      (∏ j : Fin 4, (X - C (phaseContactExactRoot (phaseContactCosineCoordinate j))) ^ 2) * r := by
  apply phase_four_factor_quotient phaseContactExactPolynomial_ne_zero phaseContactExactPolynomial_natDegree_le
    phaseContactExactRoot_cosine_strictAnti.injective
  · intro j
    rw [phaseContactExactPolynomial_eval, phaseContactExactKernel_contact]
  · intro j
    have h := phaseContactExactPolynomial.hasDerivAt (phaseContactExactRoot (phaseContactCosineCoordinate j))
    have he : (fun x : ℝ ↦ phaseContactExactPolynomial.eval x) = phaseContactExactKernel := by
      ext x
      exact phaseContactExactPolynomial_eval x
    rw [he] at h
    exact h.unique (hasDerivAt_phaseContactExactKernel_contact j)

end

end RiemannGaussian
