/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeHermiteArrayHeight

/-!
# Executed bounded-width jet addition and scaling

The reports count rational scalar operations and coefficient reads. Array
allocation and writes remain explicit polynomial-size control work.
-/
set_option autoImplicit false
namespace RiemannGaussian.SemiprimeArrayOps
open Polynomial
open SemiprimeJetArray SemiprimeJetRecurrence SemiprimeJetArrayHeight

/-- Actual zero array of the retained width. -/
def zeroJet (J : ℕ) : InverseReport := ⟨Array.replicate J 0, 0, 0⟩
/-- Actual truncated constant-one array. -/
def oneJet (J : ℕ) : InverseReport :=
  ⟨Array.ofFn (fun i : Fin J => if i.val = 0 then 1 else 0), 0, 0⟩
/-- Executed coefficientwise addition, reading no coefficients above the cutoff. -/
def addJet (a b : Array ℚ) (J : ℕ) : InverseReport :=
  ⟨Array.ofFn (fun i : Fin J => coefficient a i.val + coefficient b i.val), J, 2 * J⟩
/-- Executed coefficientwise rational scaling. -/
def scaleJet (a : Array ℚ) (c : ℚ) (J : ℕ) : InverseReport :=
  ⟨Array.ofFn (fun i : Fin J => c * coefficient a i.val), J, J⟩

theorem ofFn_coefficient {J : ℕ} (f : Fin J → ℚ) (i : ℕ) (hi : i < J) :
    coefficient (Array.ofFn f) i = f ⟨i, hi⟩ := by
  simp [coefficient, hi]

theorem zeroJet_size (J : ℕ) : (zeroJet J).coefficients.size = J := by simp [zeroJet]
theorem oneJet_size (J : ℕ) : (oneJet J).coefficients.size = J := by simp [oneJet]
theorem addJet_size (a b : Array ℚ) (J : ℕ) : (addJet a b J).coefficients.size = J := by simp [addJet]
theorem scaleJet_size (a : Array ℚ) (c : ℚ) (J : ℕ) : (scaleJet a c J).coefficients.size = J := by simp [scaleJet]

theorem zeroJet_coefficient (J i : ℕ) : coefficient (zeroJet J).coefficients i = 0 := by
  by_cases hi : i < J
  · simp [zeroJet, coefficient, hi]
  · exact coefficient_zero (by rw [zeroJet_size]; omega)
theorem oneJet_coefficient (J i : ℕ) (hi : i < J) :
    coefficient (oneJet J).coefficients i = if i = 0 then 1 else 0 := ofFn_coefficient _ _ hi
theorem addJet_coefficient (a b : Array ℚ) (J i : ℕ) (hi : i < J) :
    coefficient (addJet a b J).coefficients i = coefficient a i + coefficient b i := ofFn_coefficient _ _ hi
theorem scaleJet_coefficient (a : Array ℚ) (c : ℚ) (J i : ℕ) (hi : i < J) :
    coefficient (scaleJet a c J).coefficients i = c * coefficient a i := ofFn_coefficient _ _ hi

theorem zeroJet_correct (J : ℕ) : asPolynomial (zeroJet J).coefficients = 0 := by
  ext k
  rw [asPolynomial_coeff, zeroJet_coefficient, coeff_zero]

theorem oneJet_correct (J : ℕ) : asPolynomial (oneJet J).coefficients = (1 : Polynomial ℚ) %ₘ X ^ J := by
  ext k
  rw [asPolynomial_coeff, coeff_mod_X_pow]
  by_cases hk : k < J
  · rw [oneJet_coefficient J k hk, ite_eq_left hk]
    simp only [coeff_one]
  · rw [coefficient_zero (by rw [oneJet_size]; omega), ite_eq_right hk]

theorem addJet_correct (a b : Array ℚ) (J : ℕ) (P Q : Polynomial ℚ)
    (ha : ∀ i < J, coefficient a i = P.coeff i)
    (hb : ∀ i < J, coefficient b i = Q.coeff i) :
    asPolynomial (addJet a b J).coefficients = (P + Q) %ₘ X ^ J := by
  ext k
  rw [asPolynomial_coeff, coeff_mod_X_pow]
  by_cases hk : k < J
  · rw [addJet_coefficient a b J k hk, ite_eq_left hk, coeff_add, ha k hk, hb k hk]
  · rw [coefficient_zero (by rw [addJet_size]; omega), ite_eq_right hk]

theorem scaleJet_correct (a : Array ℚ) (c : ℚ) (J : ℕ) (P : Polynomial ℚ)
    (ha : ∀ i < J, coefficient a i = P.coeff i) :
    asPolynomial (scaleJet a c J).coefficients = (C c * P) %ₘ X ^ J := by
  ext k
  rw [asPolynomial_coeff, coeff_mod_X_pow]
  by_cases hk : k < J
  · rw [scaleJet_coefficient a c J k hk, ite_eq_left hk, coeff_C_mul, ha k hk]
  · rw [coefficient_zero (by rw [scaleJet_size]; omega), ite_eq_right hk]

theorem addJet_work (a b : Array ℚ) (J : ℕ) :
    (addJet a b J).arithmetic = J ∧ (addJet a b J).reads = 2 * J := ⟨rfl, rfl⟩
theorem scaleJet_work (a : Array ℚ) (c : ℚ) (J : ℕ) :
    (scaleJet a c J).arithmetic = J ∧ (scaleJet a c J).reads = J := ⟨rfl, rfl⟩

theorem addJet_representation (a b : Array ℚ) (J d B C : ℕ)
    (ha : ∀ i < J, Representation (coefficient a i) d B)
    (hb : ∀ i < J, Representation (coefficient b i) d C) (i : ℕ) (hi : i < J) :
    Representation (coefficient (addJet a b J).coefficients i) d (B + C) := by
  rw [addJet_coefficient a b J i hi]
  exact representation_add (ha i hi) (hb i hi)

theorem scaleJet_representation (a : Array ℚ) (c : ℚ) (J d e B C : ℕ)
    (ha : ∀ i < J, Representation (coefficient a i) d B) (hc : Representation c e C)
    (i : ℕ) (hi : i < J) :
    Representation (coefficient (scaleJet a c J).coefficients i) (e * d) (C * B) := by
  rw [scaleJet_coefficient a c J i hi]
  exact representation_mul hc (ha i hi)

/-- A low-coefficient specification is precisely the truncated polynomial identity. -/
theorem specification (a : Array ℚ) (P : Polynomial ℚ) (J : ℕ)
    (ha : ∀ i < J, coefficient a i = P.coeff i) :
    asPolynomial a %ₘ X ^ J = P %ₘ X ^ J := by
  ext k
  rw [coeff_mod_X_pow, coeff_mod_X_pow]
  by_cases hk : k < J
  · rw [ite_eq_left hk, ite_eq_left hk, asPolynomial_coeff, ha k hk]
  · rw [ite_eq_right hk, ite_eq_right hk]

theorem specification_of_asPolynomial (a : Array ℚ) (P : Polynomial ℚ) (J : ℕ)
    (ha : asPolynomial a = P %ₘ X ^ J) (i : ℕ) (hi : i < J) : coefficient a i = P.coeff i := by
  rw [← asPolynomial_coeff, ha, coeff_mod_X_pow, ite_eq_left hi]

/-- Cached multiplication under arbitrary low-coefficient input specifications. -/
theorem multiply_correct (a b : Array ℚ) (J : ℕ) (P Q : Polynomial ℚ)
    (ha : ∀ i < J, coefficient a i = P.coeff i)
    (hb : ∀ i < J, coefficient b i = Q.coeff i) :
    asPolynomial (multiply a b J).coefficients = (P * Q) %ₘ X ^ J := by
  rw [multiply_asPolynomial]
  calc
    _ = ((asPolynomial a %ₘ X ^ J) * (asPolynomial b %ₘ X ^ J)) %ₘ X ^ J := mul_modByMonic _ _ _
    _ = ((P %ₘ X ^ J) * (Q %ₘ X ^ J)) %ₘ X ^ J := by
      rw [specification a P J ha, specification b Q J hb]
    _ = _ := (mul_modByMonic _ _ _).symm

end RiemannGaussian.SemiprimeArrayOps
