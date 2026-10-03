/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeQAggregate
import Mathlib.Algebra.MvPolynomial.Nilpotent
import Mathlib.Data.Int.Order.Units

/-!
# Content and height audit of the known-residue bivariate encoding

When A*C-N=B*D, the polynomial (B*x+A)*(B*y+C)-N has
the nonunit integer factor B. Dividing this guaranteed factor lowers its
height. The cleared idealised small-root budget requires N<B^4,
not the desired sixth-width regime. These are exact algebra and
budget statements; no lattice solver or factoring exponent is assumed.
-/

namespace RiemannGaussian.SemiprimeKnownBitsBudget

open MvPolynomial

/-- Two public unknown coordinates of the known-residue encoding. -/
abbrev Bivariate := MvPolynomial (Fin 2) ℤ

/-- The literal polynomial with N=A*C-B*D; its linear coefficients retain B. -/
noncomputable def originalForm (B : ℕ) (A C₀ D : ℤ) : Bivariate :=
  (C (B : ℤ)*X 0+C A)*(C (B : ℤ)*X 1+C C₀)-C (A*C₀-(B : ℤ)*D)

/-- The exact polynomial after dividing the guaranteed content B. -/
noncomputable def dividedForm (B : ℕ) (A C₀ D : ℤ) : Bivariate :=
  C (B : ℤ)*X 0*X 1+C C₀*X 0+C A*X 1+C D

/-- The whole polynomial, not merely its constant coefficient, has factor B. -/
theorem originalForm_eq_content (B : ℕ) (A C₀ D : ℤ) :
    originalForm B A C₀ D=C (B : ℤ)*dividedForm B A C₀ D := by
  simp only [originalForm,dividedForm,map_sub,map_mul]
  ring

/-- Every coefficient of the original polynomial is divisible by B. -/
theorem originalForm_coeff_dvd (B : ℕ) (A C₀ D : ℤ) (m : Fin 2 →₀ ℕ) :
    (B : ℤ)∣(originalForm B A C₀ D).coeff m := by
  rw [originalForm_eq_content,coeff_C_mul]
  exact dvd_mul_right _ _

/-- The mixed monomial makes the divided form nonconstant. -/
noncomputable def mixedExponent : Fin 2 →₀ ℕ := Finsupp.single 0 1+Finsupp.single 1 1

/-- The exact xy coefficient of the divided polynomial is B. -/
theorem dividedForm_mixed_coeff (B : ℕ) (A C₀ D : ℤ) :
    (dividedForm B A C₀ D).coeff mixedExponent=(B : ℤ) := by
  classical
  have hxy : (C (B : ℤ)*X 0*X 1 : Bivariate)=monomial mixedExponent (B : ℤ) := by
    rw [C_mul_X_eq_monomial]
    change monomial (Finsupp.single 0 1) (B : ℤ)*monomial (Finsupp.single 1 1) 1=_
    rw [monomial_mul,mul_one]
    rfl
  have h0 : Finsupp.single (0 : Fin 2) 1≠mixedExponent := by
    intro he
    have h := congrArg (fun m : Fin 2 →₀ ℕ => m 1) he
    norm_num [mixedExponent,Finsupp.single_apply] at h
  have h1 : Finsupp.single (1 : Fin 2) 1≠mixedExponent := by
    intro he
    have h := congrArg (fun m : Fin 2 →₀ ℕ => m 0) he
    norm_num [mixedExponent,Finsupp.single_apply] at h
  have hz : (0 : Fin 2 →₀ ℕ)≠mixedExponent := by
    intro he
    have h := congrArg (fun m : Fin 2 →₀ ℕ => m 0) he
    norm_num [mixedExponent,Finsupp.single_apply] at h
  rw [dividedForm,hxy,C_mul_X_eq_monomial,C_mul_X_eq_monomial]
  simp only [coeff_add,coeff_monomial,coeff_C,if_true,if_neg h0,if_neg h1,if_neg hz,add_zero]

/-- The mixed monomial is not the constant monomial. -/
theorem mixedExponent_ne_zero : mixedExponent≠0 := by
  intro he
  have h := congrArg (fun m : Fin 2 →₀ ℕ => m 0) he
  norm_num [mixedExponent,Finsupp.single_apply] at h

/-- Positive B makes the divided polynomial nonunit because its mixed coefficient survives. -/
theorem dividedForm_not_unit {B : ℕ} (hB : 0<B) (A C₀ D : ℤ) :
    ¬IsUnit (dividedForm B A C₀ D) := by
  intro hu
  obtain ⟨z,_,he⟩ := isUnit_iff_eq_C_of_isReduced.mp hu
  have hc := congrArg (fun p : Bivariate => p.coeff mixedExponent) he
  rw [dividedForm_mixed_coeff] at hc
  simp only [coeff_C,Ne.symm mixedExponent_ne_zero,if_false] at hc
  have hn : B=0 := by exact_mod_cast hc
  omega

/-- A modulus greater than one is a nonunit integer constant in the polynomial ring. -/
theorem content_not_unit {B : ℕ} (hB : 1<B) : ¬IsUnit (C (B : ℤ) : Bivariate) := by
  intro hu
  obtain ⟨z,hz,he⟩ := isUnit_iff_eq_C_of_isReduced.mp hu
  have heq : (B : ℤ)=z := C_injective (Fin 2) ℤ he
  rw [←heq] at hz
  have habs := Int.isUnit_iff_natAbs_eq.mp hz
  simp only [Int.natAbs_natCast] at habs
  omega

/-- The unscaled integer polynomial is reducible whenever B>1.
Rational irreducibility does not remove this integer-content factor. -/
theorem originalForm_not_irreducible {B : ℕ} (hB : 1<B) (A C₀ D : ℤ) :
    ¬Irreducible (originalForm B A C₀ D) := by
  intro hi
  rw [originalForm_eq_content] at hi
  rcases hi.isUnit_or_isUnit rfl with hc|hp
  · exact content_not_unit hB hc
  · exact dividedForm_not_unit (by omega) A C₀ D hp

/-- Correct clearing of the idealised XY=N/B² and W=N/B height
criterion leaves precisely the usual fourth-power modulus threshold. -/
theorem cleared_height_budget_iff {N B : ℕ} (hN : 0<N) :
    N^3<N^2*B^4 ↔ N<B^4 := by
  have he : N^3=N^2*N := by ring
  rw [he,Nat.mul_lt_mul_left (by positivity : 0<N^2)]

/-- At exact sixth-power scale, the correctly normalised idealised
height budget fails for every B>1. This is a budget audit, not an
impossibility theorem for all lattice or known-bit factoring algorithms. -/
theorem sixth_scale_fails_height_budget {B : ℕ} (hB : 1<B) :
    ¬(B^6)^3<(B^6)^2*B^4 := by
  rw [cleared_height_budget_iff (by positivity : 0<B^6)]
  have hle : B^4≤B^6 := Nat.pow_le_pow_right (by omega) (by omega)
  omega

/-- A concrete balanced semiprime gives original integer content four. -/
theorem control_integer_content :
    originalForm 4 65 67 (-1512)=C (4 : ℤ)*dividedForm 4 65 67 (-1512) ∧
    Nat.gcd (Nat.gcd 16 268) (Nat.gcd 260 6048)=4 ∧
    (4*(9 : ℤ)+65)*(4*9+67)=10403 ∧
    16*(9 : ℤ)*9+67*9+65*9-6048=-3564 ∧
    (101 : ℕ).Prime ∧ (103 : ℕ).Prime ∧ 101<103 ∧ 103<2*101 := by
  refine ⟨originalForm_eq_content _ _ _ _,?_,?_,?_,?_,?_,?_,?_⟩ <;> norm_num

end RiemannGaussian.SemiprimeKnownBitsBudget
