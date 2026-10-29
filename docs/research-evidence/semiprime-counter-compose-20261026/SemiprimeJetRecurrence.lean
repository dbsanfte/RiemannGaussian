/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeHermiteRecovery

/-!
# Executed finite jet arithmetic and inverse recurrence

Coefficient arrays are represented by functions with an explicit retained width.
The inverse coefficients follow the actual finite recurrence of Jets.inverse.
No primitive-machine or bit-cost bound is asserted here.
-/
namespace RiemannGaussian.SemiprimeJetRecurrence
open Polynomial
open scoped BigOperators
open RiemannGaussian.SemiprimeHermiteRecovery

/-- The literal recursive inverse coefficient, with smaller-index recursive calls. -/
def inverseCoeff (a : ℕ → ℚ) : ℕ → ℚ
  | 0 => (a 0)⁻¹
  | n+1 => -(a 0)⁻¹ * ∑ i ∈ Finset.range (n+1), a (i+1) * inverseCoeff a (n-i)
termination_by n => n

theorem inverseCoeff_convolution (a : ℕ → ℚ) (ha : a 0 ≠ 0) (n : ℕ) :
    (∑ i ∈ Finset.range (n+1), a i * inverseCoeff a (n-i)) = if n=0 then 1 else 0 := by
  cases n with
  | zero => simp [inverseCoeff, ha]
  | succ n =>
    rw [Finset.sum_range_succ']
    simp only [Nat.add_sub_add_right, Nat.sub_zero]
    rw [inverseCoeff]
    rw [ite_eq_right (Nat.succ_ne_zero n)]
    field_simp
    ring

/-- A finite jet encoded as an ordinary polynomial, without coefficients past J. -/
noncomputable def jetPolynomial (a : ℕ → ℚ) (J : ℕ) : Polynomial ℚ :=
  ∑ k ∈ Finset.range J, monomial k (a k)

theorem jetPolynomial_coeff (a : ℕ → ℚ) (J k : ℕ) :
    (jetPolynomial a J).coeff k = if k<J then a k else 0 := by
  simp [jetPolynomial, finsetSum_coeff, coeff_monomial, eq_comm]

/-- Monic polynomial remainder has exactly the retained coefficient semantics. -/
theorem coeff_mod_X_pow (p : Polynomial ℚ) (J k : ℕ) :
    (p %ₘ X^J).coeff k = if k<J then p.coeff k else 0 := by
  by_cases hk : k<J
  · rw [ite_eq_left hk]
    have h := dvd_modByMonic_sub p (X^J)
    rw [X_pow_dvd_iff] at h
    have hz := h k hk
    simpa only [coeff_sub, sub_eq_zero] using hz
  · rw [ite_eq_right hk]
    by_cases hJ : J=0
    · subst J; simp
    · have hne : (X : Polynomial ℚ)^J ≠ 1 := by
        intro h
        have := congrArg natDegree h
        simp at this
        omega
      have hd := natDegree_modByMonic_lt p (monic_X.pow J) hne
      simp only [natDegree_X_pow] at hd
      exact coeff_eq_zero_of_natDegree_lt (by omega)

theorem jetPolynomial_eq_mod (p : Polynomial ℚ) (J : ℕ) :
    jetPolynomial p.coeff J = p %ₘ X^J := by
  ext k
  rw [jetPolynomial_coeff, coeff_mod_X_pow]

/-- Componentwise addition, exactly as in Jets.add. -/
theorem jet_add (a b : ℕ → ℚ) (J : ℕ) :
    jetPolynomial (fun k => a k+b k) J =
      (jetPolynomial a J+jetPolynomial b J) %ₘ X^J := by
  ext k
  rw [coeff_mod_X_pow, coeff_add, jetPolynomial_coeff, jetPolynomial_coeff, jetPolynomial_coeff]
  split_ifs <;> simp_all

/-- Truncated convolution, exactly as in Jets.mul. -/
theorem jet_mul (a b : ℕ → ℚ) (J : ℕ) :
    jetPolynomial (fun k => ∑ i ∈ Finset.range (k+1), a i*b (k-i)) J =
      (jetPolynomial a J*jetPolynomial b J) %ₘ X^J := by
  ext k
  rw [jetPolynomial_coeff, coeff_mod_X_pow]
  split_ifs with hk
  · rw [coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
    apply Finset.sum_congr rfl
    intro i hi
    have hi' := Finset.mem_range.mp hi
    rw [jetPolynomial_coeff, jetPolynomial_coeff, ite_eq_left (by omega), ite_eq_left (by omega)]
  · rfl

/-- The recurrence, not an inverse-equation hypothesis, gives the inverse jet. -/
theorem inversePolynomial_congruence (p : Polynomial ℚ) (hp : p.coeff 0 ≠ 0) (J : ℕ) :
    X^J ∣ p * jetPolynomial (inverseCoeff p.coeff) J-1 := by
  rw [X_pow_dvd_iff]
  intro k hk
  rw [coeff_sub, coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  have hs : (∑ i ∈ Finset.range (k+1), p.coeff i *
      (jetPolynomial (inverseCoeff p.coeff) J).coeff (k-i)) =
      ∑ i ∈ Finset.range (k+1), p.coeff i * inverseCoeff p.coeff (k-i) := by
    apply Finset.sum_congr rfl
    intro i hi
    rw [jetPolynomial_coeff, ite_eq_left (by omega)]
  rw [hs, inverseCoeff_convolution p.coeff hp]
  simp only [coeff_one]
  split_ifs <;> simp_all

/-- Two genuine inverse congruences imply equal retained inverse output. -/
theorem inverse_congruences_difference (L B C : Polynomial ℚ) (J : ℕ)
    (hB : X^J ∣ L*B-1) (hC : X^J ∣ L*C-1) : X^J ∣ B-C := by
  have h := dvd_sub (hB.mul_right C) (hC.mul_right B)
  convert h using 1; ring

/-- The executed inverse gives the same retained local quotient as the
finite-geometric inverse already used in Hermite recovery. -/
theorem recurrence_localQuotient (H L : Polynomial ℚ) (J : ℕ) (hL : L.coeff 0 = 1) :
    (H*jetPolynomial (inverseCoeff L.coeff) J) %ₘ X^J = localQuotient H L J := by
  unfold localQuotient
  apply modByMonic_eq_of_dvd_sub (monic_X.pow J)
  have hrec := inversePolynomial_congruence L (by rw [hL]; norm_num) J
  have hgeo := inverseJet_congruence L J hL
  have hd := (inverse_congruences_difference L _ _ J hrec hgeo).mul_left H
  simpa only [mul_sub] using hd

/-- Truncating the denominator packet first, as the code does, is sound too. -/
theorem packet_recurrence_localQuotient (H L : Polynomial ℚ) (J : ℕ)
    (hJ : 0 < J) (hL : L.coeff 0 = 1) :
    (H*jetPolynomial (inverseCoeff (L %ₘ X^J).coeff) J) %ₘ X^J = localQuotient H L J := by
  have hp : (L %ₘ X^J).coeff 0 = 1 := by
    rw [coeff_mod_X_pow, ite_eq_left hJ, hL]
  have hrec := inversePolynomial_congruence (L %ₘ X^J) (by rw [hp]; norm_num) J
  have hmod := (dvd_modByMonic_sub L (X^J)).mul_right
    (jetPolynomial (inverseCoeff (L %ₘ X^J).coeff) J)
  have hactual : X^J ∣ L*jetPolynomial (inverseCoeff (L %ₘ X^J).coeff) J-1 := by
    have h := dvd_sub hrec hmod
    convert h using 1; ring
  unfold localQuotient
  apply modByMonic_eq_of_dvd_sub (monic_X.pow J)
  have hd := (inverse_congruences_difference L _ _ J hactual
    (inverseJet_congruence L J hL)).mul_left H
  simpa only [mul_sub] using hd

#print axioms recurrence_localQuotient
#print axioms packet_recurrence_localQuotient
#print axioms inverseCoeff_convolution
#print axioms inversePolynomial_congruence
#print axioms jet_add
#print axioms jet_mul
end RiemannGaussian.SemiprimeJetRecurrence
