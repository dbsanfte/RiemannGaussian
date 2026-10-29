/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1JetInterpretation

/-! # Exact finite polynomial coefficients at a fresh nilpotent axis
No domain, field, or multiplicative valuation assumption is used. Retained fresh
coefficients are literal polynomial coefficients in the ENTIRE old jet ring.
-/
set_option autoImplicit false
set_option maxHeartbeats 1800000
namespace RiemannGaussian.SemiprimeD1JetPolynomialCoefficient
open scoped BigOperators
open Polynomial SemiprimeD1JetAlgebra SemiprimeD1JetInterpretation
noncomputable section
variable {m : ℕ} {R : Type*} [CommRing R]

/-- Fresh exponent j and ALL original old exponents. -/
def blockExponent (j : ℕ) (e : Fin m→₀ℕ) : Fin (m+1)→₀ℕ :=
  Finsupp.single 0 j+Finsupp.embDomain (axisShift m) e

/-- Shifted old exponents have no fresh coordinate. -/
theorem shifted_zero (e : Fin m→₀ℕ) : (Finsupp.embDomain (axisShift m) e) 0=0 := by
  apply Finsupp.embDomain_of_notMem_range
  rintro ⟨i,hi⟩
  exact Fin.succ_ne_zero i hi

/-- The block exponent has exactly the requested fresh exponent. -/
theorem block_zero (j : ℕ) (e : Fin m→₀ℕ) : blockExponent j e 0=j := by
  simp only [blockExponent,Finsupp.add_apply,Finsupp.single_eq_same,shifted_zero,Nat.add_zero]

/-- Every retained polynomial block belongs to the actual rectangular quotient box. -/
theorem block_inBox (q : ℕ) (dims : Fin m→ℕ) (j : ℕ) (hj : j<q)
    (e : Fin m→₀ℕ) (he : InBox dims e) : InBox (outerDims q dims) (blockExponent j e) := by
  intro i
  refine Fin.cases ?_ (fun k => ?_) i
  · simpa only [block_zero,outerDims,Fin.cases_zero] using hj
  · change (Finsupp.single (0:Fin (m+1)) j) k.succ+
      (Finsupp.embDomain (axisShift m) e) ((axisShift m) k)<dims k
    simpa only [Finsupp.single_apply,Ne.symm (Fin.succ_ne_zero k),ite_false,Nat.zero_add,
      Finsupp.embDomain_apply_self] using he k

/-- The original renamed series has exactly one fresh monomial degree after multiplication. -/
theorem series_monomial_coefficient (f : MvPowerSeries (Fin m) R) (e : Fin m→₀ℕ) (j n : ℕ) :
    MvPowerSeries.coeff (blockExponent j e)
      (MvPowerSeries.rename (axisShift m) f*(MvPowerSeries.X (0:Fin (m+1)))^n)=
      if n=j then MvPowerSeries.coeff e f else 0 := by
  classical
  rw [MvPowerSeries.X_pow_eq,MvPowerSeries.coeff_mul_monomial]
  by_cases hn : n≤j
  · have hle : Finsupp.single (0:Fin (m+1)) n≤blockExponent j e := by
      intro i
      refine Fin.cases ?_ (fun k => ?_) i
      · simpa only [Finsupp.single_eq_same,block_zero] using hn
      · simp only [Finsupp.single_apply,Ne.symm (Fin.succ_ne_zero k),ite_false]
        exact Nat.zero_le _
    rw [ite_eq_left hle,mul_one]
    by_cases hnj : n=j
    · subst n
      have hsub : blockExponent j e-Finsupp.single 0 j=Finsupp.embDomain (axisShift m) e := by
        unfold blockExponent
        exact add_tsub_cancel_left _ _
      rw [hsub,MvPowerSeries.coeff_embDomain_rename,ite_eq_left rfl]
    · have hpos : 0<(blockExponent j e-(Finsupp.single (0:Fin (m+1)) n) : Fin (m+1)→₀ℕ) 0 := by
        simp only [Finsupp.tsub_apply,block_zero,Finsupp.single_eq_same]
        omega
      have hnot : blockExponent j e-Finsupp.single 0 n∉Set.range (Finsupp.mapDomain (axisShift m)) := by
        rintro ⟨d,hd⟩
        rw [← Finsupp.embDomain_eq_mapDomain] at hd
        have hz := congrArg (fun z => z (0:Fin (m+1))) hd
        rw [shifted_zero] at hz
        omega
      rw [MvPowerSeries.coeff_rename_eq_zero (axisShift m) f hnot,ite_eq_right hnj]
  · have hnot : ¬Finsupp.single (0:Fin (m+1)) n≤blockExponent j e := by
      intro h
      have hz := h 0
      simp only [Finsupp.single_eq_same,block_zero] at hz
      exact hn hz
    rw [ite_eq_right hnot,ite_eq_right (by omega : n≠j)]

/-- Exact polynomial-monomial extraction in the actual quotient, including old zero divisors. -/
theorem monomial_coefficient (q : ℕ) (dims : Fin m→ℕ) (j : ℕ) (hj : j<q)
    (e : Fin m→₀ℕ) (he : InBox dims e) (n : ℕ) (c : Algebra dims R) :
    coefficient (outerDims q dims) (blockExponent j e) (block_inBox q dims j hj e he)
      (outerEmbedding q dims c*(fresh q dims)^n)=
      if n=j then coefficient dims e he c else 0 := by
  induction c using Quotient.inductionOn with
  | h c =>
    change coefficient (outerDims q dims) (blockExponent j e) (block_inBox q dims j hj e he)
      (outerEmbedding q dims (project dims c)*(project (outerDims q dims) (MvPowerSeries.X 0))^n)=_
    rw [outerEmbedding_project,←map_pow,←map_mul,coefficient_project]
    change _=if n=j then MvPowerSeries.coeff e c else 0
    exact series_monomial_coefficient c e j n

/-- The retained fresh-j coefficient is EXACTLY F.coeffj in ALL old coordinates. -/
theorem polynomial_coefficient (q : ℕ) (dims : Fin m→ℕ) (j : ℕ) (hj : j<q)
    (e : Fin m→₀ℕ) (he : InBox dims e) (F : Polynomial (Algebra dims R)) :
    coefficient (outerDims q dims) (blockExponent j e) (block_inBox q dims j hj e he)
      (F.eval₂ (outerEmbedding q dims) (fresh q dims))=
      coefficient dims e he (F.coeff j) := by
  classical
  induction F using Polynomial.induction_on' with
  | add F G hF hG =>
    simp only [Polynomial.eval₂_add,quotient_coefficient_add,Polynomial.coeff_add,hF,hG]
  | monomial n c =>
    rw [Polynomial.eval₂_monomial,monomial_coefficient q dims j hj e he n c,Polynomial.coeff_monomial]
    split_ifs <;> simp only [quotient_coefficient_zero]

end
end RiemannGaussian.SemiprimeD1JetPolynomialCoefficient
