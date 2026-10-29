/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1DyadicCongruence
import RiemannGaussian.SemiprimeD1CurrentTableDeformation

/-! # Genuine linear old-coordinate extraction and scalar Taylor compatibility
Coordinate extraction is additive and Q-linear, NEVER a ring homomorphism.
Actual modular coefficient equality derives the scalar D.5 error contract.
-/
set_option autoImplicit false
set_option maxHeartbeats 1800000
namespace RiemannGaussian.SemiprimeD1JetCoordinateLinear
open scoped BigOperators
open Polynomial SemiprimeD1JetAlgebra SemiprimeD1JetScalarMap
  SemiprimeD1JetInterpretation SemiprimeD1DyadicInteger SemiprimeD1DyadicCongruence
noncomputable section

/-- Scalar multiplication of the actual old-jet quotient commutes with bounded extraction. -/
theorem coefficient_smul {σ : Type*} (dims : σ→ℕ) (e : σ→₀ℕ) (he : InBox dims e)
    (c : ℚ) (x : Algebra dims ℚ) : coefficient dims e he (c • x)=c*coefficient dims e he x := by
  induction x using Quotient.inductionOn with
  | h x =>
    change (MvPowerSeries.coeff e) (c • x)=c*(MvPowerSeries.coeff e) x
    exact MvPowerSeries.coeff_smul x e c

/-- The actual old-coordinate functional is Q-linear, including all nilpotent cross terms. -/
def coordinate {σ : Type*} (dims : σ→ℕ) (e : σ→₀ℕ) (he : InBox dims e) :
    Algebra dims ℚ →ₗ[ℚ] ℚ where
  toFun := coefficient dims e he
  map_add' := quotient_coefficient_add dims e he
  map_smul' c x := by simpa only [smul_eq_mul,RingHom.id_apply] using coefficient_smul dims e he c x

variable {R : Type*} [CommRing R] [Algebra ℚ R]

/-- Coefficientwise linear polynomial extraction, with its literal finite support. -/
def polynomial (L : R →ₗ[ℚ] ℚ) (F : Polynomial R) : Polynomial ℚ :=
  Polynomial.ofFinsupp (AddMonoidAlgebra.map L.toAddMonoidHom F.toFinsupp)

/-- Every extracted coefficient is the actual source coefficient's linear image. -/
theorem polynomial_coefficient (L : R →ₗ[ℚ] ℚ) (F : Polynomial R) (j : ℕ) :
    (polynomial L F).coeff j=L (F.coeff j) := rfl

/-- Coefficientwise extraction is additive. -/
theorem polynomial_add (L : R →ₗ[ℚ] ℚ) (F G : Polynomial R) :
    polynomial L (F+G)=polynomial L F+polynomial L G := by
  ext j
  simp only [polynomial_coefficient,Polynomial.coeff_add,map_add]

/-- Original coefficient monomials retain precisely their linear coefficient. -/
theorem polynomial_monomial (L : R →ₗ[ℚ] ℚ) (n : ℕ) (r : R) :
    polynomial L (Polynomial.monomial n r)=Polynomial.monomial n (L r) := by
  ext j
  simp only [polynomial_coefficient,Polynomial.coeff_monomial]
  split_ifs <;> simp only [map_zero]

/-- Scalar polynomial multiplication is licensed by linearity, not multiplicativity. -/
theorem polynomial_C_mul_map (L : R →ₗ[ℚ] ℚ) (r : R) (g : Polynomial ℚ) :
    polynomial L (C r*g.map (algebraMap ℚ R))=C (L r)*g := by
  ext j
  simp only [polynomial_coefficient,Polynomial.coeff_C_mul,Polynomial.coeff_map]
  have h := L.map_smul (g.coeff j) r
  simp only [Algebra.smul_def,Algebra.algebraMap_self_apply] at h
  simpa only [mul_comm] using h

/-- Linear coordinate extraction commutes with EVERY rational scalar substitution,
including the actual t+alphaZ Taylor substitution. -/
theorem polynomial_comp (L : R →ₗ[ℚ] ℚ) (F : Polynomial R) (g : Polynomial ℚ) :
    polynomial L (F.comp (g.map (algebraMap ℚ R)))=(polynomial L F).comp g := by
  induction F using Polynomial.induction_on' with
  | add F G hF hG =>
    simp only [Polynomial.add_comp,polynomial_add,hF,hG]
  | monomial n r =>
    rw [Polynomial.monomial_comp,← Polynomial.map_pow,polynomial_C_mul_map,
      polynomial_monomial,Polynomial.monomial_comp]

/-- Linear coordinate extraction never increases the ORIGINAL scalar-variable degree. -/
theorem polynomial_degree (L : R →ₗ[ℚ] ℚ) (F : Polynomial R) :
    (polynomial L F).natDegree≤F.natDegree := by
  apply Polynomial.natDegree_le_iff_coeff_eq_zero.mpr
  intro j hj
  rw [polynomial_coefficient,Polynomial.coeff_eq_zero_of_natDegree_lt hj,map_zero]

/-- The extracted polynomial's rational evaluation is the linear image of original evaluation. -/
theorem polynomial_eval (L : R →ₗ[ℚ] ℚ) (F : Polynomial R) (t : ℚ) :
    (polynomial L F).eval t=L (F.eval ((algebraMap ℚ R) t)) := by
  have h := congrArg (fun p : Polynomial ℚ => p.coeff 0) (polynomial_comp L F (C t))
  simp only [Polynomial.map_C,Polynomial.comp_C,polynomial_coefficient,Polynomial.coeff_C_zero] at h
  exact h.symm

/-- A computed modular OLD coordinate equality gives the ACTUAL scalar representative
error, with integral source coordinates retained instead of supplied as advice. -/
theorem old_coordinate_word_error {σ : Type*} (dims : σ→ℕ) (e : σ→₀ℕ)
    (he : InBox dims e) (p : ℕ) (source : Algebra dims integers) (bs : List Bool)
    (hchild : coefficient dims e he (scalarMap dims (reduction p) source)=
      (SemiprimeBitArithmetic.bitValue bs:ZMod (2^p))) :
    SemiprimeD1DyadicBounds.AtLeast (p:ℤ)
      ((SemiprimeBitArithmetic.bitValue bs:ℚ)-
        coefficient dims e he (scalarMap dims integers.subtype source)) := by
  rw [coefficient_scalarMap] at hchild ⊢
  exact source_word_error p (coefficient dims e he source) bs hchild

end
end RiemannGaussian.SemiprimeD1JetCoordinateLinear
