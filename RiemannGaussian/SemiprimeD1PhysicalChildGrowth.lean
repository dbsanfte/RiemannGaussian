/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1PhysicalChildPolynomial

/-! # Fixed monomial growth after original child resource substitution
Only actual scalar-resource polynomials are composed; source menu multiplicity
stays outside these factors and is charged by the real child inventory.
-/
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace RiemannGaussian.SemiprimeD1PhysicalChildGrowth
open SemiprimeReportPolynomialGrowth SemiprimeD1PhysicalChildPolynomial

/-- Ordinary scalar polynomial bounds lift to the exponent/cardinality domain. -/
theorem lift_bound {f : ℕ → ℕ} (hf : Bound f) :
    SemiprimeD1ChildPrefactorPolynomial.Bound (fun S _ => f S) := by
  obtain ⟨C,k,hf⟩:=hf
  exact ⟨C,k,by intro S a ha hp; exact hf S⟩

/-- Scalar enlargement preserves fixed polynomial growth without changing the
actual original exponent or grid cardinality. -/
theorem compose_bound {f : ℕ → ℕ → ℕ} {g : ℕ → ℕ}
    (hf : SemiprimeD1ChildPrefactorPolynomial.Bound f) (hg : Bound g)
    (hlarge : ∀ S,S ≤ g S) :
    SemiprimeD1ChildPrefactorPolynomial.Bound (fun S a => f (g S) a) := by
  obtain ⟨C,k,hf⟩:=hf
  obtain ⟨A,d,hg⟩:=hg
  refine ⟨C*(A+1)^k,d*k,?_⟩
  intro S a ha hp
  have hpow : 1 ≤ (S+1)^d := Nat.one_le_pow _ _ (by omega)
  have hbase : g S+1 ≤ (A+1)*(S+1)^d := by nlinarith only [hg S,hpow]
  calc
    _ ≤ C*(g S+1)^k := hf _ _ (ha.trans (hlarge S)) (hp.trans (hlarge S))
    _ ≤ C*((A+1)*(S+1)^d)^k := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hbase k)
    _ = _ := by rw [mul_pow,←pow_mul];ring

/-- The explicit scalar enlargement is polynomial. -/
theorem inflation_monomial : Bound inflation := by
  unfold inflation
  boundArithmetic

/-- Every scalar/context cap used for actual original children is polynomial. -/
theorem scalarCap_monomial : Bound scalarCap := by
  unfold scalarCap
  apply add_bound inflation_monomial
  exact SemiprimeD1PhysicalNetworkSourceBudget.compose_bound
    SemiprimeD1ChildMetadataPolynomial.envelope_monomial inflation_monomial

/-- Actual original child scalar prefactors retain fixed uniform monomial witnesses. -/
theorem prefactor_monomial : SemiprimeD1ChildPrefactorPolynomial.Bound
    (fun S a => SemiprimeD1ChildPrefactorPolynomial.envelope (scalarCap S) a) := by
  apply compose_bound SemiprimeD1ChildPrefactorPolynomial.envelope_monomial scalarCap_monomial
  intro S
  exact (le_inflation S).trans (Nat.le_add_right _ _)



/-- Actual fresh-word production has fixed polynomial scalar overhead. -/
theorem freshBudget_monomial : Bound freshBudget := by
  unfold freshBudget inflation
  boundArithmetic

/-- The source/menu factor of the ACTUAL original child bound is polynomial.
Its acquired menu cardinality is deliberately not hidden in this factor. -/
theorem factor_monomial : SemiprimeD1ChildPrefactorPolynomial.Bound factor := by
  change SemiprimeD1ChildPrefactorPolynomial.Bound (fun S a => factor S a)
  unfold factor
  apply SemiprimeD1ChildPrefactorPolynomial.add_bound
  · apply SemiprimeD1ChildPrefactorPolynomial.mul_bound
    · exact SemiprimeD1ChildPrefactorPolynomial.add_bound
        SemiprimeD1ChildPrefactorPolynomial.scalar_bound
        (SemiprimeD1ChildPrefactorPolynomial.constant_bound 1)
    · apply SemiprimeD1ChildPrefactorPolynomial.add_bound
      · exact lift_bound SemiprimeD1PhysicalNetworkSourceBudget.factor_monomial
      · exact lift_bound freshBudget_monomial
  · exact prefactor_monomial

end RiemannGaussian.SemiprimeD1PhysicalChildGrowth
