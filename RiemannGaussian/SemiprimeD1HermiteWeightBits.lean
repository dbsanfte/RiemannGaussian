/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1HermiteWeightHeight

/-! # Actual original scalar-weight polynomial logarithmic heights
Both the stored weights and every defined coefficient-sum prefix have explicit
original-derived dyadic caps. A full-grid weight-denominator product is also
acquired and bounded, without multiplying denominators recursively at each sum.
-/
set_option autoImplicit false
namespace RiemannGaussian.SemiprimeD1HermiteWeightBits
open scoped BigOperators
open SemiprimeJetArray SemiprimeJetArrayHeight SemiprimeD1WireKernelOriginal
  SemiprimeD1TaperedLoss SemiprimeD1JetRecoveryGrid SemiprimeD1JetRecoveryWeights
  SemiprimeD1HermiteNodes SemiprimeD1WeightPrecision
  SemiprimeD1HermiteDenominatorHeight SemiprimeD1HermiteDenominatorBits
  SemiprimeD1HermiteWeightHeight

/-- Original-derived logarithmic cap covering all retained weight scalars at one node. -/
def weightExponent (a h u t : ℕ) : ℕ :=
  SemiprimeD1JetRecoveryScalarHeight.bitExponent a h u+nodeMultiplicity a h u t+
    inverseExponent a h u t+(a+1)*nodeMultiplicity a h u t+1

/-- Actual raw E_t0 scalar products have the earlier original dyadic bound. -/
theorem scalar_bounds (a h u : ℕ) (t : Fin (size a)) :
    scalarNumerator a h u t.val≤2^SemiprimeD1JetRecoveryScalarHeight.bitExponent a h u ∧
    scalarDenominator a h u t.val≤2^SemiprimeD1JetRecoveryScalarHeight.bitExponent a h u :=
  SemiprimeD1JetRecoveryScalarHeight.original_dyadic_height a h u t

/-- The actual LOCAL weight common denominator and numerator envelope have
polynomial logarithmic heights, derived from ORIGINAL data alone. -/
theorem weight_bounds (a h u : ℕ) (t : Fin (size a)) :
    weightDenominator a h u t.val≤2^weightExponent a h u t.val ∧
    weightNumerator a h u t.val≤2^weightExponent a h u t.val := by
  have hs := scalar_bounds a h u t
  have hi := inverse_power_bounds a h u t
  let q := nodeMultiplicity a h u t.val
  have hq : q≤2^q := self_le_two_power q
  have hN : (size a)^q=2^((a+1)*q) := by rw [SemiprimeD1WireKernelOriginal.size,← pow_mul]
  constructor
  · unfold weightDenominator
    rw [mul_pow,hN]
    calc
      _ ≤ 2^SemiprimeD1JetRecoveryScalarHeight.bitExponent a h u*
          (2^inverseExponent a h u t.val*2^((a+1)*q)) := Nat.mul_le_mul hs.2 (Nat.mul_le_mul_right _ hi.1)
      _ = 2^(SemiprimeD1JetRecoveryScalarHeight.bitExponent a h u+inverseExponent a h u t.val+(a+1)*q) := by
        simp only [← pow_add,Nat.add_assoc]
      _ ≤ _ := Nat.pow_le_pow_right (by decide : 0<(2:ℕ)) (by unfold weightExponent;dsimp [q];omega)
  · unfold weightNumerator
    rw [mul_pow,hN]
    calc
      _ ≤ (2^SemiprimeD1JetRecoveryScalarHeight.bitExponent a h u*2^q)*
          (2^inverseExponent a h u t.val*2^((a+1)*q)) :=
        Nat.mul_le_mul (Nat.mul_le_mul hs.1 hq) (Nat.mul_le_mul_right _ hi.2)
      _ = 2^(SemiprimeD1JetRecoveryScalarHeight.bitExponent a h u+q+inverseExponent a h u t.val+(a+1)*q) := by
        simp only [← pow_add,Nat.add_assoc]
      _ ≤ _ := Nat.pow_le_pow_right (by decide : 0<(2:ℕ)) (by unfold weightExponent;dsimp [q];omega)

/-- ACTUAL acquired weight normalization cannot exceed the original dyadic caps. -/
theorem original_weight_bits (a h u : ℕ) (t : Fin (size a))
    (hq : 0< nodeMultiplicity a h u t.val) (j : ℕ) (hj : j< nodeMultiplicity a h u t.val) :
    (coefficient (acquire a h u t.val).weights j).den≤2^weightExponent a h u t.val ∧
    (coefficient (acquire a h u t.val).weights j).num.natAbs≤2^weightExponent a h u t.val := by
  have hr := representation_reduced_bound (weightDenominator_pos a h u t.val)
    (weight_representation a h u t hq j hj)
  have hb := weight_bounds a h u t
  exact ⟨hr.1.trans hb.1,hr.2.trans hb.2⟩

/-- Every actual defined weight coefficient-sum prefix has the same logarithmic cap. -/
theorem original_weight_prefix_bits (a h u : ℕ) (t : Fin (size a))
    (hq : 0< nodeMultiplicity a h u t.val) (j len : ℕ) (hlen : len≤ nodeMultiplicity a h u t.val) :
    (weightPrefix a h u t.val j len).den≤2^weightExponent a h u t.val ∧
    (weightPrefix a h u t.val j len).num.natAbs≤2^weightExponent a h u t.val := by
  have hr := prefix_reduced_bounds a h u t hq j len hlen
  have hb := weight_bounds a h u t
  exact ⟨hr.1.trans hb.1,hr.2.trans hb.2⟩

/-- Fixed original a,M,2L polynomial envelope for EVERY scalar weight at any node. -/
def weightEnvelope (a M : ℕ) : ℕ :=
  4*(a+1)*size a*M+4*M+inverseEnvelope a M+4*(a+1)*M+1

/-- Original taper substitution yields a FIXED polynomial logarithmic envelope. -/
theorem original_weightExponent_le (a M u t : ℕ) (hM : u≤ M) :
    weightExponent a (height M u) u t≤ weightEnvelope a M := by
  have hq := nodeMultiplicity_le a M u t hM
  have hi := original_inverseExponent_le a M u t hM
  have hhu := height_mul_le M u hM
  have hE : SemiprimeD1JetRecoveryScalarHeight.bitExponent a (height M u) u≤4*(a+1)*size a*M := by
    unfold SemiprimeD1JetRecoveryScalarHeight.bitExponent
    nlinarith [Nat.mul_le_mul_left ((a+1)*size a) hhu]
  have hmul := Nat.mul_le_mul_left (a+1) hq
  unfold weightExponent weightEnvelope
  nlinarith

/-- ACTUAL finite common denominator of all acquired scalar weights on the original grid. -/
def globalDenominator (a M u : ℕ) : ℕ :=
  ∏t∈active a (height M u) u,∏j∈Finset.range (nodeMultiplicity a (height M u) u t),
    (coefficient (acquire a (height M u) u t).weights j).den

/-- The full original weight common denominator is positive, not an advised value. -/
theorem globalDenominator_pos (a M u : ℕ) : 0< globalDenominator a M u := by
  unfold globalDenominator
  apply Finset.prod_pos
  intro t _
  apply Finset.prod_pos
  intro j _
  exact Rat.den_pos _

/-- Even the product of ALL actual scalar weight denominators has polynomial
logarithmic height in original a,M,2L. -/
theorem globalDenominator_bound (a M u : ℕ) (hM : u≤ M) :
    globalDenominator a M u≤2^(weightEnvelope a M*(4*M)*size a) := by
  have hlocal (t : ℕ) (ht : t∈active a (height M u) u) :
      (∏j∈Finset.range (nodeMultiplicity a (height M u) u t),
        (coefficient (acquire a (height M u) u t).weights j).den)≤2^(weightEnvelope a M*(4*M)) := by
    have htn : t< size a := Finset.mem_range.mp (Finset.mem_filter.mp ht).1
    let tt : Fin (size a) := ⟨t,htn⟩
    have hq := active_positive a (height M u) u t ht
    have hbound : ∀j∈Finset.range (nodeMultiplicity a (height M u) u t),
        (coefficient (acquire a (height M u) u t).weights j).den≤2^weightEnvelope a M := by
      intro j hj
      exact (original_weight_bits a (height M u) u tt hq j (Finset.mem_range.mp hj)).1.trans
        (Nat.pow_le_pow_right (by decide : 0<(2:ℕ)) (original_weightExponent_le a M u t hM))
    have hp := Finset.prod_le_prod hbound
    simp only [Finset.prod_const,Finset.card_range] at hp
    apply hp.trans
    rw [← pow_mul]
    exact Nat.pow_le_pow_right (by decide : 0<(2:ℕ)) (Nat.mul_le_mul_left _ (nodeMultiplicity_le a M u t hM))
  have hp := Finset.prod_le_prod hlocal
  have hc : (active a (height M u) u).card≤ size a :=
    (Finset.card_filter_le _ _).trans (by simp)
  simp only [Finset.prod_const] at hp
  apply hp.trans
  rw [← pow_mul]
  exact Nat.pow_le_pow_right (by decide : 0<(2:ℕ)) (Nat.mul_le_mul_left _ hc)

/-- Pure polynomial in independent original dimensions; N is the acquired2L grid size. -/
def inversePolynomial (a M N : ℕ) : ℕ :=
  4*M*(4*M+4*(a+1)*N*M+4*(4*M+a+1)*N*M+3)

/-- Pure original-dimension polynomial for the local scalar weight logarithm. -/
def weightPolynomial (a M N : ℕ) : ℕ :=
  4*(a+1)*N*M+4*M+inversePolynomial a M N+4*(a+1)*M+1

/-- The actual envelope is the polynomial evaluated at the ACTUAL original grid size. -/
theorem weightEnvelope_eq (a M : ℕ) : weightEnvelope a M=weightPolynomial a M (size a) := rfl

/-- Pure finite arithmetic monotonicity, separate from semantic/runtime contexts. -/
theorem weightPolynomial_mono {a M N A B D : ℕ} (ha : a≤A) (hM : M≤B) (hN : N≤D) :
    weightPolynomial a M N≤weightPolynomial A B D := by
  unfold weightPolynomial inversePolynomial
  gcongr

/-- Literal fixed polynomial controlling the ALL-weight common-denominator bit length. -/
def polynomialEnvelope (S : ℕ) : ℕ := weightPolynomial S S S*(4*S)*S

/-- Explicit fixed monomial, not merely an assertion that the envelope is polynomial. -/
theorem polynomialEnvelope_bound (S : ℕ) : polynomialEnvelope S≤1000*(S+1)^6 := by
  unfold polynomialEnvelope weightPolynomial inversePolynomial
  nlinarith [Nat.zero_le (S^2),Nat.zero_le (S^3),Nat.zero_le (S^4),Nat.zero_le (S^5),Nat.zero_le (S^6)]

/-- Actual ORIGINAL denominator-product dyadic bound under only original dimension caps.
The cap on2L is essential; no exponential2^S width is substituted for an acquired dimension. -/
theorem original_globalDenominator_bits (a M u S : ℕ) (hM : u≤M)
    (ha : a≤S) (hm : M≤S) (hN : size a≤S) :
    globalDenominator a M u≤2^polynomialEnvelope S := by
  apply (globalDenominator_bound a M u hM).trans
  apply Nat.pow_le_pow_right (by decide : 0<(2:ℕ))
  rw [weightEnvelope_eq]
  unfold polynomialEnvelope
  exact Nat.mul_le_mul (Nat.mul_le_mul (weightPolynomial_mono ha hm hN)
    (Nat.mul_le_mul_left 4 hm)) hN

end RiemannGaussian.SemiprimeD1HermiteWeightBits
