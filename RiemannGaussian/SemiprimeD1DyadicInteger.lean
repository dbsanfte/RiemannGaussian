/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1RecoveryResidue

/-! # The legitimate odd-denominator reduction ring homomorphism
Reduction is defined ONLY on the subring of2-adically integral rationals. It is
not a ring homomorphism from all rationals into a characteristic2-power ring.
This semantic bridge has no attached execution-cost claim.
-/
set_option autoImplicit false
namespace RiemannGaussian.SemiprimeD1DyadicInteger
open scoped BigOperators
open SemiprimeD1WireKernelOriginal SemiprimeD1DyadicBounds SemiprimeD1RecoveryResidue
  SemiprimeD1CrossingCoefficient SemiprimeD1CrossingResidue SemiprimeD1CrossingModulo

/-- The actual rational subring with odd canonical denominators. -/
def integers : Subring ℚ where
  carrier := AtLeast 0
  zero_mem' := zero 0
  one_mem' := one
  add_mem' := fun ha hb => add ha hb
  neg_mem' := fun ha => neg ha
  mul_mem' := by
    intro a b ha hb
    change AtLeast 0 (a*b)
    exact mul ha hb

/-- Native product fraction used only to prove consistency of unit inversion. -/
def fractionMul (a b : Coefficient) : Coefficient :=
  ⟨a.numerator*b.numerator,a.denominator*b.denominator⟩

/-- Literal fraction multiplication has its original rational value. -/
theorem fractionMul_value (a b : Coefficient) :
    value (fractionMul a b)=value a*value b := by
  simp only [value,fractionMul,Int.cast_mul]
  ring

/-- Multiplication of actual odd-denominator fractions commutes with native reduction. -/
theorem fractionMul_residue (p : ℕ) (a b : Coefficient)
    (ha : Odd a.denominator) (hb : Odd b.denominator) :
    residue p (fractionMul a b)=residue p a*residue p b := by
  apply (odd_unit _ (ha.mul hb) p).mul_left_cancel
  change ((fractionMul a b).denominator:ZMod (2^p))*_= _
  rw [residue_denominator p (fractionMul a b) (ha.mul hb)]
  simp only [fractionMul,Int.cast_mul]
  calc
    _ = ((a.denominator:ZMod (2^p))*residue p a)*
        ((b.denominator:ZMod (2^p))*residue p b) := by
          rw [residue_denominator p a ha,residue_denominator p b hb]
    _ = _ := by ring

/-- Restricted native reduction preserves addition; integrality derives every oddness fact. -/
theorem reduce_add (p : ℕ) (a b : ℚ) (ha : AtLeast 0 a) (hb : AtLeast 0 b) :
    reduce p (a+b)=reduce p a+reduce p b := by
  have hao : Odd (canonicalFraction a).denominator := by
    change Odd ((a.den:ℕ):ℤ)
    exact_mod_cast denominator_odd a ha
  have hbo : Odd (canonicalFraction b).denominator := by
    change Odd ((b.den:ℕ):ℤ)
    exact_mod_cast denominator_odd b hb
  have hsum : Odd (canonicalFraction (a+b)).denominator := by
    change Odd (((a+b).den:ℕ):ℤ)
    exact_mod_cast denominator_odd (a+b) (add ha hb)
  have he := residue_eq_of_value_eq p (canonicalFraction (a+b))
    (fractionAdd (canonicalFraction a) (canonicalFraction b)) hsum (hao.mul hbo)
    (by rw [canonicalFraction_value,fractionAdd_value _ _ hao hbo,canonicalFraction_value,canonicalFraction_value])
  exact he.trans (fractionAdd_residue p _ _ hao hbo)

/-- Restricted native reduction preserves multiplication with no illegal Q-to-ZMod map. -/
theorem reduce_mul (p : ℕ) (a b : ℚ) (ha : AtLeast 0 a) (hb : AtLeast 0 b) :
    reduce p (a*b)=reduce p a*reduce p b := by
  have hao : Odd (canonicalFraction a).denominator := by
    change Odd ((a.den:ℕ):ℤ)
    exact_mod_cast denominator_odd a ha
  have hbo : Odd (canonicalFraction b).denominator := by
    change Odd ((b.den:ℕ):ℤ)
    exact_mod_cast denominator_odd b hb
  have hi : AtLeast 0 (a*b) := by simpa only [add_zero] using mul ha hb
  have hprod : Odd (canonicalFraction (a*b)).denominator := by
    change Odd (((a*b).den:ℕ):ℤ)
    exact_mod_cast denominator_odd (a*b) hi
  have he := residue_eq_of_value_eq p (canonicalFraction (a*b))
    (fractionMul (canonicalFraction a) (canonicalFraction b)) hprod (hao.mul hbo)
    (by rw [canonicalFraction_value,fractionMul_value,canonicalFraction_value,canonicalFraction_value])
  exact he.trans (fractionMul_residue p _ _ hao hbo)

/-- The legitimate original odd-localization map into the finite dyadic ring. -/
def reduction (p : ℕ) : integers →+* ZMod (2^p) where
  toFun q := reduce p q.val
  map_zero' := by simpa using reduce_integer p 0
  map_one' := by simpa using reduce_integer p 1
  map_add' a b := reduce_add p a.val b.val a.property b.property
  map_mul' a b := reduce_mul p a.val b.val a.property b.property

/-- Integer constants have their usual modular values under the restricted map. -/
theorem reduction_integer (p : ℕ) (z : ℤ) : reduction p (z:integers)=(z:ZMod (2^p)) := by
  change reduce p (z:ℚ)=_
  exact reduce_integer p z

/-- The restricted map commutes with finite contractions, including zero divisors
in the target ring. Every source factor is genuinely in the integral subring. -/
theorem reduction_contraction {X E : Type*} (xs : Finset X) (es : Finset E)
    (p : ℕ) (T : X → E → integers) :
    reduction p (∑x∈xs,∏e∈es,T x e)=∑x∈xs,∏e∈es,reduction p (T x e) := by
  simp only [map_sum,map_prod]

end RiemannGaussian.SemiprimeD1DyadicInteger
