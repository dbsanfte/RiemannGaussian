/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1JetRecoveryGrid

/-! # Original Hermite scalar numerator/denominator acquisition and dyadic height
The rational E_t(0) is reconstructed from acquired integer products, with a
polynomial logarithmic height bound in the original finite-grid dimensions.
This is not the missing tapered valuation regrouping or a whole bit clock.
-/
set_option autoImplicit false
namespace RiemannGaussian.SemiprimeD1JetRecoveryScalarHeight
open scoped BigOperators
open SemiprimeD1WireKernelFactors SemiprimeD1WireKernelOriginal
  SemiprimeD1TaperedLoss SemiprimeD1JetRecoveryGrid

/-- Total ORIGINAL retained Hermite multiplicity in the scalar product at node t. -/
def totalMultiplicity (a h u t : ℕ) : ℕ := ∑ q∈others a t,nodeMultiplicity a h u q

/-- Actual integer numerator product, including every original sign and multiplicity. -/
def numerator (a h u t : ℕ) : ℤ := ∏ q∈others a t,(-point a q)^nodeMultiplicity a h u q

/-- Actual nonzero integer node-difference denominator product. -/
def denominator (a h u t : ℕ) : ℤ :=
  ∏ q∈others a t,(point a t-point a q)^nodeMultiplicity a h u q

/-- Actual original E_t(0) equals the acquired integer ratio, not a supplied scalar. -/
theorem ratio_spec (a h u t : ℕ) : Ezero a h u t=
    (numerator a h u t:ℚ)/(denominator a h u t:ℚ) := by
  simp only [Ezero,numerator,denominator,Int.cast_prod,Int.cast_pow,Int.cast_neg,
    Int.cast_sub,div_pow,Finset.prod_div_distrib]

/-- Every acquired denominator factor is nonzero, also for inactive multiplicities. -/
theorem denominator_ne_zero (a h u t : ℕ) : denominator a h u t≠0 := by
  apply Finset.prod_ne_zero_iff.mpr
  intro q hq
  exact pow_ne_zero _ (point_sub_ne_zero a t q (Finset.mem_erase.mp hq).1)

/-- The number of actual scalar-factor repetitions is bounded by original grid size. -/
theorem totalMultiplicity_le (a h u t : ℕ) : totalMultiplicity a h u t≤ size a*h*u := by
  have hp : ∀ q∈others a t,nodeMultiplicity a h u q≤h*u := by
    intro q _
    exact Nat.mul_le_mul_left h (Nat.sub_le _ _)
  have hs := Finset.sum_le_sum hp
  have hc : (others a t).card≤ size a := by
    have hsub : others a t⊆Finset.range (size a) := by
      intro q hq
      exact (Finset.mem_erase.mp (Finset.mem_erase.mp hq).2).2
    simpa only [Finset.card_range] using Finset.card_le_card hsub
  change totalMultiplicity a h u t≤_ at hs
  simp only [Finset.sum_const,smul_eq_mul] at hs
  exact hs.trans (by nlinarith [Nat.mul_le_mul_right (h*u) hc])

private theorem power_product_bound (s : Finset ℕ) (f : ℕ→ℤ) (m : ℕ→ℕ)
    (N : ℕ) (hf : ∀q∈s,(f q).natAbs≤N) :
    (∏q∈s,(f q)^m q).natAbs≤N^(∑q∈s,m q) := by
  change Int.natAbsHom _≤_
  rw [map_prod Int.natAbsHom]
  simp only [Int.natAbsHom_apply,Int.natAbs_pow]
  rw [← Finset.prod_pow_eq_pow_sum]
  apply Finset.prod_le_prod
  intro q hq
  exact Nat.pow_le_pow_left (hf q hq) _

/-- Original grid point magnitudes are below its actual 2L size. -/
theorem point_abs_lt (a q : ℕ) (hq : q<size a) : (point a q).natAbs<size a := by
  exact difference_abs_lt (size a) q (center a) hq (center_lt a)

/-- Both acquired integer scalar products have logarithmic height at most
(a+1)*totalMultiplicity, without a desired rational-height premise. -/
theorem numerator_denominator_bound (a h u : ℕ) (t : Fin (size a)) :
    (numerator a h u t.val).natAbs≤(size a)^totalMultiplicity a h u t.val ∧
    (denominator a h u t.val).natAbs≤(size a)^totalMultiplicity a h u t.val := by
  constructor
  · apply power_product_bound
    intro q hq
    have hqr : q<size a := Finset.mem_range.mp
      (Finset.mem_erase.mp (Finset.mem_erase.mp hq).2).2
    simpa only [Int.natAbs_neg] using (point_abs_lt a q hqr).le
  · apply power_product_bound
    intro q hq
    have hqr : q<size a := Finset.mem_range.mp
      (Finset.mem_erase.mp (Finset.mem_erase.mp hq).2).2
    have he : point a t.val-point a q=difference t.val q := by unfold point difference;ring
    rw [he]
    exact (difference_abs_lt (size a) t.val q t.isLt hqr).le

/-- Coarse original-dimension dyadic exponent; no magnitude is used as a bit bound. -/
def bitExponent (a h u : ℕ) : ℕ := (a+1)*size a*h*u

/-- Every acquired E_t(0) integer numerator/denominator fits the explicit dyadic cap. -/
theorem original_dyadic_height (a h u : ℕ) (t : Fin (size a)) :
    (numerator a h u t.val).natAbs≤2^bitExponent a h u ∧
    (denominator a h u t.val).natAbs≤2^bitExponent a h u := by
  have hb := numerator_denominator_bound a h u t
  have hm := totalMultiplicity_le a h u t.val
  have he : (size a)^totalMultiplicity a h u t.val≤2^bitExponent a h u := by
    change (2^(a+1))^totalMultiplicity a h u t.val≤_
    rw [← pow_mul]
    apply Nat.pow_le_pow_right (by decide : 0<(2:ℕ))
    unfold bitExponent
    nlinarith [Nat.mul_le_mul_left (a+1) hm]
  exact ⟨hb.1.trans he,hb.2.trans he⟩

end RiemannGaussian.SemiprimeD1JetRecoveryScalarHeight
