/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1OddAffineInverse

/-! # Original integer-polynomial displacement cancellation for crossing tiles
Cancellation takes place in the integer polynomial domain before reduction;
no cancellation of a nonunit in the modular polynomial ring is used.
-/
set_option autoImplicit false
namespace RiemannGaussian.SemiprimeD1CrossingPolynomial
open scoped BigOperators
open Polynomial SemiprimeD1WireKernel SemiprimeD1WireKernelFactors
  SemiprimeD1WireKernelEntry SemiprimeD1WireKernelOriginal SemiprimeD1WireKernelPaper
  SemiprimeD1CrossingCoefficient SemiprimeD1CrossingExpansion

/-- Original affine displacement polynomial before removing its two-content. -/
noncomputable def rawFactor (k j d : ℕ) : ℤ[X] :=
  C (difference j d)+C ((2:ℤ)^k)*X

/-- Concrete integer-polynomial base unit after removing exactly its two-content. -/
noncomputable def baseUnit (k j d : ℕ) : ℤ[X] := linearPolynomial (normalizedFactor k j d)

/-- Concrete target unit at the actual tile index. -/
noncomputable def shiftedUnit (k i j d tile : ℕ) : ℤ[X] :=
  baseUnit k j d-C (step k i j d*(tile:ℤ))

/-- Both omitted products reconstruct the SAME original complete grid polynomial. -/
theorem raw_products_equal (k j d e : ℕ) (hd : d<2^k) (he : e<2^k) :
    rawPolynomial k j d*rawFactor k j d=rawPolynomial k j e*rawFactor k j e := by
  unfold rawPolynomial rawFactor
  rw [Finset.prod_erase_mul _ _ (Finset.mem_range.mpr hd),
    Finset.prod_erase_mul _ _ (Finset.mem_range.mpr he)]

/-- Actual original acquired integer numerators inherit the exact full-grid identity. -/
theorem numerators_raw_equal (k center j d e : ℕ) (hc : center<2^k)
    (hj : j<2^k) (hd : d<2^k) (he : e<2^k) :
    numerator (SemiprimeD1WireKernelEntry.acquire k center j d)*rawFactor k j d=
      numerator (SemiprimeD1WireKernelEntry.acquire k center j e)*rawFactor k j e := by
  have hdn : (C (derivativeProduct (2^k) center):ℤ[X])≠0 := by
    simpa only [ne_eq,C_eq_zero] using derivativeProduct_ne_zero (2^k) center hc
  apply mul_left_cancel₀ hdn
  calc
    _ = (C (oddDenominator k center)*rawPolynomial k j d)*rawFactor k j d := by
      rw [cancellation k center j d hc hj hd];ring
    _ = C (oddDenominator k center)*(rawPolynomial k j e*rawFactor k j e) := by
      rw [mul_assoc,raw_products_equal k j d e hd he]
    _ = _ := by rw [← mul_assoc,cancellation k center j e hc hj he];ring

/-- The exact affine target is obtained by subtracting the positive tile step. -/
theorem rawFactor_shift (k i j d tile : ℕ) :
    rawFactor k j (d+2^(i+1)*tile)=rawFactor k j d-C ((2:ℤ)^(i+1)*(tile:ℤ)) := by
  unfold rawFactor difference
  simp only [Nat.cast_add,Nat.cast_mul,Nat.cast_pow,Nat.cast_ofNat,C_sub,C_add,C_mul]
  ring

/-- Actual original base displacement factors through the acquired unit polynomial. -/
theorem rawFactor_base (k j d : ℕ) (hj : j<2^k) (hd : d<2^k) :
    rawFactor k j d=C ((2:ℤ)^factorOrder k j d)*baseUnit k j d :=
  (linear_reconstruct k j d hj hd).symm

/-- Actual original target displacement has the SAME stripped power, with unit
constant changed by an even tile multiple. -/
theorem rawFactor_target (k i j d tile : ℕ) (hj : j<2^k) (hd : d<2^k)
    (hne : d≠j) (hv : padicValInt 2 (difference j d)≤ i) :
    rawFactor k j (d+2^(i+1)*tile)=C ((2:ℤ)^factorOrder k j d)*shiftedUnit k i j d tile := by
  have ho : factorOrder k j d≤ i := by simpa [factorOrder,hne] using hv
  have hp : (2:ℤ)^(i+1)=(2:ℤ)^factorOrder k j d*step k i j d := by
    rw [step,← pow_add];congr 1;omega
  rw [rawFactor_shift,rawFactor_base k j d hj hd,hp]
  simp only [shiftedUnit,C_mul]
  ring

/-- CRITICAL ORIGINAL POLYNOMIAL LICENSE: normalized target times its actual unit
is base numerator times base unit. All even cancellation was performed over ℤ[X]. -/
theorem original_unit_identity (k center i j d tile : ℕ) (hc : center<2^k)
    (hj : j<2^k) (hd : d<2^k) (he : d+2^(i+1)*tile<2^k)
    (hne : d≠j) (hv : padicValInt 2 (difference j d)≤ i) :
    numerator (SemiprimeD1WireKernelEntry.acquire k center j (d+2^(i+1)*tile))*
      shiftedUnit k i j d tile=
    numerator (SemiprimeD1WireKernelEntry.acquire k center j d)*baseUnit k j d := by
  have h := numerators_raw_equal k center j (d+2^(i+1)*tile) d hc hj he hd
  rw [rawFactor_target k i j d tile hj hd hne hv,rawFactor_base k j d hj hd] at h
  apply mul_left_cancel₀ (show (C ((2:ℤ)^factorOrder k j d):ℤ[X])≠0 by simp)
  convert h using 1 <;> ring

/-- Shifted unit constant is originally odd, independently of the scalar Z. -/
theorem shifted_constant_odd (k i j d tile : ℕ) (hne : d≠j)
    (hv : padicValInt 2 (difference j d)≤ i) :
    Odd ((normalizedFactor k j d).constant-step k i j d*(tile:ℤ)) := by
  have ho : factorOrder k j d≤ i := by simpa [factorOrder,hne] using hv
  have hs : Even (step k i j d) := even_iff_two_dvd.mpr (dvd_pow_self 2 (by omega))
  exact (normalized_constant_odd k j d hne).sub_even (hs.mul_right _)

end RiemannGaussian.SemiprimeD1CrossingPolynomial
