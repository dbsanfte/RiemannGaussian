/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1DyadicInteger
import RiemannGaussian.SemiprimeD1UniversalModeData

/-! # Explicit integral local wire polynomial and its modular commuting square
The witness is constructed from the ACTUAL normalized integer factors and odd
normalizer. No coefficient selection, desired entry, or Q-to-ZMod map occurs.
Polynomials are semantic witnesses; this module asserts no new execution clock.
-/
set_option autoImplicit false
namespace RiemannGaussian.SemiprimeD1IntegralLocalKernel
open scoped BigOperators
open Polynomial SemiprimeD1DyadicInteger SemiprimeD1DyadicBounds
  SemiprimeD1WireKernelFactors SemiprimeD1WireKernelEntry SemiprimeD1WireKernelOriginal
  SemiprimeD1WireKernelPaper SemiprimeD1UniversalModeData

/-- Original odd integer inverses genuinely belong to the integral rational subring. -/
theorem odd_inverse_integral (d : ℤ) (hd : Odd d) : AtLeast 0 (d:ℚ)⁻¹ := by
  have hn : ¬(2:ℤ)∣d := by simpa only [← even_iff_two_dvd] using Int.not_even_iff_odd.mpr hd
  right
  rw [padicValRat.inv,padicValRat.of_int,padicValInt.eq_zero_of_not_dvd hn]
  norm_num

/-- Explicit original odd-denominator inverse inside the legitimate subring. -/
def oddInverse (d : ℤ) (hd : Odd d) : integers := ⟨(d:ℚ)⁻¹,odd_inverse_integral d hd⟩

/-- This is an actual inverse of the original integer in the restricted source ring. -/
theorem oddInverse_mul (d : ℤ) (hd : Odd d) : oddInverse d hd*(d:integers)=1 := by
  apply Subtype.ext
  have hn : d≠0 := by intro h;rw [h] at hd;simp at hd
  change (d:ℚ)⁻¹*(d:ℚ)=1
  exact inv_mul_cancel₀ (by exact_mod_cast hn)

/-- Restricted reduction sends the acquired odd inverse to its unique modular inverse. -/
theorem reduction_oddInverse (p : ℕ) (d : ℤ) (hd : Odd d) :
    reduction p (oddInverse d hd)=((d:ZMod (2^p))⁻¹) := by
  have hu := odd_unit d hd p
  apply hu.mul_left_cancel
  have h := congrArg (reduction p) (oddInverse_mul d hd)
  simp only [map_mul,map_one,reduction_integer] at h
  rw [mul_comm] at h
  rw [h,ZMod.mul_inv_of_unit _ hu]

/-- Literal integer linear factors, embedded without changing acquired order or data. -/
noncomputable def integralLinear (f : Linear) : Polynomial integers :=
  C (f.constant:integers)+C (f.slope:integers)*X

/-- The ACTUAL finite-factor polynomial witness over integral rationals. -/
noncomputable def entryPolynomial (e : Entry) (hd : Odd e.denominator) : Polynomial integers :=
  C (oddInverse e.denominator hd)*(numerator e).map (Int.castRingHom integers)

/-- Inclusion into Q interprets exactly the original normalized finite factor product. -/
theorem entry_inclusion (e : Entry) (hd : Odd e.denominator) :
    (entryPolynomial e hd).map integers.subtype=
      C ((e.denominator:ℚ)⁻¹)*(numerator e).map (Int.castRingHom ℚ) := by
  have hc : integers.subtype.comp (Int.castRingHom integers)=Int.castRingHom ℚ :=
    Subsingleton.elim _ _
  simp only [entryPolynomial,Polynomial.map_mul,Polynomial.map_C,Polynomial.map_map,hc]
  rfl

/-- Coefficient reduction of every acquired factor has its literal modular interpretation. -/
theorem entry_reduction (p : ℕ) (e : Entry) (hd : Odd e.denominator) :
    (entryPolynomial e hd).map (reduction p)=
      C ((e.denominator:ZMod (2^p))⁻¹)*(numerator e).map (Int.castRingHom (ZMod (2^p))) := by
  have hc : (reduction p).comp (Int.castRingHom integers)=Int.castRingHom (ZMod (2^p)) :=
    Subsingleton.elim _ _
  simp only [entryPolynomial,Polynomial.map_mul,Polynomial.map_C,Polynomial.map_map,hc,reduction_oddInverse]

/-- The commuting square holds at ANY scalar of ANY modular algebra, including nilpotents. -/
theorem entry_evaluate {A : Type*} [CommRing A] (p : ℕ) (f : ZMod (2^p) →+* A)
    (z : A) (e : Entry) (hd : Odd e.denominator) :
    ((entryPolynomial e hd).map (reduction p)).eval₂ f z=entryValue p f z e := by
  rw [entry_reduction]
  simp only [numerator,Polynomial.map_mul,Polynomial.map_C,Polynomial.map_list_prod,
    List.map_map,Function.comp_def,linearPolynomial,Polynomial.map_add,Polynomial.map_X,
    Int.coe_castRingHom,Polynomial.eval₂_mul,Polynomial.eval₂_C,Polynomial.eval₂_list_prod,
    Polynomial.eval₂_add,Polynomial.eval₂_X,entryValue,Polynomial.map_pow,
    Polynomial.eval₂_pow,map_pow]
  rw [mul_assoc]
  norm_num

/-- Concrete original local witness, built from the actual a,t,x,y constructor. -/
noncomputable def originalPolynomial (a : ℕ) (t : Fin (size a)) (x y : Fin (2^a)) : Polynomial integers :=
  entryPolynomial (SemiprimeD1WireKernelOriginal.acquireOriginal a t x y)
    (original_kernel_integral a t x y).1

/-- The explicit integral witness includes to the ORIGINAL D.7 polynomial at t+alphaZ. -/
theorem original_inclusion (a : ℕ) (t : Fin (size a)) (x y : Fin (2^a)) :
    (originalPolynomial a t x y).map integers.subtype=
      (kernel a (displacement a x y).val).comp (affine a t.val) := by
  rw [originalPolynomial,entry_inclusion,← (original_kernel_integral a t x y).2]
  rw [← mul_assoc,← C_mul]
  have hn : ((SemiprimeD1WireKernelOriginal.acquireOriginal a t x y).denominator:ℚ)≠0 := by
    exact_mod_cast denominator_ne_zero (a+1) (center a) (center_lt a)
  rw [inv_mul_cancel₀ hn,C_1,one_mul]

/-- Every original local rational coefficient is integral, with the explicit witness retained. -/
theorem original_coefficient_integral (a : ℕ) (t : Fin (size a)) (x y : Fin (2^a)) (j : ℕ) :
    AtLeast 0 (((kernel a (displacement a x y).val).comp (affine a t.val)).coeff j) := by
  rw [← original_inclusion,Polynomial.coeff_map]
  exact ((originalPolynomial a t x y).coeff j).property

/-- Original coefficientwise restricted reduction gives the actual acquired entry
in every ZMod algebra, without an integral-coefficient or requested-entry premise. -/
theorem original_evaluate {A : Type*} [CommRing A] (p a : ℕ)
    (f : ZMod (2^p) →+* A) (z : A) (t : Fin (size a)) (x y : Fin (2^a)) :
    ((originalPolynomial a t x y).map (reduction p)).eval₂ f z=
      entryValue p f z (SemiprimeD1WireKernelOriginal.acquireOriginal a t x y) :=
  entry_evaluate p f z _ _

end RiemannGaussian.SemiprimeD1IntegralLocalKernel
