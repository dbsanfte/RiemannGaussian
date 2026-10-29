/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1CrossingOriginal

/-! # Acquired odd-fraction residues and crossing truncation
Only actual integer numerators and odd denominators are interpreted modulo 2^p.
There is no nonexistent ring map from all of the rationals into ZMod(2^p).
-/
set_option autoImplicit false
namespace RiemannGaussian.SemiprimeD1CrossingResidue
open scoped BigOperators
open Polynomial SemiprimeD1WireKernel SemiprimeD1WireKernelFactors
  SemiprimeD1WireKernelEntry SemiprimeD1WireKernelOriginal SemiprimeD1WireKernelPaper
  SemiprimeD1CrossingCoefficient SemiprimeD1CrossingExpansion SemiprimeD1CrossingOriginal

/-- Actual modular evaluation of an acquired integer fraction, using extended gcd. -/
def residue (p : ℕ) (c : Coefficient) : ZMod (2^p) :=
  (c.numerator:ZMod (2^p))*(c.denominator:ZMod (2^p))⁻¹

/-- The acquired odd inverse obeys the defining exact unit law. -/
theorem residue_denominator (p : ℕ) (c : Coefficient) (hc : Odd c.denominator) :
    (c.denominator:ZMod (2^p))*residue p c=(c.numerator:ZMod (2^p)) := by
  have hi := ZMod.mul_inv_of_unit (c.denominator:ZMod (2^p)) (odd_unit _ hc p)
  unfold residue
  calc
    _ = (c.numerator:ZMod (2^p))*((c.denominator:ZMod (2^p))*
      (c.denominator:ZMod (2^p))⁻¹) := by ring
    _ = _ := by rw [hi,mul_one]

/-- A derived divisible numerator vanishes under the ACTUAL odd-unit evaluator. -/
theorem residue_zero (p : ℕ) (c : Coefficient) (hc : (2:ℤ)^p ∣ c.numerator) :
    residue p c=0 := by
  obtain ⟨u,hu⟩ := hc
  unfold residue
  rw [hu]
  simp only [Int.cast_mul,Int.cast_pow,Int.cast_ofNat]
  have h : (2:ZMod (2^p))^p=0 := by
    have hcast : ((2^p:ℕ):ZMod (2^p))=0 := ZMod.natCast_self (2^p)
    simpa only [Nat.cast_pow,Nat.cast_ofNat] using hcast
  rw [h,zero_mul,zero_mul]

/-- Equal odd fractions have identical residues; this is not a rational ring map. -/
theorem residue_eq_of_value_eq (p : ℕ) (a b : Coefficient)
    (ha : Odd a.denominator) (hb : Odd b.denominator) (he : value a=value b) :
    residue p a=residue p b := by
  have han : a.denominator≠0 := by intro h;rw [h] at ha;simp at ha
  have hbn : b.denominator≠0 := by intro h;rw [h] at hb;simp at hb
  have haq : (a.denominator:ℚ)≠0 := by exact_mod_cast han
  have hbq : (b.denominator:ℚ)≠0 := by exact_mod_cast hbn
  have hi : a.numerator*b.denominator=b.numerator*a.denominator := by
    have hq : (a.numerator:ℚ)*(b.denominator:ℚ)=(b.numerator:ℚ)*(a.denominator:ℚ) :=
      (div_eq_div_iff haq hbq).mp he
    exact_mod_cast hq
  have hz : (a.numerator:ZMod (2^p))*(b.denominator:ZMod (2^p))=
      (b.numerator:ZMod (2^p))*(a.denominator:ZMod (2^p)) := by
    simpa only [Int.cast_mul] using congrArg (fun x:ℤ => (x:ZMod (2^p))) hi
  apply ((odd_unit a.denominator ha p).mul (odd_unit b.denominator hb p)).mul_left_cancel
  calc
    _ = (b.denominator:ZMod (2^p))*((a.denominator:ZMod (2^p))*residue p a) := by ring
    _ = (b.denominator:ZMod (2^p))*(a.numerator:ZMod (2^p)) := by rw [residue_denominator p a ha]
    _ = (a.denominator:ZMod (2^p))*(b.numerator:ZMod (2^p)) := by rw [mul_comm,hz,mul_comm]
    _ = _ := by rw [← residue_denominator p b hb];ring

/-- Exact remainder denominator is odd and its actual modulo-2^p value is zero. -/
theorem strict_remainder_zero (k center i j d tile p : ℕ) (z : ℤ)
    (hc : center<2^k) (hj : j<2^k) (hd : d<2^k)
    (hi : i<k) (hne : d≠j) (hv : padicValInt 2 (difference j d)≤ i) (hp : 0<p) :
    Odd (remainder k center i j d (p-1) z tile).denominator ∧
      residue p (remainder k center i j d (p-1) z tile)=0 := by
  refine ⟨(target_remainder_odd k center i j d (p-1) z tile hc hj hd hne hv).2,?_⟩
  apply residue_zero
  simpa only [Nat.sub_add_cancel hp] using
    remainder_divisible k center i j d (p-1) z tile hj hd hi hne hv

/-- Fraction representation of an original acquired polynomial entry at an integer scalar. -/
noncomputable def entryFraction (k center j d : ℕ) (z : ℤ) : Coefficient :=
  ⟨(numerator (SemiprimeD1WireKernelEntry.acquire k center j d)).eval z,oddDenominator k center⟩

/-- Original source equality licenses the concrete scalar modular entry evaluator. -/
theorem entryFraction_value (k center j d : ℕ) (z : ℤ) (hc : center<2^k)
    (hj : j<2^k) (hd : d<2^k) :
    value (entryFraction k center j d z)=(rationalKernel k center j d).eval (z:ℚ) := by
  have he := congrArg (Polynomial.eval (z:ℚ)) (acquired_integrality k center j d hc hj hd).2
  simp only [Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_map] at he
  have hcast : (numerator (SemiprimeD1WireKernelEntry.acquire k center j d)).eval₂
      (Int.castRingHom ℚ) (z:ℚ)=
      (((numerator (SemiprimeD1WireKernelEntry.acquire k center j d)).eval z:ℤ):ℚ) := by
    change Polynomial.eval₂ (Int.castRingHom ℚ) ((Int.castRingHom ℚ) z) _ = _
    exact Polynomial.eval₂_at_apply _ _
  rw [hcast] at he
  change (oddDenominator k center:ℚ)*_=_ at he
  unfold value entryFraction
  apply (div_eq_iff (by exact_mod_cast denominator_ne_zero k center hc)).mpr
  simpa only [mul_comm] using he.symm

/-- Derived original target residue equals the actual unexpanded wire entry evaluator. -/
theorem target_residue_original (k center i j d tile p : ℕ) (z : ℤ)
    (hc : center<2^k) (hj : j<2^k) (hd : d<2^k) (htile : d+2^(i+1)*tile<2^k)
    (hne : d≠j) (hv : padicValInt 2 (difference j d)≤ i) :
    residue p (target k center i j d z tile)=
      evaluate p (SemiprimeD1WireKernelEntry.acquire k center j (d+2^(i+1)*tile)) (z:ZMod (2^p)) := by
  have h := residue_eq_of_value_eq p (target k center i j d z tile)
    (entryFraction k center j (d+2^(i+1)*tile) z)
    (target_remainder_odd k center i j d 0 z tile hc hj hd hne hv).1
    (denominator_odd k center hc)
    ((target_original k center i j d tile z hc hj hd htile hne hv).trans
      (entryFraction_value k center j (d+2^(i+1)*tile) z hc hj htile).symm)
  rw [h]
  unfold residue entryFraction
  rw [show (((numerator (SemiprimeD1WireKernelEntry.acquire k center j (d+2^(i+1)*tile))).eval z:ℤ):ZMod (2^p))=
      (numerator (SemiprimeD1WireKernelEntry.acquire k center j (d+2^(i+1)*tile))).eval₂
        (Int.castRingHom (ZMod (2^p))) (z:ZMod (2^p)) by
          exact (Polynomial.eval₂_at_apply (Int.castRingHom (ZMod (2^p))) z).symm]
  rw [numerator_mod_eval]
  unfold evaluate
  simp only [SemiprimeD1WireKernelEntry.acquire]
  ring

end RiemannGaussian.SemiprimeD1CrossingResidue
