/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1CrossingExpansion

/-! # Original D.12 crossing targets and strict finite precision cutoff
The congruence is exhibited by an actual integer numerator divisible by 2^p and
an actual odd denominator. Local scalars here are integers, not extension tuples.
-/
set_option autoImplicit false
namespace RiemannGaussian.SemiprimeD1CrossingOriginal
open scoped BigOperators
open Polynomial SemiprimeD1WireKernel SemiprimeD1WireKernelFactors
  SemiprimeD1WireKernelEntry SemiprimeD1WireKernelOriginal SemiprimeD1WireKernelPaper
  SemiprimeD1CrossingCoefficient SemiprimeD1CrossingExpansion

/-- Original full affine scalar grid product, before C'(0) normalization. -/
def fullProduct (k j : ℕ) (z : ℤ) : ℤ :=
  ∏ q∈Finset.range (2^k),displacement k j q z

/-- Cancelled kernel times its omitted factor is the SAME full original product. -/
theorem kernel_times_displacement (k center j d : ℕ) (z : ℤ) (hd : d<2^k) :
    (rationalKernel k center j d).eval (z:ℚ)*(displacement k j d z:ℚ)=
      (fullProduct k j z:ℚ)/(derivativeProduct (2^k) center:ℚ) := by
  have hp := Finset.prod_erase_mul (Finset.range (2^k))
    (fun q => (displacement k j q z:ℚ)) (Finset.mem_range.mpr hd)
  simp only [rationalKernel,Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_map,
    rawPolynomial,Polynomial.eval₂_finsetProd,Polynomial.eval₂_add,Polynomial.eval₂_C,
    Polynomial.eval₂_mul,Polynomial.eval₂_X,Int.coe_castRingHom,Int.cast_pow,Int.cast_ofNat]
  have he : (∏ q∈(Finset.range (2^k)).erase d,
      ((difference j q:ℚ)+(2:ℚ)^k*(z:ℚ)))=
      ∏ q∈(Finset.range (2^k)).erase d,(displacement k j q z:ℚ) := by
    apply Finset.prod_congr rfl
    intro q _
    simp only [SemiprimeD1CrossingCoefficient.displacement,Int.cast_add,Int.cast_mul,Int.cast_pow,Int.cast_ofNat]
  rw [he]
  change (derivativeProduct (2^k) center:ℚ)⁻¹*_ * _ = _
  rw [mul_assoc, hp]
  simp only [fullProduct,Int.cast_prod]
  ring

/-- Original tile displacement factors through the actual acquired odd target unit. -/
theorem tile_displacement (k i j d tile : ℕ) (z : ℤ) (hj : j<2^k)
    (hd : d<2^k) (hne : d≠j) (hv : padicValInt 2 (difference j d)≤ i) :
    displacement k j (d+2^(i+1)*tile) z=
      (2:ℤ)^factorOrder k j d*targetUnit k i j d z tile := by
  have ho : factorOrder k j d≤ i := by simpa [factorOrder,hne] using hv
  have hr := displacement_reconstruct k j d z hj hd
  have hp : (2:ℤ)^(i+1)=(2:ℤ)^factorOrder k j d*step k i j d := by
    rw [step,← pow_add];congr 1;omega
  have he : displacement k j (d+2^(i+1)*tile) z=
      displacement k j d z-(2:ℤ)^(i+1)*(tile:ℤ) := by
    simp only [SemiprimeD1CrossingCoefficient.displacement,difference,Nat.cast_add,Nat.cast_mul,Nat.cast_pow,Nat.cast_ofNat]
    ring
  rw [he,hr,hp]
  unfold targetUnit
  ring

/-- The acquired target fraction is EXACTLY the original kernel at the tile column. -/
theorem target_original (k center i j d tile : ℕ) (z : ℤ) (hc : center<2^k)
    (hj : j<2^k) (hd : d<2^k) (htile : d+2^(i+1)*tile<2^k)
    (hne : d≠j) (hv : padicValInt 2 (difference j d)≤ i) :
    value (target k center i j d z tile)=
      (rationalKernel k center j (d+2^(i+1)*tile)).eval (z:ℚ) := by
  have hbase := kernel_times_displacement k center j d z hd
  have htarget := kernel_times_displacement k center j (d+2^(i+1)*tile) z htile
  have hu := targetUnit_odd k i j d z tile hj hd hne hv
  have hun : (targetUnit k i j d z tile:ℚ)≠0 := by
    exact_mod_cast (show targetUnit k i j d z tile≠0 by intro h;rw [h] at hu;simp at hu)
  have he := (acquired_integrality k center j d hc hj hd).2
  have heval := congrArg (Polynomial.eval (z:ℚ)) he
  simp only [Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_map] at heval
  have hp := omittedProduct_eval k center j d z
  have hcast : (numerator (SemiprimeD1WireKernelEntry.acquire k center j d)).eval₂
      (Int.castRingHom ℚ) (z:ℚ)=
      (2:ℚ)^excess k j d*(omittedProduct k j d z:ℚ) := by
    change Polynomial.eval₂ (Int.castRingHom ℚ) ((Int.castRingHom ℚ) z) _ = _
    rw [Polynomial.eval₂_at_apply,hp]
    simp only [Int.coe_castRingHom,Int.cast_mul,Int.cast_pow,Int.cast_ofNat]
  rw [hcast] at heval
  change (oddDenominator k center:ℚ)*_=_ at heval
  have hden : (oddDenominator k center:ℚ)≠0 := by exact_mod_cast denominator_ne_zero k center hc
  have hrec := displacement_reconstruct k j d z hj hd
  have htileRec := tile_displacement k i j d tile z hj hd hne hv
  have hrecQ : (displacement k j d z:ℚ)=
      (2:ℚ)^factorOrder k j d*(unitFactor k j d z:ℚ) := by exact_mod_cast hrec
  have htileQ : (displacement k j (d+2^(i+1)*tile) z:ℚ)=
      (2:ℚ)^factorOrder k j d*(targetUnit k i j d z tile:ℚ) := by exact_mod_cast htileRec
  rw [hrecQ] at hbase
  rw [htileQ] at htarget
  have hsame : (rationalKernel k center j (d+2^(i+1)*tile)).eval (z:ℚ)*
      (targetUnit k i j d z tile:ℚ)=
      (rationalKernel k center j d).eval (z:ℚ)*(unitFactor k j d z:ℚ) := by
    apply mul_left_cancel₀ (pow_ne_zero (factorOrder k j d) (by norm_num : (2:ℚ)≠0))
    nlinarith [hbase,htarget]
  unfold value target
  simp only [Int.cast_mul,Int.cast_pow,Int.cast_ofNat]
  apply (div_eq_iff (mul_ne_zero hden hun)).mpr
  calc
    _ = ((oddDenominator k center:ℚ)*(rationalKernel k center j d).eval (z:ℚ))*
        (unitFactor k j d z:ℚ) := by rw [heval]
    _ = (oddDenominator k center:ℚ)*((rationalKernel k center j d).eval (z:ℚ)*
        (unitFactor k j d z:ℚ)) := by ring
    _ = _ := by rw [← hsame];ring

/-- Strict finite cutoff: keep exactly b+1<p and exhibit the divisible odd fraction tail. -/
theorem original_strict_cutoff (k center i j d tile p : ℕ) (z : ℤ)
    (hc : center<2^k) (hj : j<2^k) (hd : d<2^k) (htile : d+2^(i+1)*tile<2^k)
    (hi : i<k) (hne : d≠j) (hv : padicValInt 2 (difference j d)≤ i) (hp : 0<p) :
    Odd (remainder k center i j d (p-1) z tile).denominator ∧
      (2:ℤ)^p ∣ (remainder k center i j d (p-1) z tile).numerator ∧
      (rationalKernel k center j (d+2^(i+1)*tile)).eval (z:ℚ)-
        (∑ b∈Finset.range (p-1),
          value (SemiprimeD1CrossingCoefficient.acquire k center i j d b z)*(tile:ℚ)^b)=
        value (remainder k center i j d (p-1) z tile) := by
  have ho := (target_remainder_odd k center i j d (p-1) z tile hc hj hd hne hv).2
  have hdv := remainder_divisible k center i j d (p-1) z tile hj hd hi hne hv
  have he := expansion k center i j d (p-1) z tile hc hj hd hne hv
  rw [target_original k center i j d tile z hc hj hd htile hne hv] at he
  refine ⟨ho,?_,?_⟩
  · simpa only [Nat.sub_add_cancel hp] using hdv
  · exact sub_eq_iff_eq_add.mpr (by simpa only [add_comm,Int.cast_natCast] using he)

/-- The finite range is exactly the paper's strict weight cutoff, not b<p. -/
theorem strict_cutoff_iff (b p : ℕ) : b∈Finset.range (p-1) ↔ b+1<p := by
  simp only [Finset.mem_range]
  omega

end RiemannGaussian.SemiprimeD1CrossingOriginal
