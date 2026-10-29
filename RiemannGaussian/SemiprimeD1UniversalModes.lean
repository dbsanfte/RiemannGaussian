/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1CrossingPolynomial

/-! # Universal original D.12 modes over the modular polynomial ring
The nilpotent inverse is acquired by its explicit finite coefficient formula.
The congruence is polynomial in the local scalar, hence remains valid in every
algebra without assuming an extension-scalar valuation or inverse answer.
-/
set_option autoImplicit false
namespace RiemannGaussian.SemiprimeD1UniversalModes
open scoped BigOperators
open Polynomial SemiprimeD1WireKernel SemiprimeD1WireKernelFactors
  SemiprimeD1WireKernelEntry SemiprimeD1WireKernelOriginal SemiprimeD1WireKernelPaper
  SemiprimeD1CrossingCoefficient SemiprimeD1CrossingExpansion
  SemiprimeD1CrossingPolynomial SemiprimeD1OddAffineInverse

/-- Reduction of an acquired original integer numerator; no rational reduction is used. -/
noncomputable def reducedNumerator (p k center j d : ℕ) : (ZMod (2^p))[X] :=
  (numerator (SemiprimeD1WireKernelEntry.acquire k center j d)).map (Int.castRingHom _)

/-- Actual original normalized unit polynomial reduced modulo2^p. -/
noncomputable def unitPolynomial (p k j d : ℕ) : (ZMod (2^p))[X] :=
  (baseUnit k j d).map (Int.castRingHom _)

/-- Finite acquired inverse of the ORIGINAL stripped affine displacement. -/
noncomputable def unitInverse (p k j d : ℕ) : (ZMod (2^p))[X] :=
  SemiprimeD1OddAffineInverse.inverse p (normalizedFactor k j d).constant
    (normalizedFactor k j d).slope

/-- The acquired inverse works before any local scalar or extension is supplied. -/
theorem unit_inverse_correct (p k j d : ℕ) (hj : j<2^k) (hd : d<2^k) (hne : d≠j) :
    unitPolynomial p k j d*unitInverse p k j d=1 := by
  simpa only [unitPolynomial,baseUnit,linearPolynomial,Polynomial.map_add,Polynomial.map_mul,
    Polynomial.map_C,Polynomial.map_X,Int.coe_castRingHom,unitInverse] using
    inverse_correct p (normalizedFactor k j d).constant (normalizedFactor k j d).slope
      (normalized_constant_odd k j d hne) (normalized_slope_even k j d hj hd hne)

/-- Original common odd normalizer is a modular unit, with its actual acquired inverse. -/
noncomputable def normalizer (p k center : ℕ) : (ZMod (2^p))[X] :=
  C ((oddDenominator k center:ZMod (2^p))⁻¹)

/-- Universal b-th mode polynomial, acquired from the original factor/inverse data. -/
noncomputable def mode (p k center i j d b : ℕ) : (ZMod (2^p))[X] :=
  normalizer p k center*reducedNumerator p k center j d*
    (C (step k i j d:ZMod (2^p))*unitInverse p k j d)^b

/-- The original target numerator's unit identity survives reduction without
cancelling an even element in the modular ring. -/
theorem reduced_unit_identity (p k center i j d tile : ℕ) (hc : center<2^k)
    (hj : j<2^k) (hd : d<2^k) (he : d+2^(i+1)*tile<2^k)
    (hne : d≠j) (hv : padicValInt 2 (difference j d)≤ i) :
    reducedNumerator p k center j (d+2^(i+1)*tile)*
      (unitPolynomial p k j d-C (step k i j d*(tile:ℤ):ZMod (2^p)))=
    reducedNumerator p k center j d*unitPolynomial p k j d := by
  have h := congrArg (Polynomial.map (Int.castRingHom (ZMod (2^p))))
    (original_unit_identity k center i j d tile hc hj hd he hne hv)
  simpa only [Polynomial.map_mul,Polynomial.map_sub,Polynomial.map_C,
    Int.coe_castRingHom,Int.cast_mul,Int.cast_natCast,shiftedUnit,unitPolynomial,reducedNumerator] using h

/-- Actual target unit is a unit in the MODULAR POLYNOMIAL ring. -/
theorem target_polynomial_unit (p k i j d tile : ℕ) (hj : j<2^k)
    (hd : d<2^k) (hne : d≠j) (hv : padicValInt 2 (difference j d)≤ i) :
    IsUnit (unitPolynomial p k j d-C (step k i j d*(tile:ℤ):ZMod (2^p))) := by
  have h := affine_isUnit p ((normalizedFactor k j d).constant-step k i j d*(tile:ℤ))
    (normalizedFactor k j d).slope (shifted_constant_odd k i j d tile hne hv)
    (normalized_slope_even k j d hj hd hne)
  convert h using 1
  simp only [unitPolynomial,baseUnit,linearPolynomial,Polynomial.map_add,Polynomial.map_mul,
    Polynomial.map_C,Polynomial.map_X,Int.coe_castRingHom,Int.cast_sub,Int.cast_mul,Int.cast_natCast,C_sub]
  ring

/-- Actual reduced base numerator has exactly its ORIGINAL residual dyadic factor. -/
theorem reduced_numerator_factor (p k center j d : ℕ) :
    reducedNumerator p k center j d=
      C ((2:ZMod (2^p))^excess k j d)*
        (((SemiprimeD1WireKernelEntry.acquire k center j d).factors.map linearPolynomial).prod.map
          (Int.castRingHom (ZMod (2^p)))) := by
  simp only [reducedNumerator,numerator,Polynomial.map_mul,Polynomial.map_C,
    Int.coe_castRingHom,Int.cast_pow,Int.cast_ofNat,SemiprimeD1WireKernelEntry.acquire]

/-- An explicitly available p-th dyadic power is zero after modular reduction. -/
theorem dyadic_zero (p e : ℕ) (h : p≤ e) : (2:ZMod (2^p))^e=0 := by
  have hp : (2:ZMod (2^p))^p=0 := by
    simpa only [Nat.cast_pow,Nat.cast_ofNat] using ZMod.natCast_self (2^p)
  obtain ⟨l,rfl⟩ := Nat.exists_eq_add_of_le h
  rw [pow_add,hp,zero_mul]

/-- Even ratio powers together with the ORIGINAL base two-content kill the
finite tail at m=p-1. No extension-coordinate cancellation is assumed. -/
theorem base_tail_zero (p k center i j d tile : ℕ) (hj : j<2^k) (hd : d<2^k)
    (hi : i<k) (hne : d≠j) (hv : padicValInt 2 (difference j d)≤ i) (hp : 0<p) :
    reducedNumerator p k center j d*
      (C (step k i j d*(tile:ℤ):ZMod (2^p))*unitInverse p k j d)^(p-1)=0 := by
  have hbound := modePower_ge k i j d (p-1) hj hd hi hne hv
  have hz : (2:ZMod (2^p))^(excess k j d+(i+1-factorOrder k j d)*(p-1))=0 := by
    apply dyadic_zero
    unfold modePower at hbound
    rw [Nat.mul_comm (p-1)] at hbound
    omega
  rw [reduced_numerator_factor]
  simp only [step,Int.cast_pow,Int.cast_ofNat,Int.cast_natCast,mul_pow,C_mul,C_pow]
  have hmul : (C ((2:ZMod (2^p))^excess k j d): (ZMod (2^p))[X])*
      (C ((2:ZMod (2^p))^(i+1-factorOrder k j d)))^(p-1)=0 := by
    rw [← C_pow,← C_mul,← pow_mul,← pow_add,hz,C_0]
  calc
    _ = (C ((2:ZMod (2^p))^excess k j d)*
        (C ((2:ZMod (2^p))^(i+1-factorOrder k j d)))^(p-1))*
      (((SemiprimeD1WireKernelEntry.acquire k center j d).factors.map linearPolynomial).prod.map
          (Int.castRingHom (ZMod (2^p))))*
      C (tile:ZMod (2^p))^(p-1)*unitInverse p k j d^(p-1) := by simp only [C_pow];ring
    _ = 0 := by rw [hmul,zero_mul,zero_mul,zero_mul]

/-- COMPLETE finite universal D.12 in the polynomial ring. Every local scalar
in every ZMod(2^p)-algebra may be substituted afterward. -/
theorem universal_expansion (p k center i j d tile : ℕ) (hc : center<2^k)
    (hj : j<2^k) (hd : d<2^k) (he : d+2^(i+1)*tile<2^k)
    (hi : i<k) (hne : d≠j) (hv : padicValInt 2 (difference j d)≤ i) (hp : 0<p) :
    normalizer p k center*reducedNumerator p k center j (d+2^(i+1)*tile)=
      ∑ b∈Finset.range (p-1),mode p k center i j d b*C ((tile:ZMod (2^p))^b) := by
  let U := unitPolynomial p k j d
  let V : (ZMod (2^p))[X] := C (step k i j d*(tile:ℤ):ZMod (2^p))
  let R := V*unitInverse p k j d
  have hu : U*unitInverse p k j d=1 := unit_inverse_correct p k j d hj hd hne
  have hf : U-V=(1-R)*U := by
    dsimp [R]
    calc
      _ = U-V*(U*unitInverse p k j d) := by rw [hu,mul_one]
      _ = _ := by ring
  have hg := geom_sum_mul_neg R (p-1)
  have hsum : (∑ b∈Finset.range (p-1),R^b)*(U-V)=(1-R^(p-1))*U := by
    rw [hf,← mul_assoc,hg]
  have ht : reducedNumerator p k center j d*R^(p-1)=0 :=
    base_tail_zero p k center i j d tile hj hd hi hne hv hp
  have hn : reducedNumerator p k center j (d+2^(i+1)*tile)=
      reducedNumerator p k center j d*(∑ b∈Finset.range (p-1),R^b) := by
    apply (target_polynomial_unit p k i j d tile hj hd hne hv).mul_right_cancel
    change _*(U-V)=_*(U-V)
    rw [reduced_unit_identity p k center i j d tile hc hj hd he hne hv,mul_assoc,hsum]
    calc
      _ = (reducedNumerator p k center j d)*U-
        (reducedNumerator p k center j d*R^(p-1))*U := by rw [ht,zero_mul,sub_zero]
      _ = _ := by ring
  rw [hn,← mul_assoc,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro b _
  dsimp [R,V]
  simp only [mode,Int.cast_natCast,C_mul,C_pow,mul_pow]
  ring

/-- Exact acquired mode dyadic factorization before substituting any extension scalar. -/
theorem mode_content (p k center i j d b : ℕ) :
    mode p k center i j d b=
      C ((2:ZMod (2^p))^modePower k i j d b)*
        (normalizer p k center*
          (((SemiprimeD1WireKernelEntry.acquire k center j d).factors.map linearPolynomial).prod.map
            (Int.castRingHom (ZMod (2^p))))*unitInverse p k j d^b) := by
  rw [mode,reduced_numerator_factor]
  simp only [step,Int.cast_pow,Int.cast_ofNat,mul_pow,modePower,pow_add,C_mul,C_pow]
  rw [show b*(i+1-factorOrder k j d)=(i+1-factorOrder k j d)*b by exact Nat.mul_comm _ _,pow_mul]
  ring

/-- Universal mode coefficients carry the paper's weight b+1 in the polynomial
ring itself; evaluation in any algebra preserves this divisibility. -/
theorem mode_divisible (p k center i j d b : ℕ) (hj : j<2^k) (hd : d<2^k)
    (hi : i<k) (hne : d≠j) (hv : padicValInt 2 (difference j d)≤ i) :
    C ((2:ZMod (2^p))^(b+1)) ∣ mode p k center i j d b := by
  have hle := modePower_ge k i j d b hj hd hi hne hv
  rw [mode_content]
  refine dvd_mul_of_dvd_left ⟨C ((2:ZMod (2^p))^(modePower k i j d b-(b+1))),?_⟩ _
  rw [← C_mul,← pow_add]
  congr 2
  omega

/-- The complete universal identity may be evaluated in ANY modular algebra,
including unramified extensions; no integer-local-scalar restriction remains. -/
theorem evaluated_expansion {A : Type*} [CommRing A] (p k center i j d tile : ℕ)
    (f : ZMod (2^p) →+* A) (z : A) (hc : center<2^k)
    (hj : j<2^k) (hd : d<2^k) (he : d+2^(i+1)*tile<2^k)
    (hi : i<k) (hne : d≠j) (hv : padicValInt 2 (difference j d)≤ i) (hp : 0<p) :
    (normalizer p k center*reducedNumerator p k center j (d+2^(i+1)*tile)).eval₂ f z=
      ∑ b∈Finset.range (p-1),(mode p k center i j d b).eval₂ f z*
        f ((tile:ZMod (2^p))^b) := by
  have h := congrArg (Polynomial.eval₂ f z)
    (universal_expansion p k center i j d tile hc hj hd he hi hne hv hp)
  simpa only [Polynomial.eval₂_finsetSum,Polynomial.eval₂_mul,Polynomial.eval₂_C] using h

end RiemannGaussian.SemiprimeD1UniversalModes
