/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1CrossingCoefficient
import Mathlib.Algebra.Ring.GeomSum

/-! # Finite positive crossing expansions with an acquired divisible remainder
All scalar numerators and odd denominators are constructed from the original
integer grid. No infinite series or desired-integrality premise is used.
-/
set_option autoImplicit false
namespace RiemannGaussian.SemiprimeD1CrossingExpansion
open scoped BigOperators
open Polynomial SemiprimeD1WireKernel SemiprimeD1WireKernelFactors
  SemiprimeD1WireKernelEntry SemiprimeD1WireKernelOriginal SemiprimeD1WireKernelPaper
  SemiprimeD1CrossingCoefficient

/-- Stripped tile step; this is a positive power of two for a crossing. -/
def step (k i j d : ℕ) : ℤ := (2:ℤ)^(i+1-factorOrder k j d)

/-- Actual denominator unit at the displaced tile column. -/
def targetUnit (k i j d : ℕ) (z tile : ℤ) : ℤ :=
  unitFactor k j d z-step k i j d*tile

/-- The shifted denominator remains odd: only an even multiple was subtracted. -/
theorem targetUnit_odd (k i j d : ℕ) (z tile : ℤ) (hj : j<2^k)
    (hd : d<2^k) (hne : d≠j) (hv : padicValInt 2 (difference j d)≤ i) :
    Odd (targetUnit k i j d z tile) := by
  have ho : factorOrder k j d≤ i := by simpa [factorOrder,hne] using hv
  have hs : Even (step k i j d) := by
    apply even_iff_two_dvd.mpr
    exact dvd_pow_self 2 (by omega)
  exact (unitFactor_odd k j d z hj hd hne).sub_even (hs.mul_right tile)

/-- Full target fraction after cancelling the exact common two-content. -/
def target (k center i j d : ℕ) (z tile : ℤ) : Coefficient :=
  ⟨(2:ℤ)^excess k j d*omittedProduct k j d z*unitFactor k j d z,
    oddDenominator k center*targetUnit k i j d z tile⟩

/-- Explicit finite geometric remainder, entirely integer acquired data. -/
def remainder (k center i j d m : ℕ) (z tile : ℤ) : Coefficient :=
  ⟨(2:ℤ)^modePower k i j d m*omittedProduct k j d z*tile^m*unitFactor k j d z,
    oddDenominator k center*(unitFactor k j d z)^m*targetUnit k i j d z tile⟩

/-- Both finite target and remainder invert only genuinely odd original units. -/
theorem target_remainder_odd (k center i j d m : ℕ) (z tile : ℤ)
    (hc : center<2^k) (hj : j<2^k) (hd : d<2^k) (hne : d≠j)
    (hv : padicValInt 2 (difference j d)≤ i) :
    Odd (target k center i j d z tile).denominator ∧
      Odd (remainder k center i j d m z tile).denominator := by
  have hu := unitFactor_odd k j d z hj hd hne
  have ht := targetUnit_odd k i j d z tile hj hd hne hv
  exact ⟨(denominator_odd k center hc).mul ht,
    ((denominator_odd k center hc).mul hu.pow).mul ht⟩

/-- The true finite remainder has at least m+1 powers of two. -/
theorem remainder_divisible (k center i j d m : ℕ) (z tile : ℤ)
    (hj : j<2^k) (hd : d<2^k) (hi : i<k) (hne : d≠j)
    (hv : padicValInt 2 (difference j d)≤ i) :
    (2:ℤ)^(m+1) ∣ (remainder k center i j d m z tile).numerator := by
  exact dvd_mul_of_dvd_left (dvd_mul_of_dvd_left
    (dvd_mul_of_dvd_left (pow_dvd_pow 2 (modePower_ge k i j d m hj hd hi hne hv)) _) _) _

/-- A positive geometric expansion with an exact finite remainder over any field. -/
theorem finite_geometric {K : Type*} [Field K] (A U V : K) (hU : U≠0)
    (hV : U-V≠0) (m : ℕ) :
    A*U/(U-V)=A*(∑ b∈Finset.range m,(V/U)^b)+A*(V/U)^m*U/(U-V) := by
  have hg := geom_sum_mul_neg (V/U) m
  have hratio : 1-V/U=(U-V)/U := by field_simp
  rw [hratio] at hg
  have he : (∑ b∈Finset.range m,(V/U)^b)*(U-V)=(1-(V/U)^m)*U := by
    have ht := congrArg (fun x:K => x*U) hg
    simpa only [div_mul_cancel₀ _ hU,mul_assoc] using ht
  apply (div_eq_iff hV).2
  field_simp [hV]
  linear_combination -A*he

/-- Every acquired mode is the base fraction times a POSITIVE geometric power. -/
theorem mode_value (k center i j d b : ℕ) (z tile : ℤ) :
    value (SemiprimeD1CrossingCoefficient.acquire k center i j d b z)*(tile:ℚ)^b=
      ((2:ℚ)^excess k j d*(omittedProduct k j d z:ℚ)/(oddDenominator k center:ℚ))*
        (((step k i j d:ℤ):ℚ)*(tile:ℚ)/(unitFactor k j d z:ℚ))^b := by
  unfold value SemiprimeD1CrossingCoefficient.acquire modePower step
  simp only [Int.cast_mul,Int.cast_pow,Int.cast_ofNat,pow_add,div_pow,mul_pow]
  rw [show b*(i+1-factorOrder k j d)=(i+1-factorOrder k j d)*b by exact Nat.mul_comm _ _,pow_mul]
  ring

/-- Exact D.12 scalar finite expansion, including an explicit original-derived remainder. -/
theorem expansion (k center i j d m : ℕ) (z tile : ℤ)
    (hc : center<2^k) (hj : j<2^k) (hd : d<2^k) (hne : d≠j)
    (hv : padicValInt 2 (difference j d)≤ i) :
    value (target k center i j d z tile)=
      (∑ b∈Finset.range m,value (SemiprimeD1CrossingCoefficient.acquire k center i j d b z)*(tile:ℚ)^b)+
      value (remainder k center i j d m z tile) := by
  have hu := unitFactor_odd k j d z hj hd hne
  have ht := targetUnit_odd k i j d z tile hj hd hne hv
  have hun : (unitFactor k j d z:ℚ)≠0 := by
    exact_mod_cast (show unitFactor k j d z≠0 by intro h;rw [h] at hu;simp at hu)
  have htn : (unitFactor k j d z:ℚ)-(step k i j d:ℚ)*(tile:ℚ)≠0 := by
    have h : targetUnit k i j d z tile≠0 := by intro h;rw [h] at ht;simp at ht
    exact_mod_cast h
  have hdn : (oddDenominator k center:ℚ)≠0 := by exact_mod_cast denominator_ne_zero k center hc
  have hg := finite_geometric
    ((2:ℚ)^excess k j d*(omittedProduct k j d z:ℚ)/(oddDenominator k center:ℚ))
    (unitFactor k j d z:ℚ) ((step k i j d:ℚ)*(tile:ℚ)) hun htn m
  simp_rw [mode_value]
  rw [← Finset.mul_sum]
  convert hg using 1
  · simp only [value,target,Int.cast_mul,Int.cast_pow,Int.cast_ofNat,targetUnit,Int.cast_sub]
    field_simp [hdn,htn]
  · congr 1
    simp only [value,remainder,modePower,Int.cast_mul,Int.cast_pow,Int.cast_ofNat,
      targetUnit,Int.cast_sub,step,pow_add,div_pow,mul_pow]
    rw [show m*(i+1-factorOrder k j d)=(i+1-factorOrder k j d)*m by exact Nat.mul_comm _ _,pow_mul]
    field_simp [hdn,hun,htn]

end RiemannGaussian.SemiprimeD1CrossingExpansion
