/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1DyadicBounds

/-! # Integrality of the ACTUAL original local denominator and cached inverse
All bounds come from original grid differences and the executed coefficient
recurrences. No desired inverse, integrality or intermediate-fit premise is used.
-/
set_option autoImplicit false
namespace RiemannGaussian.SemiprimeD1InverseIntegral
open scoped BigOperators
open Polynomial SemiprimeD1DyadicBounds SemiprimeD1WireKernelFactors
  SemiprimeD1WireKernelOriginal SemiprimeD1JetRecoveryGrid SemiprimeD1JetRecoveryWeights
  SemiprimeJetArray SemiprimeJetRecurrence SemiprimeHermiteArrayHeight

/-- Every stored/default coefficient of a concrete rational array is integral. -/
def IntegralArray (a : Array ℚ) : Prop := ∀i,AtLeast 0 (coefficient a i)

/-- The actual constant1 coefficient array has integral default coefficients too. -/
theorem unitArray_integral : IntegralArray #[1] := by
  intro i
  by_cases hi : i=0
  · subst i
    simpa [coefficient] using one
  · rw [coefficient_zero (by simp only [Array.size_singleton];omega)]
    exact zero 0

/-- Literal affine coefficient arrays inherit their actual scalar integrality. -/
theorem affineArray_integral (c : ℚ) (hc : AtLeast 0 c) : IntegralArray (affineArray c) := by
  intro i
  cases i with
  | zero => simpa [coefficient,affineArray] using one
  | succ i =>
    cases i with
    | zero => simpa [coefficient,affineArray] using hc
    | succ i =>
      rw [coefficient_zero (by simp [affineArray])]
      exact zero 0

/-- Every executed truncated convolution coefficient is integral, including zeros
outside the stored output width. -/
theorem multiply_integral (a b : Array ℚ) (J : ℕ) (ha : IntegralArray a) (hb : IntegralArray b) :
    IntegralArray (multiply a b J).coefficients := by
  intro i
  by_cases hi : i<J
  · rw [multiply_coefficient a b J i hi]
    apply SemiprimeD1DyadicBounds.sum
    intro j _
    simpa only [add_zero] using mul (ha j) (hb (i-j))
  · rw [coefficient_zero (by rw [multiply_size];omega)]
    exact zero 0

/-- The original affine builder preserves integrality at every actual recursive suffix. -/
theorem buildAffine_integral (J : ℕ) (cs : List ℚ) (hc : ∀c∈cs,AtLeast 0 c) :
    IntegralArray (buildAffine J cs).coefficients := by
  induction cs with
  | nil => exact unitArray_integral
  | cons c cs ih =>
    exact multiply_integral _ _ J (ih (fun x hx => hc x (List.mem_cons_of_mem _ hx)))
      (affineArray_integral c (hc c (by simp)))

/-- Exact recurrence integrality is derived from its ACTUAL constant1 and input coefficients. -/
theorem inverseCoeff_integral (a : ℕ→ℚ) (ha : ∀i,AtLeast 0 (a i)) (h0 : a 0=1) (n : ℕ) :
    AtLeast 0 (inverseCoeff a n) := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    cases n with
    | zero => simpa only [inverseCoeff,h0,inv_one] using one
    | succ n =>
      rw [inverseCoeff,h0,inv_one,neg_one_mul]
      apply neg
      apply SemiprimeD1DyadicBounds.sum
      intro i hi
      simpa only [add_zero] using mul (ha (i+1)) (ih (n-i) (by omega))

/-- Actual cached inverse arrays are integral from the original input recurrence,
not an inverse coefficient/height oracle. -/
theorem inverse_integral (a : Array ℚ) (J : ℕ) (ha : IntegralArray a) (h0 : coefficient a 0=1) :
    IntegralArray (SemiprimeJetArray.inverse a J).coefficients := by
  intro i
  by_cases hi : i<J
  · rw [inverse_coefficient a J i hi]
    exact inverseCoeff_integral _ ha h0 i
  · rw [coefficient_zero (by rw [inverse_size];omega)]
    exact zero 0

/-- Each ACTUAL original-grid slope has one dyadic factor before taking inverse jets. -/
theorem original_slope (a h u : ℕ) (t : Fin (size a)) (c : ℚ)
    (hc : c∈slopes a h u t.val) : AtLeast 1 c := by
  obtain ⟨q,hqr,hc⟩ := List.mem_flatMap.mp hc
  have hq : q<2^(a+1) := List.mem_range.mp hqr
  by_cases hex : q=SemiprimeD1WireKernelOriginal.center a ∨ q=t.val
  · simp only [hex,ite_true,List.not_mem_nil] at hc
  · simp only [hex,ite_false,List.mem_replicate] at hc
    obtain ⟨_,rfl⟩ := hc
    have hqt : q≠t.val := fun he => hex (Or.inr he)
    have hd : (point a t.val:ℚ)-(point a q:ℚ)≠0 := by
      exact_mod_cast point_sub_ne_zero a t.val q hqt
    have hα : (((2:ℤ)^(a+1)):ℚ)≠0 := by positivity
    have hv := difference_order_lt (a+1) t.val q t.isLt hq hqt
    have he : point a t.val-point a q=difference t.val q := by unfold point difference;ring
    apply Or.inr
    rw [padicValRat.div hα hd]
    have hn : padicValRat 2 ((((2:ℤ)^(a+1)):ℚ))=(a+1:ℤ) := by
      have htwo : padicValRat 2 (2:ℚ)=1 := padicValRat.self (p:=2) (by decide)
      simp only [Int.cast_ofNat,padicValRat.pow,htwo,mul_one,Nat.cast_add,Nat.cast_one]

    have hden : (point a t.val:ℚ)-(point a q:ℚ)=((point a t.val-point a q:ℤ):ℚ) := by push_cast;rfl
    rw [hn,hden,SemiprimeD1JetRecoveryGrid.int_valuation,he]
    omega

/-- Integrality of the ACTUAL acquired local denominator is derived from original grid data. -/
theorem acquire_denominator_integral (a h u : ℕ) (t : Fin (size a)) :
    IntegralArray (acquire a h u t.val).denominator.coefficients := by
  apply buildAffine_integral
  intro c hc
  exact mono (original_slope a h u t c hc) (by omega)

/-- Integrality of every ACTUAL acquired inverse coefficient, with no output-fit advice. -/
theorem acquire_inverse_integral (a h u : ℕ) (t : Fin (size a))
    (hq : 0<nodeMultiplicity a h u t.val) :
    IntegralArray (acquire a h u t.val).inverse.coefficients :=
  inverse_integral _ _ (acquire_denominator_integral a h u t)
    (acquire_denominator_constant a h u t.val hq)

end RiemannGaussian.SemiprimeD1InverseIntegral
