/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1WireKernelPaper

/-! # Actual scalar crossing-mode coefficients of D.12
The integer scalar substitution is explicit. All powers of two are cancelled
before taking an odd-denominator fraction. The extension-coordinate and physical
bit implementations are separate obligations.
-/
set_option autoImplicit false
namespace RiemannGaussian.SemiprimeD1CrossingCoefficient
open scoped BigOperators
open Polynomial SemiprimeD1WireKernel SemiprimeD1WireKernelFactors
  SemiprimeD1WireKernelEntry SemiprimeD1WireKernelOriginal SemiprimeD1WireKernelPaper

/-- Actual normalized denominator factor at the supplied integer local scalar. -/
def unitFactor (k j d : ℕ) (z : ℤ) : ℤ :=
  (normalizedFactor k j d).constant+(normalizedFactor k j d).slope*z

/-- Original scalar denominator, before stripping powers of two. -/
def displacement (k j d : ℕ) (z : ℤ) : ℤ := difference j d+(2:ℤ)^k*z

/-- Exact acquired factor reconstruction at the actual scalar. -/
theorem displacement_reconstruct (k j d : ℕ) (z : ℤ)
    (hj : j<2^k) (hd : d<2^k) :
    displacement k j d z=(2:ℤ)^factorOrder k j d*unitFactor k j d z := by
  have hc := normalized_constant k j d
  have hs := normalized_slope k j d hj hd
  unfold displacement unitFactor
  rw [← hc,← hs]
  ring

/-- Maximal content makes the actual normalized nonzero constant odd. -/
theorem normalized_constant_odd (k j d : ℕ) (hne : d≠j) :
    Odd (normalizedFactor k j d).constant := by
  apply Int.not_even_iff_odd.mp
  rw [even_iff_two_dvd]
  intro h
  obtain ⟨u,hu⟩ := h
  have hd : (2:ℤ)^(padicValInt 2 (difference j d)+1) ∣ difference j d := by
    refine ⟨u,?_⟩
    have hr := normalized_constant k j d
    rw [show factorOrder k j d=padicValInt 2 (difference j d) by simp [factorOrder,hne],hu] at hr
    calc
      difference j d = 2*u*2^padicValInt 2 (difference j d) := hr.symm
      _ = 2^(padicValInt 2 (difference j d)+1)*u := by rw [pow_succ];ring
  rcases (padicValInt_dvd_iff (p:=2) _ _).mp hd with hz|hv
  · exact difference_ne_zero j d hne hz
  · omega

/-- The scalar correction is even after stripping the actual crossing order. -/
theorem normalized_slope_even (k j d : ℕ) (hj : j<2^k)
    (hd : d<2^k) (hne : d≠j) : Even (normalizedFactor k j d).slope := by
  have hl := difference_order_lt k j d hj hd hne
  have he : factorOrder k j d+(k-factorOrder k j d)=k := by simp [factorOrder,hne];omega
  have hs : (normalizedFactor k j d).slope=(2:ℤ)^(k-factorOrder k j d) := by
    apply mul_right_cancel₀ (pow_ne_zero _ (by decide : (2:ℤ)≠0))
    rw [normalized_slope k j d hj hd,← pow_add]
    congr 1
    omega
  rw [hs]
  exact even_iff_two_dvd.mpr (dvd_pow_self 2 (by simp only [factorOrder,hne,ite_false];omega))

/-- Adding alpha*z cannot destroy oddness of the stripped crossing denominator. -/
theorem unitFactor_odd (k j d : ℕ) (z : ℤ) (hj : j<2^k)
    (hd : d<2^k) (hne : d≠j) : Odd (unitFactor k j d z) := by
  exact (normalized_constant_odd k j d hne).add_even
    ((normalized_slope_even k j d hj hd hne).mul_right z)

/-- The exact integer product of the original omitted-factor normalized data. -/
def omittedProduct (k j d : ℕ) (z : ℤ) : ℤ :=
  ((indices k d).map (fun q => unitFactor k j q z)).prod

/-- Explicit exponent of the b-th crossing mode, with no valuation oracle. -/
def modePower (k i j d b : ℕ) : ℕ :=
  excess k j d+b*(i+1-factorOrder k j d)

/-- Actual integer numerator and odd denominator acquired from original inputs. -/
structure Coefficient where
  /-- Numerator includes every cancelled power of two. -/
  numerator : ℤ
  /-- Only original odd units are multiplied into this denominator. -/
  denominator : ℤ

/-- Acquire mode b without a rational coefficient or inverse answer input. -/
def acquire (k center i j d b : ℕ) (z : ℤ) : Coefficient :=
  ⟨(2:ℤ)^modePower k i j d b*omittedProduct k j d z,
   oddDenominator k center*(unitFactor k j d z)^b⟩

/-- Exact crossing order bounds imply the claimed weight b+1 divisibility. -/
theorem modePower_ge (k i j d b : ℕ) (hj : j<2^k) (hd : d<2^k)
    (hi : i<k) (hne : d≠j) (hv : padicValInt 2 (difference j d)≤ i) :
    b+1≤ modePower k i j d b := by
  have hx := excess_add_order k j d hj hd
  have ho : factorOrder k j d≤ i := by simpa [factorOrder,hne] using hv
  have hstep : 1≤ i+1-factorOrder k j d := by omega
  have hex : 1≤ excess k j d := by omega
  have hb := Nat.mul_le_mul_left b hstep
  unfold modePower
  omega

/-- Original-input acquired mode coefficients have odd denominators. -/
theorem acquire_odd (k center i j d b : ℕ) (z : ℤ) (hc : center<2^k)
    (hj : j<2^k) (hd : d<2^k) (hne : d≠j) :
    Odd (acquire k center i j d b z).denominator := by
  exact (denominator_odd k center hc).mul (unitFactor_odd k j d z hj hd hne).pow

/-- The actual acquired numerator is divisible by the mode weight, not an assumed bound. -/
theorem acquire_divisible (k center i j d b : ℕ) (z : ℤ)
    (hj : j<2^k) (hd : d<2^k) (hi : i<k) (hne : d≠j)
    (hv : padicValInt 2 (difference j d)≤ i) :
    (2:ℤ)^(b+1) ∣ (acquire k center i j d b z).numerator := by
  exact dvd_mul_of_dvd_left (pow_dvd_pow 2 (modePower_ge k i j d b hj hd hi hne hv)) _

/-- Scalar rational interpretation is proof-side; acquisition uses only integers. -/
def value (c : Coefficient) : ℚ := (c.numerator:ℚ)/(c.denominator:ℚ)

/-- Integer product interpretation agrees exactly with evaluation of acquired factors. -/
theorem omittedProduct_eval (k center j d : ℕ) (z : ℤ) :
    (numerator (SemiprimeD1WireKernelEntry.acquire k center j d)).eval z=
      (2:ℤ)^excess k j d*omittedProduct k j d z := by
  simp [numerator,SemiprimeD1WireKernelEntry.acquire,linearPolynomial,
    Polynomial.eval_list_prod,List.map_map,Function.comp_def,omittedProduct,unitFactor]

/-- D.12 coefficient identity with the positive geometric ratio, for original kernel data. -/
theorem acquire_value (k center i j d b : ℕ) (z : ℤ) (hc : center<2^k)
    (hj : j<2^k) (hd : d<2^k) (hne : d≠j)
    (hv : padicValInt 2 (difference j d)≤ i) :
    value (acquire k center i j d b z)=
      (rationalKernel k center j d).eval (z:ℚ)*
        (((2:ℚ)^(i+1))/(displacement k j d z:ℚ))^b := by
  have ho : factorOrder k j d≤ i := by simpa [factorOrder,hne] using hv
  have hu := unitFactor_odd k j d z hj hd hne
  have hun : unitFactor k j d z≠0 := by intro h;rw [h] at hu;simp at hu
  have hden := denominator_ne_zero k center hc
  have he := (acquired_integrality k center j d hc hj hd).2
  have heval := congrArg (Polynomial.eval (z:ℚ)) he
  simp only [Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_map,
] at heval
  have hn := omittedProduct_eval k center j d z
  have hcast : (numerator (SemiprimeD1WireKernelEntry.acquire k center j d)).eval₂
      (Int.castRingHom ℚ) (z:ℚ)=
      (2:ℚ)^excess k j d*(omittedProduct k j d z:ℚ) := by
    change Polynomial.eval₂ (Int.castRingHom ℚ) ((Int.castRingHom ℚ) z) _ = _
    rw [Polynomial.eval₂_at_apply,hn]
    simp only [Int.coe_castRingHom,Int.cast_mul,Int.cast_pow,Int.cast_ofNat]
  rw [hcast] at heval
  change (oddDenominator k center:ℚ)*_=_ at heval
  have hdrec := displacement_reconstruct k j d z hj hd
  have hpow : (2:ℚ)^(i+1)=(2:ℚ)^factorOrder k j d*
      (2:ℚ)^(i+1-factorOrder k j d) := by rw [← pow_add];congr 1;omega
  have hdc : (displacement k j d z:ℚ)=
      (2:ℚ)^factorOrder k j d*(unitFactor k j d z:ℚ) := by exact_mod_cast hdrec
  have hdn : (oddDenominator k center:ℚ)≠0 := by exact_mod_cast hden
  have hunq : (unitFactor k j d z:ℚ)≠0 := by exact_mod_cast hun
  have h2 : (2:ℚ)^factorOrder k j d≠0 := pow_ne_zero _ (by norm_num)
  have hk : (rationalKernel k center j d).eval (z:ℚ)=
      (2:ℚ)^excess k j d*(omittedProduct k j d z:ℚ)/(oddDenominator k center:ℚ) := by
    apply (eq_div_iff hdn).mpr
    simpa only [mul_comm] using heval
  have hr : (2:ℚ)^(i+1)/(displacement k j d z:ℚ)=
      (2:ℚ)^(i+1-factorOrder k j d)/(unitFactor k j d z:ℚ) := by
    rw [hpow,hdc]
    exact mul_div_mul_left _ _ h2
  rw [hr,hk]
  unfold value acquire modePower
  simp only [Int.cast_mul,Int.cast_pow,Int.cast_ofNat,pow_add,div_pow]
  rw [show b*(i+1-factorOrder k j d)=(i+1-factorOrder k j d)*b by exact Nat.mul_comm _ _,pow_mul]
  field_simp

end RiemannGaussian.SemiprimeD1CrossingCoefficient
