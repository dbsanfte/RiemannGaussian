/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1WireKernelEntry

/-! # Original a,t,x,y kernel and acquired odd-unit modular evaluation
Runtime acquires integer factors from the actual complete grid. Rational and
polynomial objects specify those acquired data only. Modular inverse uses the
actual extended-gcd implementation of ZMod.inv, not a supplied inverse answer.
-/
set_option autoImplicit false
namespace RiemannGaussian.SemiprimeD1WireKernelOriginal
open scoped BigOperators
open Polynomial SemiprimeD1WireKernel SemiprimeD1WireKernelFactors SemiprimeD1WireKernelEntry

/-- Exact rational polynomial D.7 after original local substitution. -/
noncomputable def rationalKernel (k center j d : ℕ) : ℚ[X] :=
  C ((derivativeProduct (2^k) center:ℚ)⁻¹)*
    (rawPolynomial k j d).map (Int.castRingHom ℚ)

/-- Constructive coefficientwise integrality: the witness is the ACTUAL acquired
integer factor product, and its clearing denominator is genuinely odd. -/
theorem acquired_integrality (k center j d : ℕ)
    (hc : center<2^k) (hj : j<2^k) (hd : d<2^k) :
    Odd (acquire k center j d).denominator ∧
    C ((acquire k center j d).denominator:ℚ)*rationalKernel k center j d=
      (numerator (acquire k center j d)).map (Int.castRingHom ℚ) := by
  refine ⟨denominator_odd k center hc,?_⟩
  have h := congrArg (Polynomial.map (Int.castRingHom ℚ)) (cancellation k center j d hc hj hd)
  simp only [Polynomial.map_mul,Polynomial.map_C,Int.coe_castRingHom] at h
  have hn : (derivativeProduct (2^k) center:ℚ)≠0 := by
    exact_mod_cast derivativeProduct_ne_zero (2^k) center hc
  change C (oddDenominator k center:ℚ)*rationalKernel k center j d=_
  calc
    _=C ((derivativeProduct (2^k) center:ℚ)⁻¹)*
        (C (oddDenominator k center:ℚ)*(rawPolynomial k j d).map (Int.castRingHom ℚ)) := by
      unfold rationalKernel
      ring
    _=C ((derivativeProduct (2^k) center:ℚ)⁻¹)*
        (C (derivativeProduct (2^k) center:ℚ)*
          (numerator (acquire k center j d)).map (Int.castRingHom ℚ)) := by rw [h]
    _=_ := by rw [← mul_assoc,← C_mul,inv_mul_cancel₀ hn,C_1,one_mul]

/-- The nonlocal original entry has an additional integral factor two. -/
theorem nonlocal_even_numerator (k center j d : ℕ)
    (hj : j<2^k) (hd : d<2^k) (hne : d≠j) :
    C (2:ℤ) ∣ numerator (acquire k center j d) := by
  have he := excess_positive k j d hj hd hne
  have hp : excess k j d=(excess k j d-1)+1 := by omega
  refine ⟨C ((2:ℤ)^(excess k j d-1))*
    (((acquire k center j d).factors.map linearPolynomial).prod),?_⟩
  unfold numerator
  change C ((2:ℤ)^excess k j d)*_= _
  have hh : (2:ℤ)^excess k j d=2*(2:ℤ)^(excess k j d-1) := by
    conv_lhs => rw [hp,pow_succ]
    ring
  rw [hh,C_mul]
  ring

/-- Every coefficient has an explicitly acquired odd-denominator rational witness. -/
theorem coefficient_odd_denominator (k center j d i : ℕ)
    (hc : center<2^k) (hj : j<2^k) (hd : d<2^k) :
    (rationalKernel k center j d).coeff i=
      ((numerator (acquire k center j d)).coeff i:ℚ)/(acquire k center j d).denominator ∧
      Odd (acquire k center j d).denominator := by
  have h := acquired_integrality k center j d hc hj hd
  have he := congrArg (fun p : ℚ[X] => p.coeff i) h.2
  simp only [coeff_C_mul,coeff_map,Int.coe_castRingHom] at he
  have hn : ((acquire k center j d).denominator:ℚ)≠0 := by
    exact_mod_cast denominator_ne_zero k center hc
  refine ⟨?_,h.1⟩
  apply (eq_div_iff hn).mpr
  simpa only [mul_comm] using he

/-- Original complete grid cardinality 2L. -/
def size (a : ℕ) : ℕ := 2^(a+1)
/-- Original grid centre index, whose translated point is zero. -/
def center (a : ℕ) : ℕ := 2^a
/-- Original point q-L as an actual integer. -/
def point (a q : ℕ) : ℤ := (q:ℤ)-(center a:ℤ)

/-- Original centre belongs to the acquired grid. -/
theorem center_lt (a : ℕ) : center a<size a := by
  unfold center size
  have hp : 0<2^a := by positivity
  rw [pow_succ]
  omega

/-- Original cancelled displacement y-x represented as its actual grid index. -/
def displacement (a : ℕ) (x y : Fin (2^a)) : Fin (size a) :=
  ⟨2^a+y.val-x.val,by
    have hx := x.isLt
    have hy := y.isLt
    have hp : 0<2^a := by positivity
    unfold size
    rw [pow_succ]
    omega⟩

/-- The acquired index cancels precisely the original D.7 displacement factor. -/
theorem displacement_point (a : ℕ) (x y : Fin (2^a)) :
    point a (displacement a x y).val=(y.val:ℤ)-(x.val:ℤ) := by
  have hx := x.isLt
  unfold point center displacement
  dsimp only
  omega

/-- ORIGINAL data constructor from a,t,x,y, with no requested entry/coefficients. -/
def acquireOriginal (a : ℕ) (t : Fin (size a)) (x y : Fin (2^a)) : Entry :=
  acquire (a+1) (center a) t.val (displacement a x y).val

/-- The original constructor's odd unit is derived for every actual grid point. -/
theorem original_integrality (a : ℕ) (t : Fin (size a)) (x y : Fin (2^a)) :
    Odd (acquireOriginal a t x y).denominator ∧
    C ((acquireOriginal a t x y).denominator:ℚ)*
        rationalKernel (a+1) (center a) t.val (displacement a x y).val=
      (numerator (acquireOriginal a t x y)).map (Int.castRingHom ℚ) :=
  acquired_integrality (a+1) (center a) t.val (displacement a x y).val
    (center_lt a) t.isLt (displacement a x y).isLt

/-- A known odd integer is an actual unit modulo every 2^P, including negative signs. -/
theorem odd_unit (z : ℤ) (hz : Odd z) (P : ℕ) : IsUnit (z : ZMod (2^P)) := by
  have hn : ¬2 ∣ z.natAbs := by
    intro h
    have hd : (2:ℤ) ∣ z := by exact_mod_cast (Int.natCast_dvd.mpr h : ((2:ℕ):ℤ) ∣ z)
    exact (Int.not_even_iff_odd.mpr hz) (even_iff_two_dvd.mpr hd)
  have hc : z.natAbs.Coprime (2^P) :=
    ((Nat.prime_two.coprime_iff_not_dvd.mpr hn).symm).pow_right P
  have hu := (ZMod.isUnit_iff_coprime z.natAbs (2^P)).mpr hc
  cases z with
  | ofNat n => simpa only [Int.ofNat_eq_natCast,Int.natAbs_natCast,Int.cast_natCast] using hu
  | negSucc n => simpa only [Int.natAbs_negSucc,Int.cast_negSucc] using hu.neg

/-- Execute the unexpanded acquired factors and actual odd inverse modulo 2^P.
ZMod.inv uses extended gcd. No native rational entry is encoded by this routine. -/
def evaluate (P : ℕ) (entry : Entry) (z : ZMod (2^P)) : ZMod (2^P) :=
  (entry.denominator:ZMod (2^P))⁻¹*(2:ZMod (2^P))^entry.power*
    (entry.factors.map (fun f => (f.constant:ZMod (2^P))+(f.slope:ZMod (2^P))*z)).prod

/-- Original evaluation inverts only an acquired original odd unit. -/
theorem original_inverse_unit (a P : ℕ) (t : Fin (size a)) (x y : Fin (2^a)) :
    IsUnit ((acquireOriginal a t x y).denominator:ZMod (2^P)) :=
  odd_unit _ (original_integrality a t x y).1 P

/-- The inverse used by the actual original evaluator satisfies the unit law. -/
theorem original_inverse_correct (a P : ℕ) (t : Fin (size a)) (x y : Fin (2^a)) :
    ((acquireOriginal a t x y).denominator:ZMod (2^P))*
      ((acquireOriginal a t x y).denominator:ZMod (2^P))⁻¹=1 :=
  ZMod.mul_inv_of_unit _ (original_inverse_unit a P t x y)

end RiemannGaussian.SemiprimeD1WireKernelOriginal
