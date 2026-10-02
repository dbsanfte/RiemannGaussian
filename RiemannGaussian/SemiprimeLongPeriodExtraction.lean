/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import Mathlib.Algebra.QuadraticAlgebra.Basic
import Mathlib.Algebra.Polynomial.Div
import Mathlib.Algebra.BigOperators.GroupWithZero.Finset
import Mathlib.RingTheory.Polynomial.Dickson
import Mathlib.Tactic

/-!
# Exact signals used by the long-period side experiment

Reciprocal trace detects equal or inverse norm-one elements. All-degree
Dickson fibres lift to root-of-unity relations. Complex corrections either
shift the inverse channel or erase the global separating signal. Polynomial
finite differences and repeated powers generate nonlinear collision points.
Monic remainders preserve evaluation over composite rings. These lemmas
certify the algebraic signals, not generic factoring coverage or the full
Python implementation. Its algebra is checked in the ordinary library; numerical probes remain optional.
-/

namespace RiemannGaussian.SemiprimeLongPeriodExtraction

/-- Trace folding is valid even when the quadratic algebra is split. -/
theorem norm_one_trace_collision {F : Type*} [Field F] {D : F}
    (x y : QuadraticAlgebra F D 0) (hD : D ≠ 0)
    (hx : QuadraticAlgebra.norm x = 1) (hy : QuadraticAlgebra.norm y = 1) :
    x.re = y.re ↔ x = y ∨ x = star y := by
  constructor
  · intro hr
    have hs : (x.im - y.im) * (x.im + y.im) = 0 := by
      have hh : D * ((x.im - y.im) * (x.im + y.im)) = 0 := by
        simp only [QuadraticAlgebra.norm_def, zero_mul, add_zero] at hx hy
        rw [hr] at hx
        linear_combination hy - hx
      exact (mul_eq_zero.mp hh).resolve_left hD
    rcases mul_eq_zero.mp hs with h | h
    · left
      apply QuadraticAlgebra.ext hr
      exact sub_eq_zero.mp h
    · right
      apply QuadraticAlgebra.ext
      · simpa using hr
      · simpa using (eq_neg_iff_add_eq_zero.mpr h)
  · rintro (rfl | rfl) <;> simp

/-- A phase changes the inverse collision channel before projection.
It does not assume either hidden local order is known. -/
theorem corrected_norm_one_trace_collision {F : Type*} [Field F] {D : F}
    (k x y : QuadraticAlgebra F D 0) (hD : D ≠ 0)
    (hk : QuadraticAlgebra.norm k = 1)
    (hx : QuadraticAlgebra.norm x = 1) (hy : QuadraticAlgebra.norm y = 1) :
    (k*x).re = (k*y).re ↔ x = y ∨ k^2*x*y = 1 := by
  have hkn : QuadraticAlgebra.norm (k*x) = 1 := by rw [map_mul, hk, hx, mul_one]
  have hyn : QuadraticAlgebra.norm (k*y) = 1 := by rw [map_mul, hk, hy, mul_one]
  have hku : star k*k = 1 := by
    rw [mul_comm, ← QuadraticAlgebra.algebraMap_norm_eq_mul_star, hk, map_one]
  have hyu : (k*y)*star (k*y) = 1 := by
    rw [← QuadraticAlgebra.algebraMap_norm_eq_mul_star, hyn, map_one]
  have hprod : (k*x)*(k*y) = k^2*x*y := by ring
  rw [norm_one_trace_collision (k*x) (k*y) hD hkn hyn]
  constructor
  · rintro (he | he)
    · left
      have hh := congrArg (fun v => star k*v) he
      simpa only [← mul_assoc, hku, one_mul] using hh
    · right
      have hh : (k*x)*(k*y) = 1 := by
        rw [he, mul_comm, hyu]
      rwa [hprod] at hh
  · rintro (he | he)
    · left
      rw [he]
    · right
      rw [← hprod] at he
      have hh := congrArg (fun v => v*star (k*y)) he
      simpa only [mul_assoc, hyu, mul_one, one_mul] using hh

/-- The RH cross-phase null identity transfers algebraically to the
modular Gaussian ring, without an ordered norm or a square root. -/
theorem coherent_phase_cross_zero {R : Type*} [CommRing R] {D : R}
    (phase : QuadraticAlgebra R D 0) (scalar : R) :
    phase.im*(phase*QuadraticAlgebra.C scalar).re -
      phase.re*(phase*QuadraticAlgebra.C scalar).im = 0 := by
  simp only [QuadraticAlgebra.re_mul, QuadraticAlgebra.im_mul,
    QuadraticAlgebra.re_C, QuadraticAlgebra.im_C, mul_zero, add_zero]
  ring

/-- The parallel channel recovers the amplitude exactly. Perpendicular
null cancellation by itself erases that entire factor-bearing amplitude. -/
theorem coherent_phase_parallel_recovers {R : Type*} [CommRing R]
    (phase : QuadraticAlgebra R (-1) 0) (scalar : R)
    (hn : QuadraticAlgebra.norm phase = 1) :
    phase.re*(phase*QuadraticAlgebra.C scalar).re +
      phase.im*(phase*QuadraticAlgebra.C scalar).im = scalar := by
  simp only [QuadraticAlgebra.norm_def, neg_mul, one_mul, sub_neg_eq_add,
    zero_mul, add_zero] at hn
  simp only [QuadraticAlgebra.re_mul, QuadraticAlgebra.im_mul,
    QuadraticAlgebra.re_C, QuadraticAlgebra.im_C, mul_zero, add_zero]
  linear_combination scalar*hn

/-- On the exactly coherent detector, the perpendicular signal always
returns the full modulus as its GCD, not a separating factor. -/
theorem coherent_null_gcd_is_full (n : ℕ)
    (phase : QuadraticAlgebra (ZMod n) (-1) 0) (scalar : ZMod n) :
    (phase.im*(phase*QuadraticAlgebra.C scalar).re -
      phase.re*(phase*QuadraticAlgebra.C scalar).im).val.gcd n = n := by
  rw [coherent_phase_cross_zero]
  simp

/-- Publicly forcing the inverse channel globally aligns both hidden
prime legs at once. This requires no field assumption. -/
theorem global_inverse_alignment_trace {R : Type*} [CommRing R] {D : R}
    (k x y : QuadraticAlgebra R D 0)
    (hk : QuadraticAlgebra.norm k = 1) (hy : QuadraticAlgebra.norm y = 1)
    (hxy : k^2*x*y = 1) : (k*x).re = (k*y).re := by
  have hyu : (k*y)*star (k*y) = 1 := by
    rw [← QuadraticAlgebra.algebraMap_norm_eq_mul_star, map_mul, hk, hy,
      mul_one, map_one]
  have hp : (k*x)*(k*y) = 1 := by
    calc
      (k*x)*(k*y) = k^2*x*y := by ring
      _ = 1 := hxy
  have hh := congrArg (fun v => v*star (k*y)) hp
  have he : k*x = star (k*y) := by
    simpa only [mul_assoc, hyu, mul_one, one_mul] using hh
  simpa using congrArg QuadraticAlgebra.re he

/-- A globally perfect phase match returns N, not a separating factor. -/
theorem global_inverse_alignment_gcd_is_full (n : ℕ) {D : ZMod n}
    (k x y : QuadraticAlgebra (ZMod n) D 0)
    (hk : QuadraticAlgebra.norm k = 1) (hy : QuadraticAlgebra.norm y = 1)
    (hxy : k^2*x*y = 1) : ((k*x).re - (k*y).re).val.gcd n = n := by
  rw [global_inverse_alignment_trace k x y hk hy hxy, sub_self]
  simp

/-- A reciprocal trace has two exact collision channels, without norms. -/
theorem reciprocal_trace_difference {F : Type*} [Field F] {x y : F}
    (hx : x ≠ 0) (hy : y ≠ 0) :
    x + x⁻¹ - (y + y⁻¹) = (x-y)*(x*y-1)/(x*y) := by
  field_simp
  ring

theorem reciprocal_trace_eq_iff {F : Type*} [Field F] {x y : F}
    (hx : x ≠ 0) (hy : y ≠ 0) :
    x + x⁻¹ = y + y⁻¹ ↔ x = y ∨ x*y = 1 := by
  rw [← sub_eq_zero, reciprocal_trace_difference hx hy]
  rw [div_eq_zero_iff]
  simp [mul_ne_zero hx hy, mul_eq_zero, sub_eq_zero]

/-- The degree-six control is one instance of an all-degree principle:
lift a trace to a unit, power that unit, and project back. Fibres are
root-of-unity relations in either the ratio or the product channel. -/
theorem dickson_collision_lift {F : Type*} [Field F]
    {x y : F} (hx : x ≠ 0) (hy : y ≠ 0) (degree : ℕ) :
    (Polynomial.dickson 1 (1 : F) degree).eval (x+x⁻¹) =
      (Polynomial.dickson 1 (1 : F) degree).eval (y+y⁻¹) ↔
    (x/y)^degree = 1 ∨ (x*y)^degree = 1 := by
  rw [Polynomial.dickson_one_one_eval_add_inv x x⁻¹ (mul_inv_cancel₀ hx),
    Polynomial.dickson_one_one_eval_add_inv y y⁻¹ (mul_inv_cancel₀ hy),
    inv_pow, inv_pow,
    reciprocal_trace_eq_iff (pow_ne_zero degree hx) (pow_ne_zero degree hy)]
  rw [mul_pow, div_pow, div_eq_one_iff_eq (pow_ne_zero degree hy)]

/-- Iterating a fold multiplies its degree; it is not an independent
cost-free layer. This is Mathlib's Dickson composition identity at a point. -/
theorem dickson_nested_fold {R : Type*} [CommRing R]
    (m n : ℕ) (x : R) :
    (Polynomial.dickson 1 (1 : R) m).eval
      ((Polynomial.dickson 1 (1 : R) n).eval x) =
      (Polynomial.dickson 1 (1 : R) (m*n)).eval x := by
  rw [Polynomial.dickson_one_one_mul, Polynomial.eval_comp]

/-- A fixed degree-six fold has at most six preimages of each output,
independently of field size. One long-order hit is not a uniform 95-fold
coverage improvement. -/
theorem dickson6_fiber_card_le {F : Type*} [Field F]
    (S : Finset F) (value : F)
    (hS : ∀ x ∈ S, x^6-6*x^4+9*x^2-2 = value) : S.card ≤ 6 := by
  let p : Polynomial F := Polynomial.X^6 - 6*Polynomial.X^4 +
    9*Polynomial.X^2 - 2 - Polynomial.C value
  have hp : p ≠ 0 := by
    intro he
    have hh := congrArg (fun q : Polynomial F => q.coeff 6) he
    norm_num [p, Polynomial.coeff_X_pow] at hh
  have hsub : S.val ⊆ p.roots := by
    intro x hx
    apply (Polynomial.mem_roots hp).mpr
    simpa [p] using sub_eq_zero.mpr (hS x hx)
  have hdegree : p.natDegree ≤ 6 := by
    dsimp [p]
    compute_degree
  exact (Polynomial.card_le_degree_of_subset_roots hsub).trans hdegree

/-- The public sixth-root budget bounds the smaller prime's two possible
quadratic group cardinalities. -/
theorem smaller_factor_group_budget {p q B : ℕ}
    (hpq : p ≤ q) (hsize : p*q ≤ B^6) : p+1 ≤ B^3+1 := by
  have hh : p*p ≤ B^6 := (Nat.mul_le_mul_left p hpq).trans hsize
  have he : B^6 = B^3*B^3 := by ring
  rw [he] at hh
  set x := B^3
  change p*p ≤ x*x at hh
  change p+1 ≤ x+1
  nlinarith

/-- With B chosen at the sixth-root scale, the smaller-prime group order
is at most B^3+1. Removing every prime through B leaves at most two rough
prime factors, counted with multiplicity. This is the arithmetic part;
the theorem does not assume the unknown order can be read out. -/
theorem three_rough_factors_impossible {B a b c : ℕ} (hB : 0 < B)
    (ha : B+1 ≤ a) (hb : B+1 ≤ b) (hc : B+1 ≤ c)
    (hsize : a*b*c ≤ B^3+1) : False := by
  have hmin : (B+1)^3 ≤ a*b*c := by
    calc
      (B+1)^3 = (B+1)*(B+1)*(B+1) := by ring
      _ ≤ a*b*c := Nat.mul_le_mul (Nat.mul_le_mul ha hb) hc
  nlinarith

/-- In the two-rough-factor case, each individual factor lies below B^2,
even though their product can exceed the existing closure cover. -/
theorem two_rough_factors_lt_square {B a b : ℕ} (hB : 2 ≤ B)
    (ha : B+1 ≤ a) (hb : B+1 ≤ b) (hsize : a*b ≤ B^3+1) :
    a < B^2 ∧ b < B^2 := by
  have hsq : 1 < B^2 := by nlinarith
  have hbound (x y : ℕ) (hy : B+1 ≤ y) (hxy : x*y ≤ B^3+1) : x < B^2 := by
    by_contra he
    have hx : B^2 ≤ x := Nat.le_of_not_gt he
    have hh : B^3+B^2 ≤ x*y := by
      calc
        B^3+B^2 = B^2*(B+1) := by ring
        _ ≤ x*y := Nat.mul_le_mul hx hy
    omega
  exact ⟨hbound a b hb hsize, hbound b a ha (by simpa [Nat.mul_comm] using hsize)⟩

/-- The exact count ceiling includes repeated prime factors. Only a single
long prime, two rough primes, or a rough prime square can survive the
sixth-root smooth projection on the smaller-prime group. -/
theorem rough_order_prime_count_le_two {B d : ℕ} (hB : 0 < B)
    (hd : 0 < d) (hsize : d ≤ B^3+1)
    (hrough : ∀ p ∈ d.primeFactorsList, B < p) :
    d.primeFactorsList.length ≤ 2 := by
  by_contra hn
  cases he : d.primeFactorsList with
  | nil => simp [he] at hn
  | cons a tail =>
    cases tail with
    | nil => simp [he] at hn
    | cons b tail =>
      cases tail with
      | nil => simp [he] at hn
      | cons c tail =>
        have ha : B+1 ≤ a := hrough a (by simp [he])
        have hb : B+1 ≤ b := hrough b (by simp [he])
        have hc : B+1 ≤ c := hrough c (by simp [he])
        have hp : a*b*c*tail.prod = d := by
          simpa only [he, List.prod_cons, mul_assoc] using Nat.prod_primeFactorsList hd.ne'
        have htail : 0 < tail.prod := by
          by_contra ht
          have hz : tail.prod = 0 := Nat.eq_zero_of_not_pos ht
          rw [hz, mul_zero] at hp
          omega
        have hle : a*b*c ≤ d := by
          calc
            a*b*c = a*b*c*1 := by simp
            _ ≤ a*b*c*tail.prod := Nat.mul_le_mul_left _ htail
            _ = d := hp
        exact three_rough_factors_impossible hB ha hb hc (hle.trans hsize)

/-- Rotating before a reciprocal trace changes only the inverse channel.
This identity is exact; there is no estimate of a complex phase. -/
theorem corrected_reciprocal_trace_difference {F : Type*} [Field F]
    {k x y : F} (hk : k ≠ 0) (hx : x ≠ 0) (hy : y ≠ 0) :
    k*x + (k*x)⁻¹ - (k*y + (k*y)⁻¹) =
      k*(x-y)*(k^2*x*y-1)/(k^2*x*y) := by
  field_simp
  ring

/-- A phase power adds an explicitly known shift to the inverse channel. -/
theorem phase_power_inverse_channel {G : Type*} [Group G]
    (a : G) (c e f : ℤ) : (a^c)^2 * a^e * a^f = a^(e+f+2*c) := by
  rw [pow_two, ← zpow_add, ← zpow_add, ← zpow_add]
  congr 1
  ring

/-- Exponentially large integer exponents need not be materialized:
each new point is obtained by one small/public group powering. -/
theorem exponential_orbit_step {M : Type*} [Monoid M]
    (a : M) (b k : ℕ) : (a^(b^k))^b = a^(b^(k+1)) := by
  rw [← pow_mul, pow_succ]

/-- After removing the 2-part, the generated odd-order subgroup cannot
reach -1. Thus an imaginary quarter-turn cannot add an inverse hit. -/
theorem odd_order_cannot_reach_neg_one {F : Type*} [Ring F]
    {a : F} {m e : ℕ} (ha : a^m = 1) (hm : Odd m)
    (hneg : (-1 : F) ≠ 1) : a^e ≠ -1 := by
  intro he
  have hh : (-1 : F)^m = 1 := by
    calc
      (-1 : F)^m = (a^e)^m := by rw [he]
      _ = (a^m)^e := by rw [← pow_mul, ← pow_mul, Nat.mul_comm e m]
      _ = 1 := by rw [ha, one_pow]
  exact hneg (by simpa only [hm.neg_one_pow] using hh)

/-- A pure imaginary phase loses the inverse channel on the projected
odd-order subgroup. This covers modular rings as well as fields. -/
theorem imaginary_rotation_odd_order_inverse_impossible
    {F : Type*} [CommRing F] (a i : F) (c e f m : ℕ)
    (ha : a^m = 1) (hm : Odd m) (hneg : (-1 : F) ≠ 1)
    (hi : i^2 = -1) : (i*a^c)^2 * a^e * a^f ≠ 1 := by
  have hh : (i*a^c)^2 * a^e * a^f = -(a^(2*c+e+f)) := by
    rw [mul_pow, hi, neg_one_mul, ← pow_mul, neg_mul, neg_mul,
      ← pow_add, ← pow_add]
    rw [Nat.mul_comm c 2]
  intro he
  rw [hh] at he
  exact odd_order_cannot_reach_neg_one ha hm hneg (neg_eq_iff_eq_neg.mp he)

/-- The in-place ascending update in the probe is exactly the additive
finite-difference update, expressed multiplicatively. -/
theorem finite_difference_power_step {G : Type*} [Group G]
    (a : G) (v next : ℤ) : a^v * a^(next-v) = a^next := by
  rw [← zpow_add]
  congr 1
  ring

theorem finite_difference_power_table_step {G : Type*} [Group G]
    (a : G) (v : ℕ → ℤ) (i : ℕ) :
    a^(v i) * a^(v (i+1)-v i) = a^(v (i+1)) :=
  finite_difference_power_step a _ _

/-- A cheap public exponent encodes the factor gap on the first local leg. -/
theorem public_power_eq_gap_left {G : Type*} [Group G] (a : G)
    {p q : ℕ} (hp : 0 < p) (hqp : p ≤ q) (ha : a^(p-1) = 1) :
    a^(p*q-1) = a^(q-p) := by
  have h1 : p-1+1=p := by omega
  have h2 : q-p+p=q := Nat.sub_add_cancel hqp
  have hn : 0 < p*q := Nat.mul_pos hp (lt_of_lt_of_le hp hqp)
  have h3 : p*q-1+1=p*q := by omega
  have he : p*q-1=(p-1)*(q+1)+(q-p) := by nlinarith
  rw [he, pow_add, pow_mul, ha, one_pow, one_mul]

/-- The same exponent encodes the inverse gap on the other local leg. -/
theorem public_power_eq_inverse_gap_right {G : Type*} [Group G] (a : G)
    {p q : ℕ} (hp : 0 < p) (hqp : p ≤ q) (ha : a^(q-1) = 1) :
    a^(p*q-1) = (a^(q-p))⁻¹ := by
  have h2 : q-p+p=q := Nat.sub_add_cancel hqp
  have hn : 0 < p*q := Nat.mul_pos hp (lt_of_lt_of_le hp hqp)
  have h3 : p*q-1+1=p*q := by omega
  have h4 : q-1+1=q := by omega
  have he : p*q-1+(q-p)=(q-1)*(p+1) := by nlinarith
  apply eq_inv_of_mul_eq_one_left
  rw [← pow_add, he, pow_mul, ha, one_pow]

/-- Newton's reciprocal iteration doubles the error order algebraically;
there is no division by an unknown nonunit coefficient. -/
theorem reciprocal_newton_error {R : Type*} [CommRing R] (f g : R) :
    1 - f*(g*(2-f*g)) = (1-f*g)^2 := by ring

/-- Remainder evaluation is exact over a composite base ring too. -/
theorem monic_remainder_eval_at_root {R : Type*} [CommRing R]
    (f g : Polynomial R) (x : R) (hx : g.eval x = 0) :
    (f %ₘ g).eval x = f.eval x := by
  rw [Polynomial.modByMonic_eq_sub_mul_div]
  simp only [Polynomial.eval_sub, Polynomial.eval_mul, hx, zero_mul, sub_zero]

theorem collision_product_eval {R I : Type*} [CommRing R]
    (S : Finset I) (roots : I → R) (x : R) :
    (∏ i ∈ S, (Polynomial.X - Polynomial.C (roots i))).eval x =
      ∏ i ∈ S, (x-roots i) := by
  rw [Polynomial.eval_prod]
  simp only [Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C]

theorem collision_product_zero_iff {F I : Type*} [Field F]
    (S : Finset I) (roots : I → F) (x : F) :
    (∏ i ∈ S, (Polynomial.X - Polynomial.C (roots i))).eval x = 0 ↔
      ∃ i ∈ S, x = roots i := by
  rw [collision_product_eval, Finset.prod_eq_zero_iff]
  simp only [sub_eq_zero]

/-- The long-period hit is a quadratic/cyclotomic alias rather than a
linear period closure. The identity holds over every commutative ring. -/
theorem dickson6_difference {R : Type*} [CommRing R] (x y : R) :
    (x^6-6*x^4+9*x^2-2) - (y^6-6*y^4+9*y^2-2) =
      (x-y)*(x+y)*(x^2-x*y+y^2-3)*(x^2+x*y+y^2-3) := by ring

/-- The explicit selected quadratic factor contains the long private
period. No such private period is supplied to the extraction algorithm. -/
theorem dickson6_quadratic_alias_control :
    (477*1431 : ℕ)^2 + 1427^2 - ((477*1431)*1427+3) =
      195522707*2378 ∧
    (477*1431+1427 : ℕ) < 195522707 := by norm_num

/-- The degree-six map genuinely escapes the old linear cover in the
reproducible 64-bit control. This only certifies the exponent congruence. -/
theorem dickson6_long_alias_control :
    (195522707 : ℕ) > 1431^2 ∧
    (477*1431 : ℕ)^6 - 6*(477*1431)^4 + 9*(477*1431)^2 - 2 =
      101145851947691613918017073899850562 ∧
    (1427 : ℕ)^6 - 6*1427^4 + 9*1427^2 - 2 = 8443889844527188802 ∧
    (101145851947691613918017073899850562 : ℕ) % 195522707 =
      8443889844527188802 % 195522707 := by
  norm_num

/-- GCD recovery from the public trace witness in the optional replay.
The witness-generation algorithm is tested separately in Python. -/
theorem public_trace_gcd_control :
    (6820094445240089472 - 237621801882584593 : ℕ).gcd 8562316804979989201 =
      2346272483 ∧
    (2346272483 : ℕ)*3649327547 = 8562316804979989201 := by norm_num

end RiemannGaussian.SemiprimeLongPeriodExtraction
